// The firmware owns the PCI device, DMA mappings and exception handlers.
// SNP only exchanges complete Ethernet frames with the Lean application.
#include "efi.h"
#include "../boot.h"
#include "../../rt/rt.h"

static SystemTable *system_table;
static Handle image_handle;
static Network *nic;
void *boot_heap_start;
// How much the runtime's heap is. A package whose program needs more says so when it compiles this file.
#ifndef BOOT_HEAP_BYTES
#define BOOT_HEAP_BYTES (256 * 1024 * 1024)
#endif
size_t boot_heap_size = BOOT_HEAP_BYTES;
static uint64_t epoch, ticks_per_ms;

void boot_serial_write(char const *bytes, size_t length) {
    uint16_t chars[128];
    size_t n = 0;
    while (length--) {
        unsigned char c = (unsigned char)*bytes++;
        if (c == '\n') chars[n++] = '\r';
        chars[n++] = c;
        if (n >= 125 || length == 0) {
            chars[n] = 0;
            system_table->out->write(system_table->out, chars);
            n = 0;
        }
    }
}

_Noreturn void boot_halt(int code) {
    rt_print("silo: EFI service stopped (");
    rt_print_size((size_t)code);
    rt_print(")\n");
    for (;;) system_table->boot->stall(100000);
}

static uint64_t tsc(void) {
    uint32_t lo, hi;
    __asm__ volatile ("lfence; rdtsc" : "=a"(lo), "=d"(hi) :: "memory");
    return ((uint64_t)hi << 32) | lo;
}

#if REQUIRE_TDX
static bool is_td(void) {
    uint32_t version = 0x21, b, c = 0, d;
    __asm__ volatile ("cpuid" : "+a"(version), "=b"(b), "+c"(c), "=d"(d));
    uint32_t signature[3] = {b, d, c};
    return memcmp(signature, "IntelTDX    ", 12) == 0;
}
#endif

static uint64_t millis(void) {
    return (tsc() - epoch) / ticks_per_ms;
}

lean_obj_res silo_efi_millis(void) {
    return lean_io_result_mk_ok(lean_box_uint64(millis()));
}

lean_obj_res silo_efi_idle(void) {
    system_table->boot->stall(1000);
    return lean_io_result_mk_ok(lean_box(0));
}

lean_object *lean_mk_io_user_error(lean_object *);

static lean_obj_res error(const char *msg) {
    return lean_io_result_mk_error(lean_mk_io_user_error(lean_mk_string(msg)));
}

static lean_obj_res bytes(const uint8_t *data, size_t count) {
    lean_object *a = lean_alloc_sarray(1, count, count);
    if (count) memcpy(lean_sarray_cptr(a), data, count);
    return lean_io_result_mk_ok(a);
}

static const Guid snp_guid = {0xa19832b9, 0xac25, 0x11d3,
                              {0x9a,0x2d,0,0x90,0x27,0x3f,0xc1,0x4d}};
static const Guid pci_io_guid = {0x4cf5b200, 0x68b8, 0x4ca5,
                                 {0x9e,0xec,0xb2,0x3e,0x3f,0x50,0x02,0x9a}};

static const Guid path_guid = {0x09576e91, 0x6d3f, 0x11d2,
                               {0x8e,0x39,0,0xa0,0xc9,0x69,0x72,0x3b}};

// OVMF installs the same SNP pointer on its IPv4 and IPv6 PXE child
// handles. Exclusive ownership has to be requested on the original MAC
// controller. Device paths here are firmware metadata, separate from frames.
static bool mac_controller(Handle handle) {
    const uint8_t *node = NULL;
    if (system_table->boot->open_protocol(handle, &path_guid, (void **)&node,
                                          image_handle, NULL, 2) != 0 || !node) return false;
    size_t remaining = 4096;
    bool last_was_mac = false;
    while (remaining >= 4) {
        size_t size = node[2] | ((size_t)node[3] << 8);
        if (size < 4 || size > remaining) return false;
        if (node[0] == 0x7f)
            return node[1] == 0xff && size == 4 && last_was_mac;
        last_was_mac = node[0] == 3 && node[1] == 11;
        remaining -= size;
        node += size;
    }
    return false;
}

// Firmware may have connected only the controllers needed to boot the disk.
static void connect_devices(void) {
    Handle *handles;
    size_t count;
    BootServices *bs = system_table->boot;
    if (bs->handles(2, &pci_io_guid, NULL, &count, &handles) != 0) return;
    for (size_t i = 0; i < count; ++i) bs->connect(handles[i], NULL, NULL, 1);
    bs->free_pool(handles);
}

lean_obj_res silo_efi_mac(void) {
    if (nic) return bytes(nic->mode->address, 6);
    Handle *handles;
    size_t count;
    BootServices *bs = system_table->boot;
    connect_devices();
    if (bs->handles(2, &snp_guid, NULL, &count, &handles) != 0)
        return error("UEFI has no Simple Network Protocol interface");
    Network *device = NULL;
    // An exclusive open disconnects the firmware network clients. They must
    // not race the application for packets from this queue.
    Handle controller = NULL;
    for (size_t i = 0; i < count; ++i) {
        if (!mac_controller(handles[i])) continue;
        if (controller) {
            bs->free_pool(handles);
            return error("multiple UEFI Ethernet controllers");
        }
        controller = handles[i];
    }
    bs->free_pool(handles);
    if (!controller) return error("UEFI has no Ethernet MAC controller");
    if (bs->open_protocol(controller, &snp_guid, (void **)&device, image_handle, NULL, 0x20) != 0 || !device)
        return error("UEFI could not grant exclusive access to its Ethernet controller");
    NetworkMode *mode = device->mode;
    if (mode->address_size != 6 || mode->header_size != 14 || mode->if_type != 1 || mode->max_packet < 1500)
        return error("UEFI NIC is not 1500-byte Ethernet");
    if (mode->state == 0 && device->start(device) != 0) return error("SNP Start failed");
    if (mode->state == 1 && device->initialize(device, 0, 0) != 0) return error("SNP Initialize failed");
    if (mode->state != 2) return error("SNP is not initialized");
    // Receive solicited-node multicast for IPv6. VirtioNetDxe exposes
    // promiscuous mode. Some other drivers offer multicast-only promiscuity.
    uint32_t multicast = (mode->filters_supported & 16) ? 16 : 8;
    uint32_t wanted = 1 | 4 | multicast;
    if ((wanted & ~mode->filters_supported) || device->filters(device, wanted, 0, 0, 0, NULL) != 0)
        return error("SNP cannot receive unicast, broadcast and multicast");
    nic = device;
    return bytes(mode->address, 6);
}

lean_obj_res silo_efi_receive(void) {
    uint8_t packet[2048];
    size_t length = sizeof(packet);
    if (!nic) return error("SNP has not been opened");
    Status result = nic->receive(nic, NULL, &length, packet, NULL, NULL, NULL);
    if (result == NOT_READY) return bytes(NULL, 0);
    if (result != 0) return error("SNP Receive failed");
    if (length > sizeof(packet)) return error("SNP returned an invalid length");
    if (length < 14 || length > 1514) return bytes(NULL, 0);
    return bytes(packet, length);
}

lean_obj_res silo_efi_send(b_lean_obj_arg frame) {
    // A driver may still be reading a transmit buffer after Transmit
    // returns. Keep our own copy until it returns that buffer via GetStatus.
    static uint8_t packet[1514];
    static bool outstanding;
    size_t length = lean_sarray_size(frame);
    if (!nic || outstanding || length < 14 || length > sizeof(packet))
        return error("invalid SNP transmit state or frame size");
    memcpy(packet, lean_sarray_cptr(frame), length);
    uint64_t start = millis();
    do {
        Status result = nic->transmit(nic, 0, length, packet, NULL, NULL, NULL);
        if (result == 0) { outstanding = true; break; }
        if (result != NOT_READY) return error("SNP Transmit failed");
        system_table->boot->stall(100);
    } while (millis() - start < 1000);
    if (!outstanding) return error("SNP transmit queue timed out");
    // The buffer usually comes back within microseconds, so it is asked for
    // many times before any waiting is done: a wait is never shorter than
    // 100 microseconds, and one per frame is most of what a frame would cost.
    unsigned asked = 0;
    do {
        void *completed = NULL;
        if (nic->status(nic, NULL, &completed) != 0) return error("SNP GetStatus failed");
        if (completed == packet) {
            outstanding = false;
            return lean_io_result_mk_ok(lean_box(0));
        }
        if (++asked > 256) system_table->boot->stall(100);
    } while (millis() - start < 1000);
    return error("SNP did not release the transmit buffer");
}

lean_obj_res silo_efi_report(b_lean_obj_arg challenge) {
#if REQUIRE_TDX
    // Intel TDG.MR.REPORT subtype 0. UEFI boot services use identity-mapped
    // private memory. Neither buffer is ever mapped for device access.
    static _Alignas(1024) uint8_t report[1024];
    static _Alignas(64) uint8_t report_data[64];
    if (lean_sarray_size(challenge) != sizeof(report_data)) return bytes(NULL, 0);
    memcpy(report_data, lean_sarray_cptr(challenge), sizeof(report_data));
    uint64_t status = 4;
    register uint64_t subtype __asm__("r8") = 0;
    uint8_t *output = report, *input = report_data;
    __asm__ volatile (".byte 0x66,0x0f,0x01,0xcc" // TDCALL
                      : "+a"(status), "+c"(output), "+d"(input), "+r"(subtype)
                      : : "r9", "r10", "r11", "cc", "memory");
    return status == 0 ? bytes(report, sizeof(report)) : bytes(NULL, 0);
#else
    (void)challenge;
    return bytes(NULL, 0);
#endif
}

extern int main(int, char **);
Status EFIAPI efi_main(Handle image, SystemTable *table) {
    system_table = table;
    image_handle = image;
#if REQUIRE_TDX
    if (!is_td()) {
        rt_print("silo: Intel TDX required\n");
        return EFI_ERROR_CODE(3);
    }
    rt_print("silo: Intel TDX EFI guest\n");
#else
    rt_print("silo: development EFI guest\n");
#endif
    if (table->boot->watchdog(0, 0, 0, NULL) != 0) return EFI_ERROR_CODE(7);
    // Allocate private loader data for the runtime. Compiled Init alone
    // exceeds 32 MiB during module initialization.
    uint64_t heap_address = 0;
    if (table->boot->allocate_pages(0, 2, boot_heap_size / 4096, &heap_address) != 0) {
        // A 512 MiB guest can have two free extents split by the EFI image.
        boot_heap_size /= 2;
        rt_print("silo: the runtime heap is half of what was asked for\n");
        if (table->boot->allocate_pages(0, 2, boot_heap_size / 4096, &heap_address) != 0) {
            rt_print("silo: firmware could not allocate the runtime heap\n");
            return EFI_ERROR_CODE(9);
        }
    }
    boot_heap_start = (void *)(uintptr_t)heap_address;
    epoch = tsc();
    if (table->boot->stall(50000) != 0) return EFI_ERROR_CODE(7);
    ticks_per_ms = (tsc() - epoch) / 50;
    if (!ticks_per_ms) return EFI_ERROR_CODE(7);
    char *argv[] = {"silo", NULL};
    boot_halt(main(1, argv));
}
