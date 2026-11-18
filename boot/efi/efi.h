// x86-64 UEFI 2.x interfaces used by this application. Compiled Lean keeps
// the System V ABI. All crossings to or from firmware use its Microsoft ABI.
#pragma once
#include <stddef.h>
#include <stdint.h>

#define EFIAPI __attribute__((ms_abi))
typedef uint64_t Status;
typedef void *Handle;
typedef struct { uint32_t a; uint16_t b, c; uint8_t d[8]; } Guid;
#define EFI_ERROR_CODE(n) ((1ULL << 63) | (n))
#define NOT_READY EFI_ERROR_CODE(6)

typedef struct {
    void *reset;
    Status (EFIAPI *write)(void *, const uint16_t *);
} Console;

typedef struct {
    uint8_t header[24];
    void *raise_tpl, *restore_tpl;
    Status (EFIAPI *allocate_pages)(uint32_t, uint32_t, size_t, uint64_t *);
    void *free_pages, *get_memory_map, *allocate_pool;
    Status (EFIAPI *free_pool)(void *);
    void *create_event, *set_timer, *wait_for_event, *signal_event, *close_event, *check_event;
    void *install_protocol, *reinstall_protocol, *uninstall_protocol, *handle_protocol, *reserved;
    void *register_notify, *locate_handle, *locate_device_path, *install_table;
    void *load_image, *start_image, *exit, *unload_image, *exit_boot_services, *monotonic_count;
    Status (EFIAPI *stall)(size_t);
    Status (EFIAPI *watchdog)(size_t, uint64_t, size_t, uint16_t *);
    Status (EFIAPI *connect)(Handle, Handle *, void *, uint8_t);
    void *disconnect;
    Status (EFIAPI *open_protocol)(Handle, const Guid *, void **, Handle, Handle, uint32_t);
    void *close_protocol, *open_protocol_information, *protocols_per_handle;
    Status (EFIAPI *handles)(uint32_t, const Guid *, void *, size_t *, Handle **);
} BootServices;

typedef struct {
    uint8_t header[24];
    void *vendor;
    uint32_t revision;
    void *in_handle, *in, *out_handle;
    Console *out;
    void *err_handle, *err, *runtime;
    BootServices *boot;
} SystemTable;

typedef struct {
    uint32_t state, address_size, header_size, max_packet, nvram_size, nvram_access;
    uint32_t filters_supported, filters_active, max_multicast, multicast_count;
    uint8_t multicast[16][32], address[32], broadcast[32], permanent[32], if_type;
} NetworkMode;

typedef struct Network Network;
struct Network {
    uint64_t revision;
    Status (EFIAPI *start)(Network *);
    void *stop;
    Status (EFIAPI *initialize)(Network *, size_t, size_t);
    void *reset, *shutdown;
    Status (EFIAPI *filters)(Network *, uint32_t, uint32_t, uint8_t, size_t, const void *);
    void *station_address, *statistics, *mcast_ip_to_mac, *nvdata;
    Status (EFIAPI *status)(Network *, uint32_t *, void **);
    Status (EFIAPI *transmit)(Network *, size_t, size_t, void *, void *, void *, uint16_t *);
    Status (EFIAPI *receive)(Network *, size_t *, size_t *, void *, void *, void *, uint16_t *);
    void *wait_for_packet;
    NetworkMode *mode;
};

_Static_assert(offsetof(SystemTable, boot) == 96, "x64 system table");
_Static_assert(offsetof(BootServices, handles) == 312, "x64 boot services");
_Static_assert(offsetof(Network, mode) == 120, "x64 simple network protocol");
_Static_assert(offsetof(NetworkMode, address) == 552, "current MAC address");
