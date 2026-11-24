/* A hosted process has no EFI network device. Lake links this for the
   executable's normal host build. The EFI image links the firmware adapter. */
#include <lean/lean.h>

lean_object * lean_mk_io_user_error(lean_object * message);

static lean_obj_res unavailable(void) {
    return lean_io_result_mk_error(lean_mk_io_user_error(
        lean_mk_string("this target needs EFI boot services")));
}

lean_obj_res silo_efi_mac(void) { return unavailable(); }
lean_obj_res silo_efi_receive(void) { return unavailable(); }
lean_obj_res silo_efi_send(b_lean_obj_arg bytes) { (void)bytes; return unavailable(); }
lean_obj_res silo_efi_millis(void) { return unavailable(); }
lean_obj_res silo_efi_idle(void) { return unavailable(); }
lean_obj_res silo_efi_report(b_lean_obj_arg bytes) { (void)bytes; return unavailable(); }
uint64_t silo_efi_quote_ask(uint64_t address, uint64_t size) { (void)address; (void)size; return ~(uint64_t)0; }
