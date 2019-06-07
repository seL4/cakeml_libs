(*
 * Copyright 2019, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

open preamble basis utilsTheory targetInfoTheory;

val _ = new_theory "seL4";

require utils targetInfo;

val _ = ml_prog_update (open_module "SeL4");

(* FIXME: number of message registers for arch *)
(* FIXME: return updated message register values *)
val _ = (append_prog o process_topdecs) `
    fun seL4_CallWithMRs dest msg_info mr0 mr1 mr2 mr3 = let
        val word_size = TargetInfo.word_size_bytes ();
        val ffi_buffer = Word8Array.array (6 * word_size) (Word8.fromInt 0)
        val u = Word8Array.copy (Utils.word64_to_bytes dest word_size) 0 word_size ffi_buffer 0
        val u = Word8Array.copy (Utils.word64_to_bytes msg_info word_size) 0 word_size ffi_buffer word_size
        val u = Word8Array.copy (Utils.word64_to_bytes mr0 word_size) 0 word_size ffi_buffer (2 * word_size)
        val u = Word8Array.copy (Utils.word64_to_bytes mr1 word_size) 0 word_size ffi_buffer (3 * word_size)
        val u = Word8Array.copy (Utils.word64_to_bytes mr2 word_size) 0 word_size ffi_buffer (4 * word_size)
        val u = Word8Array.copy (Utils.word64_to_bytes mr3 word_size) 0 word_size ffi_buffer (5 * word_size)
        val u = #(seL4_CallWithMRs) "" ffi_buffer
        val error_code = Utils.bytes_to_int ffi_buffer 0 word_size
        in
            error_code
        end
`;

(* FIXME: need that zero argument? *)
val _ = (append_prog o process_topdecs) `
    fun seL4_MessageInfo_new method_id num_cap_words num_input_words = let
        val word_size = TargetInfo.word_size_bytes ();
        val ffi_buffer = Word8Array.array (3 * word_size) (Word8.fromInt 0)
        val u = Word8Array.copy (Utils.int_to_bytes method_id word_size) 0 word_size ffi_buffer 0
        val u = Word8Array.copy (Utils.int_to_bytes num_cap_words word_size) 0 word_size ffi_buffer word_size
        val u = Word8Array.copy (Utils.int_to_bytes num_input_words word_size) 0 word_size ffi_buffer (2 * word_size)
        val u = #(seL4_MessageInfo_new) "" ffi_buffer
        val msg_info = Word8Array.array word_size (Word8.fromInt 0)
        val u = Word8Array.copy ffi_buffer 0 word_size msg_info 0
        in
            Utils.bytes_to_word64 msg_info 0 word_size
        end
`;

val _ = (append_prog o process_topdecs) `
    fun seL4_SetMR idx value = let
        val word_size = TargetInfo.word_size_bytes ();
        val ffi_buffer = Word8Array.array (2 * word_size) (Word8.fromInt 0)
        val u = Word8Array.copy (Utils.int_to_bytes idx word_size) 0 word_size ffi_buffer 0
        val u = Word8Array.copy (Utils.word64_to_bytes value word_size) 0 word_size ffi_buffer word_size
        val u = #(seL4_SetMR) "" ffi_buffer
        in () end
`;

val _ = (append_prog o process_topdecs) `
    fun seL4_SetCap idx value = let
        val word_size = TargetInfo.word_size_bytes ();
        val ffi_buffer = Word8Array.array (2 * word_size) (Word8.fromInt 0)
        val u = Word8Array.copy (Utils.int_to_bytes idx word_size) 0 word_size ffi_buffer 0
        val u = Word8Array.copy (Utils.word64_to_bytes value word_size) 0 word_size ffi_buffer word_size
        val u = #(seL4_SetCap) "" ffi_buffer
        in () end
`;

val seL4_ReplyRecv_def = (append_prog o process_topdecs) `
    fun seL4_ReplyRecv ep send_length ipcbuf = let
        val word_size = TargetInfo.word_size_bytes ();
        val u = Word8Array.copy (Utils.int_to_bytes ep word_size) 0 word_size ipcbuf 1;
        val u = Word8Array.copy (Utils.int_to_bytes send_length word_size) 0 word_size ipcbuf (1 + word_size);
        val u = #(seL4_ReplyRecv) "" ipcbuf;
        val len = Utils.bytes_to_int ipcbuf 1 word_size;
        val badge = Utils.bytes_to_int ipcbuf (1 + word_size) word_size;
        in (len, badge) end;
`;

val seL4_Recv_def = (append_prog o process_topdecs) `
    fun seL4_Recv ep ipcbuf = let
        val word_size = TargetInfo.word_size_bytes ();
        val u = Word8Array.copy (Utils.int_to_bytes ep word_size) 0 word_size ipcbuf 1;
        val u = #(seL4_Recv) "" ipcbuf;
        val len = Utils.bytes_to_int ipcbuf 1 word_size;
        val badge = Utils.bytes_to_int ipcbuf (1 + word_size) word_size;
        in (len, badge) end;
`;

val seL4_Send_def = (append_prog o process_topdecs) `
    fun seL4_Send ep send_length ipcbuf = let
        val word_size = TargetInfo.word_size_bytes ();
        val u = Word8Array.copy (Utils.int_to_bytes ep word_size) 0 word_size ipcbuf 1;
        val u = Word8Array.copy (Utils.int_to_bytes send_length 8) 0 word_size ipcbuf (1 + word_size);
        val u = #(seL4_Send) "" ipcbuf;
        in () end;
`;

val seL4_Wait_def = (append_prog o process_topdecs) `
    fun seL4_Wait src = let
        val word_size = TargetInfo.word_size_bytes ();
        val buf = Word8Array.array (1 + word_size)  (Word8.fromInt 0);
        val u = Word8Array.copy (Utils.int_to_bytes src word_size) 0 word_size buf 1;
        val u = #(seL4_Wait) "" buf;
        val badge = Utils.bytes_to_int buf 1 word_size;
        in badge end;
`;

val _ = ml_prog_update (close_module NONE);
val _ = export_theory ();
