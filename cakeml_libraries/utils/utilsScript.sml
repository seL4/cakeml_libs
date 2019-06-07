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
open preamble basis targetInfoTheory;

val _ = new_theory "utils";

require basisProg targetInfo;

val _ = ml_prog_update (open_module "Utils");

val fail_def = (append_prog o process_topdecs) `
    fun fail msg = let
        val u = TextIO.print (msg ^ "\n");
        val u = #(fail) "" (Word8Array.array 0 (Word8.fromInt 0));
        in () end;
`;

(* Encode a boolean into a little-endian array of bytes *)
(* The bool's bit will be placed as if it had been placed with (1 << bit_offset) in C *)
(* i.e. if bit_offset is n, the bit will end up at the nth bit in the array *)
val bool_to_bytes_def = (append_prog o process_topdecs) `
    fun bool_to_bytes b bit_offset len = let
        val array = Word8Array.array len (Word8.fromInt 0) in
        if b then let
            val byte_offset = bit_offset div 8
            val sub_byte_offset = bit_offset mod 8
            val byte = Word8.<< (Word8.fromInt 1) sub_byte_offset in
            array
        end else
            array
        end
`;

(* Encode a boolean into a little-endian array of bytes *)
(* The bool's bit will be placed as if it had been placed with (1 << bit_offset) in C *)
(* i.e. if bit_offset is n, the bit will end up at the nth most significant bit in the word *)
val bool_to_word64_def = (append_prog o process_topdecs) `
    fun bool_to_word64 b bit_offset =
      if b then
        Word64.<< (Word64.fromInt 1) bit_offset
      else
        Word64.fromInt 0
`;

(* Convert an integer to an array of little-endian bytes, placing the integer at
 * the byte offset given by "off". The length of the buffer to produce is "len" and any
 * bits of the number that don't fit into the assigned window are discarded.
 *)
val int_to_bytes_at_def = (append_prog o process_topdecs) `
    fun int_to_bytes_at w off len = let
        val array = Word8Array.array len (Word8.fromInt 0);
        fun loop i divisor =
            if i = len then
                ()
            else
                let val u = Word8Array.update array i (Word8.fromInt (w div divisor));
                in loop (i + 1) (divisor * 256)
                end
        val u = loop off 1;
        in array end;
`;

val int_to_bytes_def = (append_prog o process_topdecs) `
    fun int_to_bytes w len = int_to_bytes_at w 0 len
`;

val int_to_word64_at_def = (append_prog o process_topdecs) `
    fun int_to_word64_at w off = Word64.<< (Word64.fromInt w) off
`;

(* This is not very optimal *)
val word64_to_bytes_def = (append_prog o process_topdecs) `
    fun word64_to_bytes w len = int_to_bytes (Word64.toInt w) len
`;

(* Read the first `len` bytes of `buf` beginning at `off` into a int *)
val bytes_to_int_def = (append_prog o process_topdecs) `
    fun bytes_to_int buf off len = let
        fun loop i acc =
            if i = len then
                acc
            else
                loop (i + 1) (acc * 256 + (Word8.toInt (Word8Array.sub buf (off + len - i - 1))))
        in loop 0 0 end;
`;

val bytes_to_word64_def = (append_prog o process_topdecs) `
    fun bytes_to_word64 buf off len = Word64.fromInt (bytes_to_int buf off len)
`;

(* Read the a nul-terminated string from `buf` beginning at `off` *)
val read_c_string_def = (append_prog o process_topdecs) `
  fun read_c_string buf off len = let
    fun nul_byte_idx i =
      if i = len orelse Word8Array.sub buf i = Word8.fromInt 0 then
        i
      else
        nul_byte_idx (i + 1);
    val str_len = nul_byte_idx off - off;
    in (Word8Array.substring buf off str_len, str_len) end;
`;

(* Convert a string to a Word8Array *)
val string_to_bytes_def = (append_prog o process_topdecs) `
  fun string_to_bytes str = let
    val len = String.size str;
    val result = Word8Array.array len (Word8.fromInt 0);
    val u = Word8Array.copyVec str 0 len result 0;
    in result end;
`;

(* Binary OR two Word8 arrays together (must be the same length) *)
val word8_array_orb_def = (append_prog o process_topdecs) `
    fun word8_array_orb arr1 arr2 = let
        val len = Word8Array.length arr1;
        val u =
            if len <> Word8Array.length arr2 then
                fail "word8_array_orb: length mismatch"
            else
                ();
        val bytes = List.genlist (fn i => (i, Word8.orb (Word8Array.sub arr1 i) (Word8Array.sub arr2 i))) len;
        val result = Word8Array.array len (Word8.fromInt 0);
        val u = List.app (fn x => Word8Array.update result (fst x) (snd x)) bytes;
        in
            result
        end
`;

val _ = ml_prog_update (close_module NONE);

val _ = export_theory ();
