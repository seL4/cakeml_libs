(*
 * Copyright 2018, Data61
 * Commonwealth Scientific and Industrial Research Organisation (CSIRO)
 * ABN 41 687 119 230.
 *
 * This software may be distributed and modified according to the terms of
 * the BSD 2-Clause license. Note that NO WARRANTY is provided.
 * See "LICENSE_BSD2.txt" for details.
 *
 * @TAG(DATA61_BSD)
 *)

open preamble basis bigStepTheory semanticPrimitivesTheory ml_translatorTheory
     ml_translatorLib ml_progLib cfLib;

fun derive_eval_thm_bytes for_eval v_name e len = let
    val th = get_ml_prog_state () |> get_thm
    val th = MATCH_MP ml_progTheory.ML_code_Dlet_var th
           |> REWRITE_RULE [ml_progTheory.ML_code_env_def]
    val th = th |> CONV_RULE(RESORT_FORALL_CONV(sort_vars["e","s3"]))
              |> SPEC e
    val st = th |> SPEC_ALL |> concl |> dest_imp |> #1 |> strip_comb |> #2 |> el 1
    val new_st = ``^st with refs := ^st.refs ++ [W8array (REPLICATE ^(numSyntax.term_of_int len) 0w)]``
    val goal = th |> SPEC new_st |> SPEC_ALL |> concl |> dest_imp |> fst
    val lemma = goal |> (EVAL THENC SIMP_CONV(srw_ss())[semanticPrimitivesTheory.state_component_equality])
    val v_thm = prove(mk_imp(lemma |> concl |> rand, goal),
    rpt strip_tac \\ rveq \\ match_mp_tac(#2(EQ_IMP_RULE lemma))
    \\ asm_simp_tac bool_ss [])
    |> GEN_ALL |> SIMP_RULE std_ss [] |> SPEC_ALL;
    val v_tm = v_thm |> concl |> strip_comb |> #2 |> last
    val v_def = define_abbrev false v_name v_tm
    in v_thm |> REWRITE_RULE [GSYM v_def] end

structure camkesUtils = struct
    val derive_eval_thm_bytes = derive_eval_thm_bytes
end
