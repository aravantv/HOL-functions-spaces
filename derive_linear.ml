(* ========================================================================= *)
(*                                                                           *)
(*       Deriving complex linearity theorems from cfun linearity ones.       *)
(*                                                                           *)
(*   (c) Copyright, Vincent Aravantinos, 2012-2013                           *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <vincent@ece.concordia.ca>                             *)
(*                                                                           *)
(* ========================================================================= *)


let MK_CART_K = prove
  (`!x. mk_cart (K x) = vector_const x`,
  REWRITE_TAC[K_DEST_CART;CART_TYBIJ;FORALL_CFUN]);;

let MK_CART_FUN_MAP = prove
  (`!f x. mk_cart (f o x) = vector_map f (mk_cart x)`,
  REWRITE_TAC[FORALL_CFUN;FUN_MAP_DEST_CART;CART_TYBIJ]);;

let MK_CART_FUN_MAP2 = prove
  (`!f x y. mk_cart (fun_map2 f x y) = vector_map2 f (mk_cart x) (mk_cart y)`,
  REWRITE_TAC[FORALL_CFUN;FUN_MAP2_DEST_CART;CART_TYBIJ]);;

let PUSH_MK_CART = CONJS [MK_CART_K;MK_CART_FUN_MAP;MK_CART_FUN_MAP2];;

let LINCOP_CLINEAR = prove
  (`!f. is_linear_cop (dest_cart o f o mk_cart) <=> clinear f`,
  REWRITE_TAC[is_linear_cop;o_THM;cfun_defs;PUSH_MK_CART;PULL_DEST_CART;
    DEST_CART_INJ;GSYM cvector_defs;FORALL_CFUN;CART_TYBIJ;clinear]
  THEN MESON_TAC[]);;

let FUN_CART_SURJ = prove
  (`!op. ?f. op = dest_cart o f o mk_cart`,
  GEN_TAC THEN Pa.EXISTS_TAC "mk_cart o op o dest_cart"
  THEN REWRITE_TAC[FUN_EQ_THM;CART_TYBIJ;o_THM]);;

let FORALL_COP = prove
  (`!P. (!op. P op) = !f. P (dest_cart o f o mk_cart)`,
  MESON_TAC[FUN_CART_SURJ]);;

let I_CART = prove
  (`I = dest_cart o I o mk_cart`,
  REWRITE_TAC[FUN_EQ_THM;o_THM;I_THM;CART_TYBIJ]);;

let MK_CART_FUN_EQ_THM = prove
  (`!f g. (\x. f (mk_cart x)) = (\x. g (mk_cart x)) <=> (\x. f x) = (\x. g x)`,
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[CART_TYBIJ]);;

let cfun_to_cvector_with_mk_cart th =
  let intro_carts = REWRITE_RULE [FORALL_CFUN] in
  let canon = REWRITE_RULE[cfun_defs] in
  let pull = REWRITE_RULE [PULL_DEST_CART] in
  let elim_carts = REWRITE_RULE[DEST_CART_INJ;DEST_CART_FUN_EQ_THM;CART_TYBIJ;
    MK_CART_FUN_EQ_THM]
  in
  let elim_more = SIMP_RULE[CFUN_EQ;FORALL_FINITE_INDEX;GSYM finite_index] in
  let anti_canon = REWRITE_RULE [GSYM cvector_defs] in
  (anti_canon o elim_more o elim_carts o pull o canon o intro_carts) th;;

let cop_to_cvector th =
  let intro_carts = REWRITE_RULE [FORALL_COP;I_CART] in
  let canon = REWRITE_RULE[cop_defs;fun_map2;o_DEF;K_DEF] in
  let elim_lincop = REWRITE_RULE[REWRITE_RULE[o_DEF] LINCOP_CLINEAR] in
  let ALPHA_CONV' t =
    let x = bndvar t in
    if (name_of x).[0] = '_'
    then ALPHA_CONV (mk_var ("v",type_of x)) t
    else failwith "ALPHA_CONV'"
  in
  let clean = CONV_RULE (DEPTH_CONV ALPHA_CONV') in
  (UNIQUE_NAME_RULE o clean o elim_lincop o cfun_to_cvector_with_mk_cart
    o canon o intro_carts) th;;

let _ = map_thms "CLINEAR" (cop_to_cvector o finitize_type) linear_thms;;

