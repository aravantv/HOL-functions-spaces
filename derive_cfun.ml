(* ========================================================================= *)
(*                                                                           *)
(*       Deriving complex vector theorems from cfun theorems.                *)
(*                                                                           *)
(*   (c) Copyright, Vincent Aravantinos, 2012-2013                           *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <vincent@ece.concordia.ca>                             *)
(*                                                                           *)
(* ========================================================================= *)


let CART_TYBIJ = prove
  (`(!x. mk_cart (dest_cart x) = x) /\ (!x. dest_cart (mk_cart x) = x)
    /\ mk_cart o dest_cart = I /\ dest_cart o mk_cart = I`,
  REWRITE_TAC[REWRITE_RULE [] cart_tybij;o_DEF;I_DEF]);;

let FORALL_CFUN = prove
  (`!P. (!f. P f) = !v. P (dest_cart v)`,
  MESON_TAC[CART_TYBIJ]);;

let DEST_CART_INJ = prove
  (`!f g. dest_cart f = dest_cart g <=> f = g`,
  MESON_TAC[CART_TYBIJ]);;

let DEST_CART_FUN_EQ_THM = prove
  (`!f g. (\x. dest_cart (f x)) = (\x. dest_cart (g x)) <=> f = g`,
  REWRITE_TAC[FUN_EQ_THM] 
  THEN REWRITE_TAC[REWRITE_RULE[FUN_EQ_THM] DEST_CART_INJ]);;

let MK_CART_INJ = prove
  (`!x y. mk_cart x = mk_cart y <=> x = y`,
  MESON_TAC[CART_TYBIJ]);;

let common_prove t = prove(t,
  REWRITE_TAC[GSYM MK_CART_INJ;CART_TYBIJ;CART_EQ;VECTOR_CONST_COMPONENT;
    VECTOR_MAP_COMPONENT;VECTOR_MAP2_COMPONENT]
  THEN REWRITE_TAC[finite_index;CART_TYBIJ;K_THM;o_THM;FUN_MAP2_THM]);;

let K_DEST_CART = common_prove
  `!x. K x = dest_cart (vector_const x)`;;

let FUN_MAP_DEST_CART = common_prove
  `!f x. f o (dest_cart x) = dest_cart (vector_map f x)`;;

let FUN_MAP2_DEST_CART = common_prove
  `!f x y. fun_map2 f (dest_cart x) (dest_cart y)
    = dest_cart (vector_map2 f x y)`;;

let LET_DEST_CART = prove
  (`(let x = dest_cart y in f x y) = (let x = y in f (dest_cart x) y)`,
  REWRITE_TAC[LET_DEF;LET_END_DEF]);;

let PULL_DEST_CART = CONJS
  [K_DEST_CART;FUN_MAP_DEST_CART;FUN_MAP2_DEST_CART;LET_DEST_CART];;

let DEST_CART_LAMBDA = prove
  (`!f. dest_cart ((lambda i. f i):A^N) = \x. f (dest_finite_image x)`,
  SIMP_TAC[GSYM MK_CART_INJ;CART_TYBIJ;CART_EQ;LAMBDA_BETA]
  THEN SIMP_TAC[finite_index;CART_TYBIJ;finite_image_tybij;GSYM IN_NUMSEG]);;

let finitize_type th =
  let tyvs = type_vars_in_term (concl th) in
  INST_TYPE (map (fun v -> mk_type("finite_image",[v]),v) tyvs) th;;

(* Remark to CPP reviewers:
  * the present transformation adds one more transformation (elim_more) to
  * what is described in the paper in order to deal with a few more cases.
  *)
let cfun_to_cvector th =
  let intro_carts = REWRITE_RULE [FORALL_CFUN] in
  let canon = REWRITE_RULE[cfun_defs] in
  let pull = REWRITE_RULE [PULL_DEST_CART] in
  let elim_carts = REWRITE_RULE[DEST_CART_INJ] in
  let elim_more = SIMP_RULE[CFUN_EQ;FORALL_FINITE_INDEX;GSYM finite_index] in
  let anti_canon = REWRITE_RULE [GSYM cvector_defs] in
  (anti_canon o elim_more o elim_carts o pull o canon o intro_carts) th;;

let blacklist =
  ["dest_cart";"fun_map2";"mk_cart";"cop_of_cmatrix";"is_linear_cop"];;

let is_transformation_ok =
  (not o can (find_term (fun t -> mem (name_of t) blacklist)) o concl);;

let temp_thm = ref TRUTH;;

let map_thms pfx f ths =
  C List.iter (ths ()) (fun s,th ->
    temp_thm := f th;
    if is_transformation_ok !temp_thm
    then
      let thm_name = pfx ^ "_" ^ s in
      print_endline ("Deriving theorem " ^ thm_name);
      Meta.let_ thm_name "!temp_thm");;

let _ = map_thms "CVECTOR" (cfun_to_cvector o finitize_type) cfun_thms;;

