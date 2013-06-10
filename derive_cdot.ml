(* ========================================================================= *)
(*                                                                           *)
(*               Deriving cdot theorems from inner space ones.               *)
(*                                                                           *)
(*   (c) Copyright, Vincent Aravantinos, 2012-2013                           *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <vincent@ece.concordia.ca>                             *)
(*                                                                           *)
(* ========================================================================= *)


let CDOT_CNJ = prove
  (`!x y. cnj (x cdot y) = y cdot x`,
  IMP_REWRITE_TAC[cdot;CNJ_VSUM;FINITE_NUMSEG;CNJ_MUL;CNJ_CNJ]
  THEN REWRITE_TAC[COMPLEX_MUL_SYM]);;

let CDOT_SELF_REAL = prove
  (`!x. real (x cdot x)`,
  REWRITE_TAC[REAL_CNJ;CDOT_CNJ]);;

let DIMINDEX_GEQ_1 = prove
  (`!s. 1 <= dimindex s`,
  IMP_REWRITE_TAC[dimindex;COND_ELIM_THM;LE_REFL;
    ARITH_RULE `(1 <= x <=> ~(x=0))`;CARD_EQ_0;UNIV_NOT_EMPTY]);;

let DIMINDEX_NEQ_0 = prove
  (`!s. ~(dimindex s = 0)`,
  REWRITE_TAC[ARITH_RULE `~(x=0) <=> 1 <= x`;DIMINDEX_GEQ_1]);;

let CDOT_SELF_POS = prove
  (`!x. &0 <= real_of_complex (x cdot x)`,
  IMP_REWRITE_TAC[REAL_OF_COMPLEX_RE;CDOT_SELF_REAL;RE_DEF;cdot;VSUM_COMPONENT;
    LE_REFL;DIMINDEX_GEQ_1;SUM_POS_LE_NUMSEG;COMPLEX_MUL_CNJ;GSYM CX_POW;
    GSYM RE_DEF;RE_CX;REAL_LE_POW_2]);;

let LEMMA = prove
  (`!x:real^N. norm x pow 2 = &0 <=> norm x = &0`,
  REWRITE_TAC[REAL_POW_EQ_0;ARITH_RULE `~(2 = 0)`]);;

let CDOT_EQ_0 = prove
  (`!x. x cdot x = Cx(&0) <=> x = cvector_zero`,
  IMP_REWRITE_TAC[TAUT `(p<=>q) <=> ((p==>q) /\ (q==>p))`;
    MESON[REAL;RE_CX] `real x ==> (x = Cx y <=> Re x = y)`;
    CDOT_SELF_REAL;RE_DEF;cdot;VSUM_COMPONENT;LE_REFL;DIMINDEX_GEQ_1;
    cvector_zero]
  THEN ONCE_REWRITE_TAC[CART_EQ]
  THEN SIMP_TAC[VECTOR_CONST_COMPONENT;COMPLEX_MUL_RZERO;GSYM RE_DEF;RE_CX;
    SUM_0]
  THEN REWRITE_TAC[COMPLEX_MUL_CNJ;RE_CX;GSYM CX_POW;GSYM COMPLEX_NORM_ZERO;
    GSYM LEMMA]
  THEN IMPCONV_TAC (PURE_REWRITE_IMPCONV [SUM_POS_EQ_0_NUMSEG])
  THEN REWRITE_TAC[REAL_LE_POW_2]);;

let CDOT_LADD = prove
  (`!x y z. (x + y) cdot z = (x cdot z) + (y cdot z)`,
  IMP_REWRITE_TAC[cdot;cvector_add;VECTOR_MAP2_COMPONENT;CNJ_ADD;
    COMPLEX_ADD_RDISTRIB;VSUM_ADD;FINITE_NUMSEG]);;

let CDOT_RMUL = prove
  (`!c x y. x cdot (c % y) = c * (x cdot y)`,
  IMP_REWRITE_TAC[cdot;cvector_mul;o_THM;VECTOR_MAP_COMPONENT;
    GSYM VSUM_COMPLEX_LMUL;FINITE_NUMSEG]
  THEN REWRITE_TAC[COMPLEX_MUL_AC]);;

let CDOT_IS_INNER_SPACE = prove
  (`is_inner_space (UNIV,\x y. (mk_cart x) cdot (mk_cart y))`,
  REWRITE_TAC[is_inner_space;IN_UNIV;CFUN_SUBSPACE_UNIV;CDOT_CNJ;CDOT_EQ_0;
    CDOT_SELF_REAL;CDOT_SELF_POS;CDOT_LADD;CDOT_RMUL;cfun_smul;cfun_add;o_THM;
    MK_CART_FUN_MAP;MK_CART_FUN_MAP2;
    REWRITE_RULE[FUN_EQ_THM;o_DEF] (GSYM cvector_mul);GSYM cvector_add;
    CDOT_LADD;CDOT_RMUL]
  THEN REWRITE_TAC[GSYM DEST_CART_INJ;CART_TYBIJ;cvector_zero;GSYM
  K_DEST_CART;cfun_zero]);;

(* Orthogonality comes with it *)

let ARE_ORTHOGONAL_CORTHOGONAL = prove
  (`!x y. are_orthogonal (UNIV,\x y. (mk_cart x) cdot (mk_cart y))
      (dest_cart x) (dest_cart y) <=> corthogonal x y`,
  REWRITE_TAC[are_orthogonal;CDOT_IS_INNER_SPACE;CART_TYBIJ;IN_UNIV;
    corthogonal]);;

(* Then deriving the results from the abstract ones. *)

let inner_space_to_cdot =
  let lem1 = MESON[] `(is_inner_space (s,inprod) /\ p ==> q)
    <=> (is_inner_space (s,inprod) ==> p ==> q)`
  in
  fun th ->
    let th' = MATCH_MP (REWRITE_RULE[lem1] th) CDOT_IS_INNER_SPACE in
    let th'' = cfun_to_cvector_with_mk_cart th' in
    REWRITE_RULE[ARE_ORTHOGONAL_CORTHOGONAL;IN_UNIV] th'';;

let _ = map_thms "CDOT" inner_space_to_cdot inner_space_thms;;
let _ = map_thms "CORTHOGONAL" inner_space_to_cdot orthogonal_thms;;

