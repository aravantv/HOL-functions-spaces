(* ========================================================================= *)
(*                                                                           *)
(*                Library of complex function vector spaces:                 *)
(*                  Application to complex vectors.                          *)
(*                                                                           *)
(*   (c) Copyright, Sanaz Khan Afshar, Vincent Aravantinos, 2012-2013        *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*          Contact: <s_khanaf@ece.concordia.ca>, <vincent@ece.concordia.ca> *)
(*                                                                           *)
(* TODO: linearity, matrices, R^2^N <=> R^N^2, flatten                       *)
(* ========================================================================= *)

needs "cfunspace.ml";;


(* ------------------------------------------------------------------------- *)
(* VECTOR MAPS                                                               *)
(* ------------------------------------------------------------------------- *)

let vector_const = new_definition
  `vector_const (k:A) :A^N = lambda i. k`;;
let vector_map = new_definition
  `vector_map (f:A->B) (v:A^N) :B^N = lambda i. f(v$i)`;;
let vector_map2 = new_definition
  `vector_map2 (f:A->B->C) (v1:A^N) (v2:B^N) :C^N =
    lambda i. f (v1$i) (v2$i)`;;

let FINITE_INDEX_INRANGE_2 = prove
 (`!i. ?k. 1 <= k /\ k <= dimindex(:N) /\ (!x:A^N. x$i = x$k)
  /\ (!x:B^N. x$i = x$k) /\ (!x:C^N. x$i = x$k) /\ (!x:D^N. x$i = x$k)`,
  REWRITE_TAC[finite_index] THEN MESON_TAC[FINITE_INDEX_WORKS]);;

let common_prove x = prove(x,
  REPEAT GEN_TAC THEN CHOOSE_TAC (SPEC_ALL FINITE_INDEX_INRANGE_2)
  THEN ASM_SIMP_TAC[vector_const;vector_map;vector_map2;LAMBDA_BETA]);;

let VECTOR_CONST_COMPONENT = common_prove
  `!i k. ((vector_const k):A^N)$i = k`;;

let VECTOR_MAP_COMPONENT = common_prove
  `!i f:A->B v:A^N. (vector_map f v)$i = f (v$i)`;;

let VECTOR_MAP2_COMPONENT = common_prove
  `!i f:A->B->C v1:A^N v2. (vector_map2 f v1 v2)$i = f (v1$i) (v2$i)`;;


(* ------------------------------------------------------------------------- *)
(* BASIC ARITHMETIC                                                          *)
(* ------------------------------------------------------------------------- *)

make_overloadable "%" `:A-> B-> B`;; 

overload_interface("%",`(vector_mul):real->real^N->real^N`);;

let prioritize_cvector () =
  overload_interface("--",`(cvector_neg):complex^N->complex^N`);
  overload_interface("+",`(cvector_add):complex^N->complex^N->complex^N`);
  overload_interface("-",`(cvector_sub):complex^N->complex^N->complex^N`);
  overload_interface("%",`(cvector_mul):complex->complex^N->complex^N`);;

prioritize_complex ();;

(* The following definitions can be accessed by prefixing "cvector_" to their
 * names. *)
List.iter (fun (s,t) ->
  let s' = "cvector_" ^ s in Meta.new_definition s' (s' ^ t))
  [
    "add",  "= vector_map2 (+)";
    "sub",  "= vector_map2 (-)";
    "neg",  "= vector_map (--)";
    "mul",  "= vector_map o (*)";
    "zero", "= vector_const (Cx(&0))";
    "cnj",  "= vector_map cnj";
  ];;

let CVECTOR_MUL =
  REWRITE_RULE[] (ONCE_REWRITE_RULE[FUN_EQ_THM] (REWRITE_RULE[o_DEF]
    cvector_mul));;

let cvector_defs = CONJS
  [cvector_zero;cvector_neg;cvector_add;cvector_sub;cvector_cnj;CVECTOR_MUL];;

prioritize_cvector ();;

let COMPLEX_CART_EQ = prove
  (`!x y:complex^N. x = y <=> !i. 1 <= i /\ i <= dimindex (:N) ==> x$i = y$i`,
  REWRITE_TAC[CART_EQ]);;

(* ------------------------------------------------------------------------- *)
(* TRANSLATIONS FROM/TO INFINITE                                             *)
(* ------------------------------------------------------------------------- *)

let CART_TYBIJ = prove
  (`(!x. mk_cart (dest_cart x) = x) /\ (!x. dest_cart (mk_cart x) = x)
    /\ mk_cart o dest_cart = I /\ dest_cart o mk_cart = I`,
  REWRITE_TAC[REWRITE_RULE [] cart_tybij;o_DEF;I_DEF]);;

(* FIXME: WARNING name modification here *)
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

(*let is_transformation_ok th =
  let f = (not o can (find_term (fun t -> mem (name_of t) blacklist)) o concl) in
  if f th
  then (print_endline (">>>> " ^ string_of_thm th); true)
  else (print_endline ("-------------------------------------- " ^ string_of_thm th); false)
;;*)

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


(* ========================================================================= *)
(* INNER SPACE                                                               *)
(* ========================================================================= *)


(* First defining cdot and proving that it satisfies the `is_inner_space`
 * predicate.
 *)

parse_as_infix("cdot",(20,"right"));;

let cdot = new_definition
  `(cdot) (x:complex^N) (y:complex^N) =
    vsum (1..dimindex(:N)) (\i. cnj(x$i) * y$i)`;;

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
  (`norm x pow 2 = &0 <=> norm x = &0`,
  REWRITE_TAC[REAL_POW_EQ_0] THEN GCONV_TAC ARITH_RULE);;

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

let MK_CART_FUN_MAP = prove
  (`!f x. mk_cart (f o x) = vector_map f (mk_cart x)`,
  REWRITE_TAC[FORALL_CFUN;FUN_MAP_DEST_CART;CART_TYBIJ]);;

let MK_CART_FUN_MAP2 = prove
  (`!f x y. mk_cart (fun_map2 f x y) = vector_map2 f (mk_cart x) (mk_cart y)`,
  REWRITE_TAC[FORALL_CFUN;FUN_MAP2_DEST_CART;CART_TYBIJ]);;

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

let corthogonal = new_definition
  `corthogonal x y <=> x cdot y = Cx(&0)`;;

let ARE_ORTHOGONAL_CORTHOGONAL = prove
  (`!x y. are_orthogonal (UNIV,\x y. (mk_cart x) cdot (mk_cart y))
      (dest_cart x) (dest_cart y) <=> corthogonal x y`,
  REWRITE_TAC[are_orthogonal;CDOT_IS_INNER_SPACE;CART_TYBIJ;IN_UNIV;
    corthogonal]);;

let MK_CART_FUN_EQ_THM = prove
  (`!f g. (\x. f (mk_cart x)) = (\x. g (mk_cart x)) <=> (\x. f x) = (\x. g x)`,
  REWRITE_TAC[FUN_EQ_THM] THEN MESON_TAC[CART_TYBIJ]);;

(* Then deriving the results from the abstract ones. *)

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

(* ========================================================================= *)
(* LINEAR OPERATORS                                                          *)
(* ========================================================================= *)

let clinear = new_definition
  `clinear (f:complex^M->complex^N)
    <=> (!x y. f (x + y) = f x + f y) /\ (!c x. f (c % x) = c % f x)`;;

let MK_CART_K = prove
  (`!x. mk_cart (K x) = vector_const x`,
  REWRITE_TAC[K_DEST_CART;CART_TYBIJ;FORALL_CFUN]);;

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


(* ========================================================================= *)
(* MATRICES                                                                  *)
(* ========================================================================= *)

let cbasis = new_definition
  `cbasis k = lambda i. if i = k then Cx(&1) else Cx(&0)`;;

let cfun_basis = new_definition
  `cfun_basis (x:A) : cfun = \y. if y = x then Cx(&1) else Cx(&0)`;;

let CMATRIX_OF_COP = new_definition
  `cmatrix_of_cop (op:((N)finite_image->complex)->((M)finite_image->complex))
    : complex^N^M =
    lambda i j. mk_cart (op (cfun_basis (finite_index j)))$i`;;

let cmatrix_of_cop = prove
  (`!op.
    cmatrix_of_cop op = lambda i j. mk_cart (op (dest_cart (cbasis j)))$i`,
  REWRITE_TAC[CMATRIX_OF_COP;cfun_basis;cbasis;DEST_CART_LAMBDA]
  THEN ONCE_REWRITE_TAC[CART_EQ] THEN REWRITE_TAC[COMPLEX_CART_EQ]
  THEN SIMP_TAC[LAMBDA_BETA] THEN REPEAT STRIP_TAC
  THEN AP_THM_TAC THEN REPEAT AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM]
  THEN GEN_TAC THEN REPEAT COND_CASES_TAC
  THEN ASM_MESON_TAC[REWRITE_RULE[IN_NUMSEG] finite_image_tybij]);;

overload_interface ("**",
  `(cmatrix_cvector_mul):complex^N^M->complex^N->complex^M`);;

let cmatrix_cvector_mul = new_definition
  `!m:complex^N^M v:complex^N.
        m ** v = lambda i. vsum(1..dimindex(:N)) (\j. m$i$j * v$j)`;;

let cop_of_cmatrix = new_definition
  `cop_of_cmatrix (m:complex^N^M) = \f. dest_cart (m ** mk_cart f)`;;

let CMATRIX_OF_COP_OF_CMATRIX = prove
  (`!m:complex^N^M. cmatrix_of_cop (cop_of_cmatrix m) = m`,
  REWRITE_TAC[CMATRIX_OF_COP;cop_of_cmatrix;cfun_basis;cmatrix_cvector_mul]
  THEN REPLICATE_TAC 2 (ONCE_REWRITE_TAC[CART_EQ])
  THEN SIMP_TAC[LAMBDA_BETA;CART_TYBIJ]
  THEN REWRITE_TAC[finite_index;CART_TYBIJ]
  THEN SIMP_TAC[GSYM finite_index;FINITE_INDEX_INJ]
  THEN SPEC_TAC (`dimindex(:N)`,`n:num`) THEN INDUCT_TAC
  THEN REWRITE_TAC[ARITH_RULE `~(1 <= x /\ x <= 0)`]
  THEN REWRITE_TAC[VSUM_CLAUSES_NUMSEG;ARITH_RULE `1 <= SUC n`]
  THEN REPEAT STRIP_TAC THEN ASM_CASES_TAC `SUC n = i'` 
  THENL [
    ASM_REWRITE_TAC[COMPLEX_MUL_RID;COMPLEX_EQ_ADD_RCANCEL_0;GSYM COMPLEX_VEC_0]
    THEN MATCH_MP_TAC VSUM_EQ_0 THEN REPEAT STRIP_TAC THEN REWRITE_TAC[]
    THEN COND_CASES_TAC
    THENL [
      ASM_MESON_TAC[ARITH_RULE `~(SUC n <= n)`;IN_NUMSEG];
      REWRITE_TAC[COMPLEX_VEC_0;COMPLEX_MUL_RZERO];
    ];
    ASM_REWRITE_TAC[COMPLEX_MUL_RZERO;COMPLEX_ADD_RID]
    THEN Pa.SUBGOAL_THEN "i' <= n:num" (wrap ASM_MESON_TAC)
    THEN REPEAT (POP_ASSUM MP_TAC) THEN ARITH_TAC
  ]);;

let COP_OF_CMATRIX_CFUN_SUM = prove
  (`!m f. cop_of_cmatrix (m:complex^N^M) f
    = cfun_sum (1..dimindex (:N)) (\j x. (dest_cart m x$j) * mk_cart f$j)`,
  SIMP_TAC[CFUN_EQ;cop_of_cmatrix;cmatrix_cvector_mul;FINITE_NUMSEG;
    CFUN_SUM_VSUM;FORALL_FINITE_INDEX;GSYM finite_index;LAMBDA_BETA]);;

let lemma = prove
  (`!f:(N)finite_image->complex n j.
    j <= dimindex(:N) /\ n < j
    ==> cfun_sum (1..n)
      (\i. f (finite_index i) % cfun_basis (finite_index i)
      :(N)finite_image->complex)
      (finite_index j)
      = Cx(&0)`,
 GEN_TAC THEN INDUCT_TAC
 THENL [
   REWRITE_TAC[CFUN_SUM_CLAUSES_NUMSEG;CFUN_TO_COMPLEX;ARITH_RULE `~(1=0)`];
   ASM_SIMP_TAC[CFUN_SUM_CLAUSES_NUMSEG;ARITH_RULE `1 <= SUC n`;CFUN_ADD;ARITH_RULE `SUC n < j ==> n < j`;COMPLEX_ADD_LID]
   THEN REWRITE_TAC[cfun_basis;CFUN_SMUL_THM]
   THEN IMP_REWRITE_TAC[FINITE_INDEX_INJ;ARITH_RULE `(x:num) < y ==> (y=x)=F`]
   THEN REWRITE_TAC[COMPLEX_MUL_RZERO] THEN ARITH_TAC
 ]);;

let lemma' = prove
  (`!f:(N)finite_image->complex n j.
    1 <= j /\ j <= n /\ n <= dimindex(:N)
    ==> cfun_sum (1..n)
      (\i. f (finite_index i) % cfun_basis (finite_index i)
      :(N)finite_image->complex)
      (finite_index j)
      = f (finite_index j)`,
 GEN_TAC THEN INDUCT_TAC
 THENL [
   ARITH_TAC;
   REWRITE_TAC[CFUN_SUM_CLAUSES_NUMSEG;ARITH_RULE `1<=SUC k`]
   THEN GEN_TAC THEN ASM_CASES_TAC `j = SUC n` THEN ASM_REWRITE_TAC[CFUN_ADD]
   THENL [
     IMP_REWRITE_TAC[lemma]
     THEN REWRITE_TAC[CFUN_SMUL_THM;COMPLEX_ADD_LID;COMPLEX_MUL_RID;cfun_basis]
     THEN ARITH_TAC;
     ASM_IMP_REWRITE_TAC[CFUN_SMUL_THM;cfun_basis;FINITE_INDEX_INJ]
     THEN ASM_REWRITE_TAC[COMPLEX_MUL_RZERO;COMPLEX_ADD_RID]
     THEN POP_ASSUM MP_TAC THEN ARITH_TAC
 ]]);;

let CFUN_FINITE_BASIS_EXPANSION = prove
  (`!f:(N)finite_image->complex.
    f = cfun_sum (1..dimindex(:N)) 
      \i. f (finite_index i) % cfun_basis (finite_index i)`,
  IMP_REWRITE_TAC[CFUN_EQ;FORALL_FINITE_INDEX;lemma';LE_REFL]);;

let LINCOP_FINITE_BASIS_EXPANSION = prove
  (`!op f:(N)finite_image->complex.
    is_linear_cop op ==>
    op f = cfun_sum (1..dimindex(:N))
      (\i. f (finite_index i) % op (cfun_basis (finite_index i)))`,
  CONV_TAC (PATH_CONV "rbrbrl" (ONCE_REWRITE_CONV [CFUN_FINITE_BASIS_EXPANSION]))
  THEN IMP_REWRITE_TAC[LINCOP_SUM;FINITE_NUMSEG;o_DEF;LINCOP_SMUL]);;

let COP_OF_CMATRIX_OF_COP = prove
  (`!op:((N)finite_image->complex)->((M)finite_image->complex).
    is_linear_cop op ==> cop_of_cmatrix (cmatrix_of_cop op) = op`,
  REWRITE_TAC[COP_EQ;COP_OF_CMATRIX_CFUN_SUM]
  THEN ONCE_SIMP_TAC[LINCOP_FINITE_BASIS_EXPANSION]
  THEN IMP_REWRITE_TAC[CFUN_SUM_EQ]
  THEN REWRITE_TAC[FUN_EQ_THM;CMATRIX_OF_COP;CFUN_SMUL_THM;finite_index;CART_TYBIJ]
  THEN IMP_REWRITE_TAC [COMPLEX_FIELD `x = z ==> x * y = y * z`]
  THEN REPEAT STRIP_TAC THEN Pa.SPEC_TAC ("x'","x'")
  THEN SIMP_TAC[FORALL_FINITE_INDEX;GSYM finite_index;LAMBDA_BETA]
  THEN ASM_SIMP_TAC[REWRITE_RULE[GSYM IN_NUMSEG] LAMBDA_BETA]);;

let VSUM_CMUL = prove
  (`!a f s. FINITE s ==> vsum s (\x. a * f x) = a * vsum s f`,
  ONCE_REWRITE_TAC[TAUT `(A ==> B) <=> (A ==> A ==> B)`]
  THEN REPEAT (MATCH_MP_TAC FINITE_INDUCT ORELSE GEN_TAC)
  THEN SIMP_TAC[COMPLEX_VEC_0;COMPLEX_MUL_RZERO;VSUM_CLAUSES;FINITE_INSERT]
  THEN REPEAT GEN_TAC THEN COND_CASES_TAC
  THEN REWRITE_TAC[COMPLEX_ADD_LDISTRIB]);;

let BETA_MK_CART = prove
  (`!f i. mk_cart f$i = f (finite_index i)`,
  REWRITE_TAC[finite_index;CART_TYBIJ]);;

let LINCOP_COP_OF_CMATRIX = prove
  (`!m. is_linear_cop (cop_of_cmatrix m)`,
  REWRITE_TAC[is_linear_cop;cop_of_cmatrix;cmatrix_cvector_mul]
  THEN REWRITE_TAC[DEST_CART_LAMBDA;FUN_EQ_THM;CFUN_ADD;CFUN_SMUL]
  THEN SIMP_TAC[GSYM VSUM_ADD;GSYM VSUM_CMUL;FINITE_NUMSEG;
    GSYM COMPLEX_ADD_LDISTRIB;GSYM CFUN_ADD;GSYM CFUN_SMUL]
  THEN REWRITE_TAC[BETA_MK_CART;CFUN_SMUL;CFUN_ADD;COMPLEX_MUL_AC]);;

let COP_OF_CMATRIX_INJ = prove
  (`!m1 m2. cop_of_cmatrix m1 = cop_of_cmatrix m2 <=> m1 = m2`,
  MESON_TAC[CMATRIX_OF_COP_OF_CMATRIX;COP_OF_CMATRIX_OF_COP;
    LINCOP_COP_OF_CMATRIX]);;

let FORALL_LINCOP = prove
  (`!P. (!op. is_linear_cop op ==> P op) <=> (!m. P (cop_of_cmatrix m))`,
  MESON_TAC[CMATRIX_OF_COP_OF_CMATRIX;COP_OF_CMATRIX_OF_COP;
    LINCOP_COP_OF_CMATRIX]);;

let FORALL_CMATRIX = prove
  (`!P. (!m. P m) <=> (!op. is_linear_cop op ==> P (cmatrix_of_cop op))`,
  MESON_TAC[CMATRIX_OF_COP_OF_CMATRIX;COP_OF_CMATRIX_OF_COP;
    LINCOP_COP_OF_CMATRIX]);;

let FORALL_COP_MATRIX = prove
  (`!P. (!op. P op) ==> (!m. P (cop_of_cmatrix m))`,
  MESON_TAC[CMATRIX_OF_COP_OF_CMATRIX;COP_OF_CMATRIX_OF_COP;
    LINCOP_COP_OF_CMATRIX]);;

(* Arithmetic definitions *)

make_overloadable "%%" `:A->B->B`;;

let prioritize_cmatrix () =
  overload_interface ("--",`cmatrix_neg:complex^N^M->complex^N^M`);
  overload_interface ("+",`cmatrix_add:complex^N^M->complex^N^M->complex^N^M`);
  overload_interface ("-",`cmatrix_sub:complex^N^M->complex^N^M->complex^N^M`);
  overload_interface ("%%",`cmatrix_smul:complex->complex^N^M->complex^N^M`);
  overload_interface
    ("**",`cmatrix_mul:complex^N^M->complex^P^N->complex^P^M`);;

(* The following definitions can be accessed by prefixing "cvector_" to their
 * names. *)
List.iter (fun (s,t) ->
  let s' = "cmatrix_" ^ s in Meta.new_definition s' (s' ^ t))
  [
    "add",  "= vector_map2 (+)";
    "sub",  "= vector_map2 (-)";
    "neg",  "= vector_map (--)";
    "smul", "= vector_map o (%)";
    "zero", "= vector_const cvector_zero";
    "mul",  "= \m1:complex^N^M m2:complex^P^N.
      lambda i j. vsum(1..dimindex(:N)) (\k. m1$i$k * m2$k$j)";
    "cnj", "= vector_map cvector_cnj";
  ];;

let _ = prioritize_cmatrix ();;

let CMATRIX_SMUL =
  REWRITE_RULE[] (ONCE_REWRITE_RULE[FUN_EQ_THM] (REWRITE_RULE[o_DEF]
    cmatrix_smul));;

let cmatrix_defs = CONJS [cmatrix_add;cmatrix_sub;cmatrix_neg;CMATRIX_SMUL;
  cmatrix_zero];;

let CMATRIX_MUL_ASSOC = prove
  (`!m1:complex^N^M m2:complex^P^N x:complex^P.
   m1 ** m2 ** x = (m1 ** m2) ** x`,
  SIMP_TAC[cmatrix_mul;cmatrix_cvector_mul;COMPLEX_CART_EQ;LAMBDA_BETA]
  THEN IMP_REWRITE_TAC[GSYM VSUM_CMUL;FINITE_NUMSEG]
  THEN ONCE_REWRITE_TAC[VSUM_SWAP_NUMSEG]
  THEN IMP_REWRITE_TAC[ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] (GSYM VSUM_CMUL);
    FINITE_NUMSEG]
  THEN REWRITE_TAC[COMPLEX_MUL_AC]);;

let DEST_CART_CMATRIX_CVECTOR_MUL = prove
  (`!m x. dest_cart (m ** x) = cop_of_cmatrix m (dest_cart x)`,
  REWRITE_TAC[cop_of_cmatrix;CART_TYBIJ]);;

let MUL_COP_OF_CMATRIX = prove
  (`!m1:complex^M^N m2:complex^P^M.
    cop_of_cmatrix m1 ** cop_of_cmatrix m2 = cop_of_cmatrix (m1 ** m2)`,
  REWRITE_TAC[cop_of_cmatrix;cop_mul;COP_EQ;o_THM;CART_TYBIJ;CMATRIX_MUL_ASSOC]);;

let VSUM_CXZERO = prove
  (`!s. vsum s (\x. Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[GSYM COMPLEX_VEC_0;VSUM_0]);;

let common_prove t = prove(t,
  SIMP_TAC[cmatrix_defs;cop_of_cmatrix;COP_EQ;COP_TO_CFUN;cfun_defs;PULL_DEST_CART;
    vector_map2;DEST_CART_INJ;COMPLEX_CART_EQ;LAMBDA_BETA;cmatrix_cvector_mul;
    GSYM (CONJS [VSUM_ADD;VSUM_SUB;VSUM_NEG;VSUM_CMUL]);FINITE_NUMSEG;cvector_defs;
    VECTOR_MAP2_COMPONENT;VECTOR_MAP_COMPONENT;VECTOR_CONST_COMPONENT;VSUM_CXZERO;
    COMPLEX_MUL_LZERO;CNJ_VSUM]
  THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[FUN_EQ_THM]
  THEN SIMPLE_COMPLEX_ARITH_TAC);;

let ADD_COP_OF_MATRIX = common_prove
  `!m1 m2. cop_of_cmatrix m1 + cop_of_cmatrix m2 = cop_of_cmatrix (m1 + m2)`;;

let SUB_COP_OF_MATRIX = common_prove
  `!m1 m2. cop_of_cmatrix m1 - cop_of_cmatrix m2 = cop_of_cmatrix (m1 - m2)`;;

let NEG_COP_OF_MATRIX = common_prove
  `!m. --cop_of_cmatrix m = cop_of_cmatrix (--m)`;;

let SMUL_COP_OF_MATRIX = common_prove
  `!m a. a % cop_of_cmatrix m = cop_of_cmatrix (a %% m)`;;

let COP_ZERO_AS_COP_OF_MATRIX = common_prove
  `cop_zero = cop_of_cmatrix cmatrix_zero`;;

let PULL_COP_OF_CMATRIX = CONJS
    [MUL_COP_OF_CMATRIX;ADD_COP_OF_MATRIX;SUB_COP_OF_MATRIX;
      NEG_COP_OF_MATRIX;SMUL_COP_OF_MATRIX;COP_ZERO_AS_COP_OF_MATRIX];;

let lincop_to_cmatrix =
  let TRY_IMPCONV_RULE c th = try IMPCONV_RULE c th with _ -> th in
  let intro =
    TRY_IMPCONV_RULE (REDEPTH_IMPCONV (MATCH_MP_IMPCONV FORALL_COP_MATRIX)) 
      o REWRITE_RULE [FORALL_LINCOP]
  in
  let pull = REWRITE_RULE[PULL_COP_OF_CMATRIX] in
  let elim = REWRITE_RULE[COP_OF_CMATRIX_INJ] in
  let elim_more = SIMP_RULE[COP_EQ;FORALL_FINITE_INDEX;GSYM finite_index] in
  (* UNIQUE_NAME_RULE is used only for cosmetic purposes, to have nice names *)
  UNIQUE_NAME_RULE o elim_more o elim o pull o intro;;

let _ = map_thms "CMATRIX" (lincop_to_cmatrix o finitize_type)
  (fun _ -> cop_thms () @ linear_thms ());;


(* ========================================================================= *)
(* MATRIX HERMITIANS                                                         *)
(* ========================================================================= *)

let ctransp = new_definition
  `(ctransp:complex^N^M->complex^M^N) m = lambda i j. m$j$i`;;

let cmatrix_herm = new_definition
  `cmatrix_herm = cmatrix_cnj o ctransp`;;

(*let MATRIX_HERMITIAN = prove
  (`!m. is_hermitian (UNIV,\x y. (mk_cart x) cdot (mk_cart y))
    (cop_of_cmatrix m) (cop_of_cmatrix (cmatrix_herm m))`,
  REWRITE_TAC[is_hermitian;is_closed_by;IN_UNIV;CDOT_IS_INNER_SPACE;CART_TYBIJ;
    o_DEF;cdot;LINCOP_COP_OF_CMATRIX;cmatrix_cvector_mul;cmatrix_herm;
    cop_of_cmatrix;cmatrix_cnj;cvector_cnj;VECTOR_MAP_COMPONENT;ctransp]
  THEN REPEAT GEN_TAC THEN MATCH_MP_TAC VSUM_EQ
  THEN SIMP_TAC[LAMBDA_BETA;IN_NUMSEG]
  THEN IMP_REWRITE_TAC[GSYM VSUM_CMUL;CNJ_VSUM;FINITE_NUMSEG;CNJ_CNJ;
    ONCE_REWRITE_RULE[COMPLEX_MUL_SYM] (GSYM VSUM_CMUL)]
  THEN REPEAT STRIP_TAC THEN AP_TERM_TAC
  THEN REWRITE_TAC[FUN_EQ_THM]
*)
