(* ========================================================================= *)
(*                                                                           *)
(*                Library of complex function vector spaces:                 *)
(*                  Application to complex vectors.                          *)
(*                                                                           *)
(*   (c) Copyright, Sanaz Khan Afshar & Vincent Aravantinos, 2012-2013       *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*          Contact: <s_khanaf@ece.concordia.ca>, <vincent@ece.concordia.ca> *)
(*                                                                           *)
(* TODO: R^2^N <=> R^N^2, flatten                                            *)
(* ========================================================================= *)

needs "cfunspace.ml";;


(* ------------------------------------------------------------------------- *)
(* BASIC ARITHMETIC                                                          *)
(* ------------------------------------------------------------------------- *)

make_overloadable "%" `:A-> B-> B`;; 

let prioritize_cvector () =
  overload_interface("--",`(cvector_neg):complex^N->complex^N`);
  overload_interface("+",`(cvector_add):complex^N->complex^N->complex^N`);
  overload_interface("-",`(cvector_sub):complex^N->complex^N->complex^N`);
  overload_interface("%",`(cvector_mul):complex->complex^N->complex^N`);;

prioritize_complex ();;

(* The following definitions can be accessed by prefixing "cvector_" to their
 * names. *)
(* Remark to CPP reviewers: these definition slightly differ from their
 * presentation in the paper since we make use of general combinators
 * (vector_map, vector_map2, vector_const) which allow to factorize some proofs.
 * The resulting definitions are equivalent however.
 *)
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

needs "derive_cfun.ml";;

let CVECTOR_NON_ZERO = prove
  (`!x:complex^N. ~(x=cvector_zero)
    <=> ?i. 1 <= i /\ i <= dimindex(:N) /\ ~(x$i = Cx(&0))`,
  GEN_TAC THEN EQ_TAC THEN IMP_REWRITE_TAC[COMPLEX_CART_EQ;CVECTOR_ZERO]
  THEN MESON_TAC[]);;

let CVECTOR_MUL_COMPONENT = prove
  (`!c:complex X:complex^N i. ((c % X)$i = c * X$i)`,
  REWRITE_TAC[cvector_mul;o_THM;VECTOR_MAP_COMPONENT]);;

let CVECTOR_ADD_COMPONENT = prove
  (`!X Y:complex^N i. ((X + Y)$i = X$i + Y$i)`,
  REWRITE_TAC[cvector_add;VECTOR_MAP2_COMPONENT]);;

let CVECTOR_SUB_COMPONENT = prove 
  (`!X:complex^N Y i. ((X - Y)$i = X$i - Y$i)`,
  REWRITE_TAC[cvector_sub;VECTOR_MAP2_COMPONENT]);;

let CVECTOR_NEG_COMPONENT = prove
  (`!X:complex^N i. ((--X)$i = --(X$i))`,
  REWRITE_TAC[cvector_neg;VECTOR_MAP_COMPONENT]);;

let CVECTOR_ZERO_COMPONENT = prove
  (`!i. (cvector_zero:complex^N)$i = Cx(&0)`,
  REWRITE_TAC[cvector_zero;VECTOR_CONST_COMPONENT]);;

(* Simple generic tactic adapted from VECTOR_ARITH_TAC *)
let CVECTOR_ARITH_TAC =
  let RENAMED_LAMBDA_BETA th =
    if fst(dest_fun_ty(type_of(funpow 3 rand (concl th)))) = aty
    then INST_TYPE [aty,bty; bty,aty] LAMBDA_BETA else LAMBDA_BETA 
  in
  POP_ASSUM_LIST(K ALL_TAC)
  THEN REPEAT(GEN_TAC ORELSE CONJ_TAC ORELSE DISCH_TAC ORELSE EQ_TAC)
  THEN REPEAT(POP_ASSUM MP_TAC) THEN REWRITE_TAC[IMP_IMP; GSYM CONJ_ASSOC]
  THEN GEN_REWRITE_TAC ONCE_DEPTH_CONV [CART_EQ]
  THEN REWRITE_TAC[AND_FORALL_THM] THEN TRY EQ_TAC
  THEN TRY(MATCH_MP_TAC MONO_FORALL) THEN GEN_TAC
  THEN REWRITE_TAC[TAUT `(a ==> b) /\ (a ==> c) <=> a ==> b /\ c`;
    TAUT `(a ==> b) \/ (a ==> c) <=> a ==> b \/ c`]
  THEN TRY (MATCH_MP_TAC(TAUT `(a ==> b ==> c) ==> (a ==> b) ==> (a ==> c)`))
  THEN REWRITE_TAC[cvector_zero;cvector_add;cvector_sub;cvector_neg;
    CVECTOR_MUL;vector_map;vector_map2;vector_const]
  THEN DISCH_THEN(fun th -> REWRITE_TAC[MATCH_MP(RENAMED_LAMBDA_BETA th) th])
  THEN SIMPLE_COMPLEX_ARITH_TAC;;

let CVECTOR_ARITH tm = prove(tm,CVECTOR_ARITH_TAC);;


(* ------------------------------------------------------------------------- *)
(* LINEAR OPERATORS                                                          *)
(* ------------------------------------------------------------------------- *)

let clinear = new_definition
  `clinear (f:complex^M->complex^N)
    <=> (!x y. f (x + y) = f x + f y) /\ (!c x. f (c % x) = c % f x)`;;

needs "derive_linear.ml";;


(* ------------------------------------------------------------------------- *)
(* PASTING COMPLEX VECTORS                                                   *)
(* ------------------------------------------------------------------------- *)

let CLINEAR_FSTCART_SNDCART = prove
  (`clinear fstcart /\ clinear sndcart`,
  SIMP_TAC[clinear;fstcart;sndcart;CART_EQ;LAMBDA_BETA;CVECTOR_ADD_COMPONENT;
    CVECTOR_MUL_COMPONENT; DIMINDEX_FINITE_SUM;
    ARITH_RULE `x <= a ==> x <= a + b:num`;
    ARITH_RULE `x <= b ==> x + a <= a + b:num`]);;

let FSTCART_CLINEAR = CONJUNCT1 CLINEAR_FSTCART_SNDCART;;
let SNDCART_CLINEAR = CONJUNCT2 CLINEAR_FSTCART_SNDCART;;

let FSTCART_SNDCART_CVECTOR_ZERO = prove
  (`fstcart cvector_zero = cvector_zero
  /\ sndcart cvector_zero = cvector_zero`,
  SIMP_TAC[CVECTOR_ZERO_COMPONENT;fstcart;sndcart;LAMBDA_BETA;CART_EQ;
    DIMINDEX_FINITE_SUM;ARITH_RULE `x <= a ==> x <= a + b:num`;
    ARITH_RULE `x <= b ==> x + a <= a + b:num`]);;

let FSTCART_CVECTOR_ZERO = CONJUNCT1 FSTCART_SNDCART_CVECTOR_ZERO;;
let SNDCART_CVECTOR_ZERO = CONJUNCT2 FSTCART_SNDCART_CVECTOR_ZERO;;

let FSTCART_SNDCART_CVECTOR_ADD = prove
 (`!x:complex^(M,N)finite_sum y.
  fstcart(x + y) = fstcart(x) + fstcart(y) 
  /\ sndcart(x + y) = sndcart(x) + sndcart(y)`,
  REWRITE_TAC[REWRITE_RULE[clinear] CLINEAR_FSTCART_SNDCART]);;

let FSTCART_SNDCART_CVECTOR_MUL = prove
  (`!x:complex^(M,N)finite_sum c.
  fstcart(c % x) = c % fstcart(x) /\ sndcart(c % x) = c % sndcart(x)`,
  REWRITE_TAC[REWRITE_RULE[clinear] CLINEAR_FSTCART_SNDCART]);;

let PASTECART_TAC xs =
  REWRITE_TAC(PASTECART_EQ::FSTCART_PASTECART::SNDCART_PASTECART::xs);;

let PASTECART_CVECTOR_ZERO = prove
  (`pastecart (cvector_zero:complex^N) (cvector_zero:complex^M)
    = cvector_zero`,
  PASTECART_TAC[FSTCART_SNDCART_CVECTOR_ZERO]);;

let PASTECART_EQ_CVECTOR_ZERO = prove
  (`!x:complex^N y:complex^M.
    pastecart x y = cvector_zero <=> x = cvector_zero /\ y = cvector_zero`,
  PASTECART_TAC [FSTCART_SNDCART_CVECTOR_ZERO]);;

let PASTECART_CVECTOR_ADD = prove
  (`!x1 y2 x2:complex^N y2:complex^M.
    pastecart x1 y1 + pastecart x2 y2 = pastecart (x1 + x2) (y1 + y2)`,
  PASTECART_TAC [FSTCART_SNDCART_CVECTOR_ADD]);;

let PASTECART_CVECTOR_MUL = prove
  (`!x1 x2 c:complex.
    pastecart (c % x1) (c % y1) = c % pastecart x1 y1`,
  PASTECART_TAC [FSTCART_SNDCART_CVECTOR_MUL]);;


(* ------------------------------------------------------------------------- *)
(* INJECTION OF VECTORS INTO COMPLEX VECTORS                                 *)
(* ------------------------------------------------------------------------- *)

let cvector_re = new_definition
  `cvector_re :complex^N -> real^N = vector_map Re`;;
let cvector_im = new_definition
  `cvector_im :complex^N -> real^N = vector_map Im`;;
let vector_to_cvector = new_definition
  `vector_to_cvector :real^N -> complex^N = vector_map Cx`;;

let CVECTOR_RE_COMPONENT = prove
  (`!x:complex^N i. (cvector_re x)$i = Re (x$i)`,
  REWRITE_TAC[cvector_re;VECTOR_MAP_COMPONENT]);;

let CVECTOR_IM_COMPONENT = prove
  (`!x:complex^N i. (cvector_im x)$i = Im (x$i)`,
  REWRITE_TAC[cvector_im;VECTOR_MAP_COMPONENT]);;

let VECTOR_TO_CVECTOR_COMPONENT = prove
  (`!x:real^N i. (vector_to_cvector x)$i = Cx(x$i)`,
  REWRITE_TAC[vector_to_cvector;VECTOR_MAP_COMPONENT]);;

let VECTOR_TO_CVECTOR_ZERO = prove
  (`vector_to_cvector (vec 0) = cvector_zero:complex^N`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[VECTOR_TO_CVECTOR_COMPONENT;CVECTOR_ZERO_COMPONENT;
    VEC_COMPONENT]);;

let VECTOR_TO_CVECTOR_ZERO_EQ = prove
  (`!x:real^N. vector_to_cvector x = cvector_zero <=> x = vec 0`,
  GEN_TAC THEN EQ_TAC THEN SIMP_TAC[VECTOR_TO_CVECTOR_ZERO]
  THEN ONCE_REWRITE_TAC[CART_EQ]
  THEN SIMP_TAC[VECTOR_TO_CVECTOR_COMPONENT;CVECTOR_ZERO_COMPONENT;
    VEC_COMPONENT;CX_INJ]);;

let CVECTOR_ZERO_VEC0 = prove
  (`!x:complex^N.
    x = cvector_zero <=> cvector_re x = vec 0 /\ cvector_im x = vec 0`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_ZERO_COMPONENT;CVECTOR_RE_COMPONENT;
    CVECTOR_IM_COMPONENT;VEC_COMPONENT;COMPLEX_EQ;RE_CX;IM_CX]
  THEN MESON_TAC[]);;

let VECTOR_TO_CVECTOR_MUL = prove
  (`!a x:real^N. vector_to_cvector (a % x) = Cx a % vector_to_cvector x`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[VECTOR_TO_CVECTOR_COMPONENT;CVECTOR_MUL_COMPONENT;
    VECTOR_MUL_COMPONENT;CX_MUL]);;

let CVECTOR_EQ = prove
  (`!x:complex^N y z.
    x = vector_to_cvector y + ii % vector_to_cvector z
    <=> cvector_re x = y /\ cvector_im x = z`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_ADD_COMPONENT;CVECTOR_MUL_COMPONENT;
    CVECTOR_RE_COMPONENT;CVECTOR_IM_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT]
  THEN REWRITE_TAC[COMPLEX_EQ;RE_CX;IM_CX;RE_ADD;IM_ADD;RE_MUL_II;REAL_NEG_0;
    REAL_ADD_RID;REAL_ADD_LID;IM_MUL_II] THEN MESON_TAC[]);;

let CVECTOR_RE_VECTOR_TO_CVECTOR = prove
  (`!x:real^N. cvector_re (vector_to_cvector x) = x`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_RE_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT;RE_CX]);;

let CVECTOR_IM_VECTOR_TO_CVECTOR = prove
  (`!x:real^N. cvector_im (vector_to_cvector x) = vec 0`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_IM_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT;IM_CX;
    VEC_COMPONENT]);;

let CVECTOR_IM_VECTOR_TO_CVECTOR_IM = prove
  (`!x:real^N. cvector_im (ii % vector_to_cvector x) = x`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_IM_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT;IM_CX;
    VEC_COMPONENT;CVECTOR_MUL_COMPONENT;IM_MUL_II;RE_CX]);;

let VECTOR_TO_CVECTOR_CVECTOR_RE_IM = prove
  (`!x:complex^N.
    vector_to_cvector (cvector_re x) + ii % vector_to_cvector (cvector_im x)
      = x`,
  GEN_TAC THEN MATCH_MP_TAC EQ_SYM THEN REWRITE_TAC[CVECTOR_EQ]);;

let CVECTOR_IM_VECTOR_TO_CVECTOR_RE_IM = prove
  (`!x y:real^N.
    cvector_im (vector_to_cvector x + ii % vector_to_cvector y) = y`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_IM_COMPONENT;CVECTOR_ADD_COMPONENT;
    CVECTOR_MUL_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT;IM_ADD;IM_CX;IM_MUL_II;
    RE_CX;REAL_ADD_LID]);;

let CVECTOR_RE_VECTOR_TO_CVECTOR_RE_IM = prove
  (`!x y:real^N.
    cvector_re (vector_to_cvector x + ii % vector_to_cvector y) = x`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_RE_COMPONENT;CVECTOR_ADD_COMPONENT;
    CVECTOR_MUL_COMPONENT;RE_ADD;VECTOR_TO_CVECTOR_COMPONENT;RE_CX;RE_MUL_CX;
    RE_II;REAL_MUL_LZERO;REAL_ADD_RID]);;

let CVECTOR_RE_ADD = prove
  (`!x y:complex^N. cvector_re (x+y) = cvector_re x + cvector_re y`,
  ONCE_REWRITE_TAC[CART_EQ] THEN REWRITE_TAC[CVECTOR_RE_COMPONENT;
    VECTOR_ADD_COMPONENT;CVECTOR_ADD_COMPONENT;RE_ADD]);;

let CVECTOR_IM_ADD = prove
  (`!x y:complex^N. cvector_im (x+y) = cvector_im x + cvector_im y`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_IM_COMPONENT;VECTOR_ADD_COMPONENT;
    CVECTOR_ADD_COMPONENT;IM_ADD]);;

let CVECTOR_RE_MUL = prove
  (`!a x:complex^N. cvector_re (Cx a % x) = a % cvector_re x`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_RE_COMPONENT;VECTOR_MUL_COMPONENT;
    CVECTOR_MUL_COMPONENT;RE_MUL_CX]);;

let CVECTOR_IM_MUL = prove
  (`!a x:complex^N. cvector_im (Cx a % x) = a % cvector_im x`,
  ONCE_REWRITE_TAC[CART_EQ]
  THEN REWRITE_TAC[CVECTOR_IM_COMPONENT;VECTOR_MUL_COMPONENT;
    CVECTOR_MUL_COMPONENT;IM_MUL_CX]);;

let CVECTOR_RE_VECTOR_MAP = prove
  (`!f v:A^N. cvector_re (vector_map f v) = vector_map (Re o f) v`,
  REWRITE_TAC[cvector_re;VECTOR_MAP_VECTOR_MAP]);;

let CVECTOR_IM_VECTOR_MAP = prove
  (`!f v:A^N. cvector_im (vector_map f v) = vector_map (Im o f) v`,
  REWRITE_TAC[cvector_im;VECTOR_MAP_VECTOR_MAP]);;

let VECTOR_MAP_CVECTOR_RE = prove
  (`!f:real->A v:complex^N.
    vector_map f (cvector_re v) = vector_map (f o Re) v`,
  REWRITE_TAC[cvector_re;VECTOR_MAP_VECTOR_MAP]);;

let VECTOR_MAP_CVECTOR_IM = prove
  (`!f:real->A v:complex^N.
    vector_map f (cvector_im v) = vector_map (f o Im) v`,
  REWRITE_TAC[cvector_im;VECTOR_MAP_VECTOR_MAP]);;

let CVECTOR_RE_VECTOR_MAP2 = prove
  (`!f v1:A^N v2:B^N.
    cvector_re (vector_map2 f v1 v2) = vector_map2 (\x y. Re (f x y)) v1 v2`,
  REWRITE_TAC[cvector_re;VECTOR_MAP_VECTOR_MAP2]);;

let CVECTOR_IM_VECTOR_MAP2 = prove
  (`!f v1:A^N v2:B^N.
    cvector_im (vector_map2 f v1 v2) = vector_map2 (\x y. Im (f x y)) v1 v2`,
  REWRITE_TAC[cvector_im;VECTOR_MAP_VECTOR_MAP2]);;


(* ------------------------------------------------------------------------- *)
(* COMPLEX CROSS PRODUCT                                                     *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("ccross",(20,"right"));;

let ccross = new_definition
  `((ccross):complex^3 -> complex^3 -> complex^3) x y = vector [
    x$2 * y$3 - x$3 * y$2;
    x$3 * y$1 - x$1 * y$3;
    x$1 * y$2 - x$2 * y$1
  ]`;; 

let CCROSS_COMPONENT = prove 
  (`!x y:complex^3.
  (x ccross y)$1 = x$2 * y$3 - x$3 * y$2
  /\ (x ccross y)$2 = x$3 * y$1 - x$1 * y$3
  /\ (x ccross y)$3 = x$1 * y$2 - x$2 * y$1`,
  REWRITE_TAC[ccross;VECTOR_3]);;

let CART_EQ3 = prove
  (`!x y:complex^3. x = y <=> x$1 = y$1 /\ x$2 = y$2 /\ x$3 = y$3`,
  GEN_REWRITE_TAC (PATH_CONV "rbrblr") [CART_EQ]
  THEN REWRITE_TAC[DIMINDEX_3;FORALL_3]);;

let ccross_prove t = prove(t,
  REWRITE_TAC[CART_EQ3;CCROSS_COMPONENT;CVECTOR_ZERO_COMPONENT;
    CVECTOR_NEG_COMPONENT;CVECTOR_ADD_COMPONENT;CVECTOR_MUL_COMPONENT]
  THEN SIMPLE_COMPLEX_ARITH_TAC);;

let CCROSS_LZERO = ccross_prove 
  `!x:complex^3. cvector_zero ccross x = cvector_zero`;;

let CCROSS_RZERO = ccross_prove 
  `!x:complex^3. x ccross cvector_zero = cvector_zero`;;

let CCROSS_SKEW = ccross_prove 
  `!x y:complex^3. (x ccross y) = --(y ccross x)`;;

let CCROSS_REFL = ccross_prove 
  `!x:complex^3. x ccross x = cvector_zero`;;

let CCROSS_LADD = ccross_prove
  `!x y z:complex^3. (x + y) ccross z = (x ccross z) + (y ccross z)`;;

let CCROSS_RADD = ccross_prove 
  `!x y z:complex^3. x ccross(y + z) = (x ccross y) + (x ccross z)`;;

let CCROSS_LMUL = ccross_prove 
  `!c x y:complex^3. (c % x) ccross y = c % (x ccross y)`;;

let CCROSS_RMUL = ccross_prove 
  `!c x y:complex^3. x ccross (c % y) = c % (x ccross y)`;;

let CCROSS_LNEG = ccross_prove 
  `!x y:complex^3. (--x) ccross y = --(x ccross y)`;;

let CCROSS_RNEG = ccross_prove 
`!x y:complex^3. x ccross (--y) = --(x ccross y)`;;

let CCROSS_JACOBI = prove
 (`!(x:complex^3) y z.
    x ccross (y ccross z) + y ccross (z ccross x) + z ccross (x ccross y) =
      cvector_zero`,
  REWRITE_TAC[CART_EQ3]
  THEN REWRITE_TAC[CVECTOR_ADD_COMPONENT;CCROSS_COMPONENT;
    CVECTOR_ZERO_COMPONENT] THEN SIMPLE_COMPLEX_ARITH_TAC);;

(* ------------------------------------------------------------------------- *)
(* COMPLEX DOT PRODUCT                                                       *)
(* ------------------------------------------------------------------------- *)

parse_as_infix("cdot",(20,"right"));;

let cdot = new_definition
  `(cdot) (x:complex^N) (y:complex^N) =
    vsum (1..dimindex(:N)) (\i. cnj(x$i) * y$i)`;;

let corthogonal = new_definition
  `corthogonal x y <=> x cdot y = Cx(&0)`;;

needs "derive_cdot.ml";;

let CDOT3 = prove
  (`!x y:complex^3.
    x cdot y = (cnj (x$1) * y$1 + cnj (x$2) * y$2 + cnj (x$3) * y$3)`,
    REWRITE_TAC[cdot;DIMINDEX_3;VSUM_3]);;
 

(* ------------------------------------------------------------------------- *)
(* RELATION WITH REAL DOT AND CROSS PRODUCTS                                 *)
(* ------------------------------------------------------------------------- *)

let CCROSS_LREAL = prove
  (`!r c.
    (vector_to_cvector r) ccross c =
      vector_to_cvector (r cross (cvector_re c)) 
      + ii % (vector_to_cvector (r cross (cvector_im c)))`,
  REWRITE_TAC[CART_EQ3;CVECTOR_ADD_COMPONENT;CVECTOR_MUL_COMPONENT;
    VECTOR_TO_CVECTOR_COMPONENT;CCROSS_COMPONENT;CROSS_COMPONENTS;
    CVECTOR_RE_COMPONENT;CVECTOR_IM_COMPONENT;complex_mul;RE_CX;IM_CX;CX_DEF;
    complex_sub;complex_neg;complex_add;RE;IM;RE_II;IM_II]
  THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ]
  THEN ARITH_TAC);;

let CCROSS_RREAL = prove
  (`!r c.
    c ccross (vector_to_cvector r) =
      vector_to_cvector ((cvector_re c) cross r)
      + ii % (vector_to_cvector ((cvector_im c) cross r))`,
  REWRITE_TAC[CART_EQ3;CVECTOR_ADD_COMPONENT;CVECTOR_MUL_COMPONENT;
    VECTOR_TO_CVECTOR_COMPONENT;CCROSS_COMPONENT;CROSS_COMPONENTS;
    CVECTOR_RE_COMPONENT;CVECTOR_IM_COMPONENT;complex_mul;RE_CX;IM_CX;CX_DEF;
    complex_sub;complex_neg;complex_add;RE;IM;RE_II;IM_II]
  THEN REPEAT STRIP_TAC THEN AP_TERM_TAC THEN REWRITE_TAC[PAIR_EQ]
  THEN ARITH_TAC);;

let CDOT_LREAL = prove
  (`!r c.
    (vector_to_cvector r) cdot c =
      Cx (r dot (cvector_re c)) + ii * Cx (r dot (cvector_im c))`,
  REWRITE_TAC[cdot; dot; VECTOR_TO_CVECTOR_COMPONENT;CVECTOR_RE_COMPONENT;
    CVECTOR_IM_COMPONENT] THEN REPEAT GEN_TAC
  THEN GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [COMPLEX_EXPAND]
  THEN REWRITE_TAC[MATCH_MP RE_VSUM (SPEC `dimindex (:N)` (GEN_ALL (CONJUNCT1
    (SPEC_ALL (REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
  THEN REWRITE_TAC[MATCH_MP (IM_VSUM) (SPEC `dimindex (:N)` (GEN_ALL
    (CONJUNCT1 (SPEC_ALL (REWRITE_RULE[HAS_SIZE]
      HAS_SIZE_NUMSEG_1)))))]
  THEN REWRITE_TAC[RE_MUL_CX;RE_CNJ;IM_MUL_CX;IM_CNJ;CNJ_CX]
  THEN REWRITE_TAC[COMPLEX_POLY_NEG_CLAUSES] THEN REWRITE_TAC[COMPLEX_MUL_AC]
  THEN REWRITE_TAC[COMPLEX_MUL_ASSOC] THEN REWRITE_TAC[GSYM CX_MUL]
  THEN REWRITE_TAC[GSYM SUM_LMUL]
  THEN REWRITE_TAC[GSYM REAL_NEG_MINUS1;GSYM REAL_MUL_RNEG]);;

let CDOT_RREAL = prove
  (`!r c.
    c cdot (vector_to_cvector r) = 
      Cx ((cvector_re c) dot r) - ii * Cx ((cvector_im c) dot r)`,
  REWRITE_TAC[cdot; dot; VECTOR_TO_CVECTOR_COMPONENT;CVECTOR_RE_COMPONENT;
    CVECTOR_IM_COMPONENT]
  THEN REPEAT GEN_TAC
  THEN GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [COMPLEX_EXPAND]
  THEN REWRITE_TAC[MATCH_MP RE_VSUM (SPEC `dimindex (:N)` (GEN_ALL (CONJUNCT1
    (SPEC_ALL (REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
  THEN REWRITE_TAC[MATCH_MP IM_VSUM (SPEC `dimindex (:N)` (GEN_ALL (CONJUNCT1
    (SPEC_ALL (REWRITE_RULE[HAS_SIZE] HAS_SIZE_NUMSEG_1)))))]
  THEN REWRITE_TAC[RE_MUL_CX;RE_CNJ;IM_MUL_CX;IM_CNJ;GSYM REAL_NEG_LMUL;
  SUM_NEG;CX_NEG;COMPLEX_FIELD `x+y* --z= x-y*z:complex`]);;

let CORTHOGONAL_REAL_CLAUSES = prove
  (`!r c.
    (corthogonal c (vector_to_cvector r)
      <=> orthogonal (cvector_re c) r /\ orthogonal (cvector_im c) r)
    /\ (corthogonal (vector_to_cvector r) c
      <=> orthogonal r (cvector_re c) /\ orthogonal r (cvector_im c))`,
  REWRITE_TAC[corthogonal;orthogonal;CDOT_LREAL;CDOT_RREAL;COMPLEX_SUB_0;
    COMPLEX_EQ;RE_CX;IM_CX;RE_SUB;IM_SUB;RE_ADD;IM_ADD]
  THEN REWRITE_TAC[RE_DEF;CX_DEF;IM_DEF;complex;complex_mul;VECTOR_2;ii]
  THEN CONV_TAC REAL_FIELD);;


(* ------------------------------------------------------------------------- *)
(* NORM, UNIT VECTORS.                                                       *)
(* ------------------------------------------------------------------------- *)

let cnorm2 = new_definition
  `cnorm2 (v:complex^N) = real_of_complex (v cdot v)`;;

let CX_CNORM2 = prove
  (`!v:complex^N. Cx(cnorm2 v) = v cdot v`,
  SIMP_TAC[cnorm2;CDOT_SELF_REAL;REAL_OF_COMPLEX]);;

let CNORM2_CVECTOR_ZERO = prove
  (`cnorm2 (cvector_zero:complex^N) = &0`,
  REWRITE_TAC[cnorm2;CDOT_RZERO;REAL_OF_COMPLEX_CX]);;

let CNORM2_MODULUS = prove
  (`!x:complex^N. cnorm2 x = (vector_map norm x) dot (vector_map norm x)`,
  REWRITE_TAC[cnorm2;cdot;COMPLEX_MUL_CNJ;COMPLEX_POW_2;GSYM CX_MUL;
    VSUM_CX_NUMSEG;dot;VECTOR_MAP_COMPONENT;REAL_OF_COMPLEX_CX]);;

let CNORM2_EQ_0 = prove
  (`!x:complex^N. cnorm2 x = &0 <=> x = cvector_zero`,
  REWRITE_TAC[CNORM2_MODULUS;CX_INJ;DOT_EQ_0] THEN GEN_TAC
  THEN GEN_REWRITE_TAC (RATOR_CONV o DEPTH_CONV) [CART_EQ]
  THEN REWRITE_TAC[VEC_COMPONENT;VECTOR_MAP_COMPONENT;COMPLEX_NORM_ZERO]
  THEN GEN_REWRITE_TAC (RAND_CONV o DEPTH_CONV) [CART_EQ]
  THEN REWRITE_TAC[CVECTOR_ZERO_COMPONENT]);;

let CDOT_EQ_0 = prove
  (`!x:complex^N. x cdot x = Cx(&0) <=> x = cvector_zero`,
  SIMP_TAC[TAUT `(p<=>q) <=> ((p==>q) /\ (q==>p))`;CDOT_LZERO]
  THEN GEN_TAC THEN DISCH_THEN (MP_TAC o MATCH_MP (MESON[REAL_OF_COMPLEX_CX]
    `x = Cx y ==> real_of_complex x = y`))
  THEN REWRITE_TAC[GSYM cnorm2;CNORM2_EQ_0]);;

let CNORM2_POS = prove
  (`!x:complex^N. &0 <= cnorm2 x`, REWRITE_TAC[CNORM2_MODULUS;DOT_POS_LE]);;

let CNORM2_NORM2_2 = prove
  (`!x y:real^N.
    cnorm2 (vector_to_cvector x + ii % vector_to_cvector y) =
      norm x pow 2 + norm y pow 2`,
  REWRITE_TAC[cnorm2;vector_norm;cdot;CVECTOR_ADD_COMPONENT;
    CVECTOR_MUL_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT;CNJ_ADD;CNJ_CX;CNJ_MUL;
    CNJ_II;COMPLEX_ADD_RDISTRIB;COMPLEX_ADD_LDISTRIB;
    SIMPLE_COMPLEX_ARITH
      `(x*x+x*ii*y)+(--ii*y)*x+(--ii*y)*ii*y = x*x-(ii*ii)*y*y`]
  THEN REWRITE_TAC[GSYM COMPLEX_POW_2;COMPLEX_POW_II_2;
    SIMPLE_COMPLEX_ARITH `x-(--Cx(&1))*y = x+y`]
  THEN SIMP_TAC[MESON[CARD_NUMSEG_1;HAS_SIZE_NUMSEG_1;FINITE_HAS_SIZE]
    `FINITE (1..dimindex(:N))`;VSUM_ADD;GSYM CX_POW;VSUM_CX;GSYM dot;
    REAL_POW_2;GSYM dot]
  THEN SIMP_TAC[GSYM CX_ADD;REAL_OF_COMPLEX_CX;GSYM REAL_POW_2;DOT_POS_LE;
    SQRT_POW_2]);;

let CNORM2_NORM2 = prove
  (`!v:complex^N.
    cnorm2 v = norm (cvector_re v) pow 2 + norm (cvector_im v) pow 2`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [GSYM
    VECTOR_TO_CVECTOR_CVECTOR_RE_IM] THEN REWRITE_TAC[CNORM2_NORM2_2]);;

let CNORM2_ALT = prove
  (`!x:complex^N. cnorm2 x = norm (x cdot x)`,
  SIMP_TAC[cnorm2;REAL_OF_COMPLEX_NORM;CDOT_SELF_REAL;EQ_SYM_EQ;REAL_ABS_REFL;
    REWRITE_RULE[cnorm2] CNORM2_POS]);;

let CNORM2_SUB = prove
  (`!x y:complex^N. cnorm2 (x-y) = cnorm2 (y-x)`,
  REWRITE_TAC[cnorm2;CDOT_SUB_LDIST;CDOT_SUB_RDIST] THEN REPEAT GEN_TAC
  THEN AP_TERM_TAC THEN SIMPLE_COMPLEX_ARITH_TAC);;

let CNORM2_VECTOR_TO_CVECTOR = prove
  (`!x:real^N. cnorm2 (vector_to_cvector x) = norm x pow 2`,
  REWRITE_TAC[CNORM2_ALT;CDOT_LREAL;CVECTOR_RE_VECTOR_TO_CVECTOR;
    CVECTOR_IM_VECTOR_TO_CVECTOR;DOT_RZERO;COMPLEX_MUL_RZERO;COMPLEX_ADD_RID;
    DOT_SQUARE_NORM;CX_POW;COMPLEX_NORM_POW;COMPLEX_NORM_CX;REAL_POW2_ABS]);;

let cnorm = new_definition
  `cnorm :complex^N->real = sqrt o cnorm2`;;

overload_interface ("norm",`cnorm:complex^N->real`);;

let CNORM_CVECTOR_ZERO = prove
  (`norm (cvector_zero:complex^N) = &0`,
  REWRITE_TAC[cnorm;CNORM2_CVECTOR_ZERO;o_DEF;SQRT_0]);;

let CNORM_POW_2 = prove
  (`!x:complex^N. norm x pow 2 = cnorm2 x`, 
  SIMP_TAC[cnorm;o_DEF;SQRT_POW_2;CNORM2_POS]);;

let CNORM_NORM_2 = prove
  (`!x y:real^N.
    norm (vector_to_cvector x + ii % vector_to_cvector y) =
      sqrt(norm x pow 2 + norm y pow 2)`,
  REWRITE_TAC[cnorm;o_DEF;CNORM2_NORM2_2]);;

let CNORM_NORM = prove(
  `!v:complex^N.
    norm v = sqrt(norm (cvector_re v) pow 2 + norm (cvector_im v) pow 2)`,
  GEN_TAC THEN GEN_REWRITE_TAC (RATOR_CONV o ONCE_DEPTH_CONV) [GSYM
    VECTOR_TO_CVECTOR_CVECTOR_RE_IM] THEN REWRITE_TAC[CNORM_NORM_2]);;

let CNORM_EQ_0 = prove
  (`!x:complex^N. norm x = &0 <=> x = cvector_zero`,
  SIMP_TAC[cnorm;o_DEF;SQRT_EQ_0;CNORM2_POS;CNORM2_EQ_0]);;

let CNORM_POS = prove
  (`!x:complex^N. &0 <= norm x`,
  SIMP_TAC[cnorm;o_DEF;SQRT_POS_LE;CNORM2_POS]);;

let CNORM_SUB = prove
  (`!x y:complex^N. norm (x-y) = norm (y-x)`,
  REWRITE_TAC[cnorm;o_DEF;CNORM2_SUB]);;

let CNORM_VECTOR_TO_CVECTOR = prove
  (`!x:real^N. norm (vector_to_cvector x) = norm x`,
  SIMP_TAC[cnorm;o_DEF;CNORM2_VECTOR_TO_CVECTOR;POW_2_SQRT;NORM_POS_LE]);;

let CNORM_BASIS = prove
  (`!k. 1 <= k /\ k <= dimindex(:N)
    ==> norm (vector_to_cvector (basis k :real^N)) = &1`,
  SIMP_TAC[NORM_BASIS;CNORM_VECTOR_TO_CVECTOR]);;

let CNORM_BASIS_1 = prove
 (`norm(basis 1:real^N) = &1`,
  SIMP_TAC[NORM_BASIS_1;CNORM_VECTOR_TO_CVECTOR]);;

let CVECTOR_CHOOSE_SIZE = prove
  (`!c. &0 <= c ==> ?x:complex^N. norm(x) = c`,
  MESON_TAC[VECTOR_CHOOSE_SIZE;CNORM_VECTOR_TO_CVECTOR]);;

let cunit = new_definition
  `cunit (X:complex^N) = inv(Cx(norm X))% X`;;

let CUNIT_CVECTOR_ZERO = prove
  (`cunit cvector_zero = cvector_zero:complex^N`, 
  REWRITE_TAC[cunit;CNORM_CVECTOR_ZERO;COMPLEX_INV_0;CVECTOR_SMUL_LZERO]);;

let CDOT_CUNIT_MUL_CUNIT = prove
  (`!x:complex^N. (cunit x cdot x) % cunit x = x`,
  GEN_TAC THEN ASM_CASES_TAC `x = cvector_zero:complex^N`
  THEN ASM_REWRITE_TAC[CUNIT_CVECTOR_ZERO;CDOT_LZERO;CVECTOR_SMUL_LZERO]
  THEN SIMP_TAC[cunit;CVECTOR_SMUL_ASSOC;CDOT_LSMUL;CNJ_INV;CNJ_CX;
    SIMPLE_COMPLEX_ARITH `(x*y)*x=(x*x)*y`;GSYM COMPLEX_INV_MUL;GSYM CX_MUL;
    GSYM REAL_POW_2;cnorm;o_DEF;CNORM2_POS;SQRT_POW_2]
  THEN ASM_SIMP_TAC[cnorm2;REAL_OF_COMPLEX;CDOT_SELF_REAL;CDOT_EQ_0;
    CNORM2_CVECTOR_ZERO;CVECTOR_SMUL_RZERO;CNORM2_EQ_0;COMPLEX_MUL_LINV;
    CVECTOR_SMUL_LID]);;


(* ------------------------------------------------------------------------- *)
(* COLLINEARITY                                                              *)
(* ------------------------------------------------------------------------- *)

(* Definition of collinearity between complex vectors.
 * Note: This is different from collinearity between points (which is the one
 * defined in HOL-Light library)
 *)
let collinear_cvectors = new_definition
  `collinear_cvectors x (y:complex^N) <=> ?a. y = a % x \/ x = a % y`;;

let COLLINEAR_CVECTORS_SYM = prove
  (`!x y:complex^N. collinear_cvectors x y <=> collinear_cvectors y x`,
  REWRITE_TAC[collinear_cvectors] THEN MESON_TAC[]);;

let COLLINEAR_CVECTORS_0 = prove
  (`!x:complex^N. collinear_cvectors x cvector_zero`,
  REWRITE_TAC[collinear_cvectors] THEN GEN_TAC THEN EXISTS_TAC `Cx(&0)`
  THEN REWRITE_TAC[CVECTOR_SMUL_LZERO]);;

let NON_NULL_COLLINEARS = prove
  (`!x y:complex^N.
    collinear_cvectors x y /\ ~(x=cvector_zero) /\ ~(y=cvector_zero)
      ==> ?a. ~(a=Cx(&0)) /\ y = a % x`,
  REWRITE_TAC[collinear_cvectors] THEN REPEAT STRIP_TAC THENL [
    ASM_MESON_TAC[CVECTOR_SMUL_LZERO];
    SUBGOAL_THEN `~(a=Cx(&0))` ASSUME_TAC THENL [
      ASM_MESON_TAC[CVECTOR_SMUL_LZERO];
      EXISTS_TAC `inv a :complex`
      THEN ASM_REWRITE_TAC[COMPLEX_INV_EQ_0;CVECTOR_SMUL_ASSOC]
      THEN ASM_SIMP_TAC[COMPLEX_MUL_LINV;CVECTOR_SMUL_LID]]]);;

let COLLINEAR_LNONNULL = prove(
  `!x y:complex^N.
    collinear_cvectors x y /\ ~(x=cvector_zero) ==> ?a. y = a % x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `y=cvector_zero:complex^N` THENL [
    ASM_REWRITE_TAC[] THEN EXISTS_TAC `Cx(&0)`
    THEN ASM_MESON_TAC[CVECTOR_SMUL_LZERO];
    ASM_MESON_TAC[NON_NULL_COLLINEARS] ]);;

let COLLINEAR_RNONNULL = prove(
  `!x y:complex^N.
    collinear_cvectors x y /\ ~(y=cvector_zero) ==> ?a. x = a % y`,
  MESON_TAC[COLLINEAR_LNONNULL;COLLINEAR_CVECTORS_SYM]);;

let CORTHOGONAL_COLLINEAR_CVECTORS = prove
  (`!x y:complex^N.
    collinear_cvectors x y /\ ~(x=cvector_zero) /\ ~(y=cvector_zero)
      ==> ~(corthogonal x y)`,
  REWRITE_TAC[collinear_cvectors;corthogonal] THEN REPEAT STRIP_TAC
  THEN POP_ASSUM MP_TAC
  THEN ASM_REWRITE_TAC[CDOT_RSMUL;CDOT_LSMUL;COMPLEX_ENTIRE;GSYM cnorm2;
    CDOT_EQ_0;CNJ_EQ_0]
  THEN ASM_MESON_TAC[CVECTOR_SMUL_LZERO]);;

let COMPLEX_BALANCE_DIV_MUL = COMPLEX_FIELD
  `!x y z t. ~(z=Cx(&0)) ==> (x = y/z * t <=> x*z = y * t)`;;

let CCROSS_COLLINEAR_CVECTORS = prove
  (`!x y:complex^3. x ccross y = cvector_zero <=> collinear_cvectors x y`,
  REWRITE_TAC[ccross;collinear_cvectors;CART_EQ3;VECTOR_3;
    CVECTOR_ZERO_COMPONENT;COMPLEX_SUB_0;CVECTOR_MUL_COMPONENT]
  THEN REPEAT GEN_TAC THEN EQ_TAC
  THENL [
    REPEAT (POP_ASSUM MP_TAC) THEN ASM_CASES_TAC `(x:complex^3)$1 = Cx(&0)`
    THENL [
      ASM_CASES_TAC `(x:complex^3)$2 = Cx(&0)` THENL [
        ASM_CASES_TAC `(x:complex^3)$3 = Cx(&0)` THENL [
          REPEAT DISCH_TAC THEN EXISTS_TAC `Cx(&0)`
          THEN ASM_REWRITE_TAC[COMPLEX_POLY_CLAUSES];
          REPEAT STRIP_TAC THEN EXISTS_TAC `(y:complex^3)$3/(x:complex^3)$3`
          THEN ASM_SIMP_TAC[COMPLEX_BALANCE_DIV_MUL]
          THEN ASM_MESON_TAC[COMPLEX_MUL_AC];];
        REPEAT STRIP_TAC THEN EXISTS_TAC `(y:complex^3)$2/(x:complex^3)$2`
        THEN ASM_SIMP_TAC[COMPLEX_BALANCE_DIV_MUL]
        THEN ASM_MESON_TAC[COMPLEX_MUL_AC]; ];
      REPEAT STRIP_TAC THEN EXISTS_TAC `(y:complex^3)$1/(x:complex^3)$1`
      THEN ASM_SIMP_TAC[COMPLEX_BALANCE_DIV_MUL]
      THEN ASM_MESON_TAC[COMPLEX_MUL_AC];];
      SIMPLE_COMPLEX_ARITH_TAC ]);;

let CVECTOR_MUL_INV = prove
  (`!a x y:complex^N. ~(a = Cx(&0)) /\ x = a % y ==> y = inv a % x`,
  REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CVECTOR_SMUL_ASSOC;
    MESON[] `(p\/q) <=> (~p ==> q)`;COMPLEX_MUL_LINV;CVECTOR_SMUL_LID]);;

let CVECTOR_MUL_INV2 = prove
  (`!a x y:complex^N. ~(x = cvector_zero) /\ x = a % y ==> y = inv a % x`,
  REPEAT STRIP_TAC THEN ASM_CASES_TAC `a=Cx(&0)`
  THEN ASM_MESON_TAC[CVECTOR_SMUL_LZERO;CVECTOR_MUL_INV]);;

let COLLINEAR_CVECTORS_VECTOR_TO_CVECTOR = prove
  (`!x y:real^N.
    collinear_cvectors (vector_to_cvector x) (vector_to_cvector y)
      <=> collinear {vec 0,x,y}`,
  REWRITE_TAC[COLLINEAR_LEMMA_ALT;collinear_cvectors]
  THEN REPEAT (STRIP_TAC ORELSE EQ_TAC) THENL [
    POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[CART_EQ]
    THEN REWRITE_TAC[CVECTOR_MUL_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT;
      VECTOR_MUL_COMPONENT;COMPLEX_EQ;RE_CX;RE_MUL_CX]
    THEN REPEAT STRIP_TAC THEN DISJ2_TAC THEN EXISTS_TAC `Re a`
    THEN ASM_SIMP_TAC[];
    REWRITE_TAC[MESON[]`(p\/q) <=> (~p ==> q)`]
    THEN REWRITE_TAC[GSYM VECTOR_TO_CVECTOR_ZERO_EQ]
    THEN DISCH_TAC
    THEN SUBGOAL_TAC "" `vector_to_cvector (y:real^N) =
      inv a % vector_to_cvector x` [ASM_MESON_TAC[CVECTOR_MUL_INV2]]
    THEN POP_ASSUM MP_TAC THEN ONCE_REWRITE_TAC[CART_EQ]
    THEN REWRITE_TAC[CVECTOR_MUL_COMPONENT;VECTOR_TO_CVECTOR_COMPONENT;
      VECTOR_MUL_COMPONENT;COMPLEX_EQ;RE_CX;RE_MUL_CX]
    THEN REPEAT STRIP_TAC THEN EXISTS_TAC `Re(inv a)` THEN ASM_SIMP_TAC[];
    EXISTS_TAC `Cx(&0)` THEN ASM_REWRITE_TAC[VECTOR_TO_CVECTOR_ZERO;
      CVECTOR_SMUL_LZERO];
    ASM_REWRITE_TAC[VECTOR_TO_CVECTOR_MUL] THEN EXISTS_TAC `Cx c`
    THEN REWRITE_TAC[];
  ]);;
