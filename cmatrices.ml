(* ========================================================================= *)
(*                                                                           *)
(*    Matrix operations and derivation of their theorems from cop ones.      *)
(*                                                                           *)
(*   (c) Copyright, Vincent Aravantinos, 2012-2013                           *)
(*                  Hardware Verification Group,                             *)
(*                  Concordia University                                     *)
(*                                                                           *)
(*           Contact: <vincent@ece.concordia.ca>                             *)
(*                                                                           *)
(* ========================================================================= *)


needs "cvectors.ml";;

(* ------------------------------------------------------------------------- *)
(* MATRIX ARITHMETIC DEFINITIONS                                             *)
(* ------------------------------------------------------------------------- *)

make_overloadable "%%" `:A->B->B`;;

let prioritize_cmatrix () =
  overload_interface ("--",`cmatrix_neg:complex^N^M->complex^N^M`);
  overload_interface ("+",`cmatrix_add:complex^N^M->complex^N^M->complex^N^M`);
  overload_interface ("-",`cmatrix_sub:complex^N^M->complex^N^M->complex^N^M`);
  overload_interface ("%%",`cmatrix_smul:complex->complex^N^M->complex^N^M`);
  overload_interface
    ("**",`cmatrix_mul:complex^N^M->complex^P^N->complex^P^M`);;

(* The following definitions can be accessed by prefixing "cmatrix_" to their
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

(* ------------------------------------------------------------------------- *)
(* MATRICES                                                                  *)
(* ------------------------------------------------------------------------- *)

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
   ASM_SIMP_TAC[CFUN_SUM_CLAUSES_NUMSEG;ARITH_RULE `1 <= SUC n`;CFUN_ADD;
     ARITH_RULE `SUC n < j ==> n < j`;COMPLEX_ADD_LID]
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
  CONV_TAC (PATH_CONV "rbrbrl"
    (ONCE_REWRITE_CONV [CFUN_FINITE_BASIS_EXPANSION]))
  THEN IMP_REWRITE_TAC[LINCOP_SUM;FINITE_NUMSEG;o_DEF;LINCOP_SMUL]);;

let COP_OF_CMATRIX_OF_COP = prove
  (`!op:((N)finite_image->complex)->((M)finite_image->complex).
    is_linear_cop op ==> cop_of_cmatrix (cmatrix_of_cop op) = op`,
  REWRITE_TAC[COP_EQ;COP_OF_CMATRIX_CFUN_SUM]
  THEN ONCE_SIMP_TAC[LINCOP_FINITE_BASIS_EXPANSION]
  THEN IMP_REWRITE_TAC[CFUN_SUM_EQ]
  THEN REWRITE_TAC[FUN_EQ_THM;CMATRIX_OF_COP;CFUN_SMUL_THM;finite_index;
    CART_TYBIJ]
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
  REWRITE_TAC[cop_of_cmatrix;cop_mul;COP_EQ;o_THM;CART_TYBIJ;
    CMATRIX_MUL_ASSOC]);;

let VSUM_CXZERO = prove
  (`!s. vsum s (\x. Cx(&0)) = Cx(&0)`,
  REWRITE_TAC[GSYM COMPLEX_VEC_0;VSUM_0]);;

let common_prove t = prove(t,
  SIMP_TAC[cmatrix_defs;cop_of_cmatrix;COP_EQ;COP_TO_CFUN;cfun_defs;
    PULL_DEST_CART;vector_map2;DEST_CART_INJ;COMPLEX_CART_EQ;LAMBDA_BETA;
    cmatrix_cvector_mul;GSYM (CONJS [VSUM_ADD;VSUM_SUB;VSUM_NEG;VSUM_CMUL]);
    FINITE_NUMSEG;cvector_defs;VECTOR_MAP2_COMPONENT;VECTOR_MAP_COMPONENT;
    VECTOR_CONST_COMPONENT;VSUM_CXZERO;COMPLEX_MUL_LZERO;CNJ_VSUM]
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


(* ------------------------------------------------------------------------- *)
(* MATRIX HERMITIANS                                                         *)
(* ------------------------------------------------------------------------- *)

let ctransp = new_definition
  `(ctransp:complex^N^M->complex^M^N) m = lambda i j. m$j$i`;;

let cmatrix_herm = new_definition
  `cmatrix_herm = cmatrix_cnj o ctransp`;;
