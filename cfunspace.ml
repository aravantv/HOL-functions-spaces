(* ========================================================================= *)
(*                                                                           *)
(*   Quantum optics library: algebra prerequisites ("Layer 1").              *)
(*                                                                           *)
(*        (c) Copyright, Mohamed Yousri Mahmoud, Vincent Aravantinos, 2012   *)
(*                       Hardware Verification Group,                        *)
(*                       Concordia University                                *)
(*                                                                           *)
(*           Contact: <mosolim@ece.concordia.ca>, <vincent@ece.concordia.ca> *)
(*                                                                           *)
(* Last update: Jan 23, 2013                                                 *)
(*                                                                           *)
(* TODO:                                                                     *)
(* - reword complex numbers as cfuns in order to factorize the notions of    *)
(*   additions and linear functions                                          *)
(* ========================================================================= *)


(*needs "Multivariate/complexes.ml";;*)
needs "/media/C81B-2C26/Quantum/utils.ml";;

(* ------------------------------------------------------------------------- *)
(* EMBEDDING OF REALS IN COMPLEX NUMBERS                                     *)
(* ------------------------------------------------------------------------- *)

let real_of_complex = new_definition
  `real_of_complex c = @r. c = Cx r`;;

let REAL_OF_COMPLEX = prove
  (`!c. real c ==> Cx(real_of_complex c) = c`,
  MESON_TAC[REAL;real_of_complex]);;

let REAL_OF_COMPLEX_RE = prove
  (`!c. real c ==> real_of_complex c = Re c`,
  MESON_TAC[RE_CX;REAL_OF_COMPLEX]);;

let REAL_OF_COMPLEX_CX = prove
  (`!r. real_of_complex (Cx r) = r`,
  SIMP_TAC[REAL_CX;REAL_OF_COMPLEX_RE;RE_CX]);;

let REAL_OF_COMPLEX_NORM = prove
  (`!c. real c ==> norm c = abs (real_of_complex c)`,
  MP_SIMP_TAC[REAL_NORM;REAL_OF_COMPLEX_RE]);;

let REAL_OF_COMPLEX_ADD = prove
  (`!x y. real x /\ real y ==>
    real_of_complex (x+y) = real_of_complex x + real_of_complex y`,
  MESON_TAC[REAL_ADD;REAL_OF_COMPLEX_RE;RE_ADD]);;

let REAL_MUL = prove
  (`!x y. real x /\ real y ==> real (x*y)`,
  REWRITE_TAC[real] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let REAL_OF_COMPLEX_MUL = prove
  (`!x y. real x /\ real y ==>
    real_of_complex (x*y) = real_of_complex x * real_of_complex y`,
  MESON_TAC[REAL_MUL;REAL_OF_COMPLEX;CX_MUL;REAL_OF_COMPLEX_CX]);;

let NORM2_ADD_REAL = prove
  (`!x y. real x /\ real y ==>
    norm (x + ii * y) pow 2 = norm x pow 2 + norm y pow 2`,
  SIMP_TAC[real;complex_norm;RE_ADD;IM_ADD;RE_MUL_II;IM_MUL_II;REAL_NEG_0;
    REAL_ADD_LID;REAL_ADD_RID;REAL_POW_ZERO;ARITH_RULE `~(2=0)`;REAL_LE_POW_2;
    SQRT_POW_2;REAL_LE_ADD]);;

let real_thms = ref [];;
let add_real_thm thm = real_thms := GIMP_IMP thm :: !real_thms;;
let add_real_thms = List.iter add_real_thm;;

let REAL_TAC ?(alternatives=[]) g =
  let is_meta_variable v = try (fst (dest_var v)).[0] = '_' with _ -> false in
  let contain_meta_variable = can (find_term is_meta_variable) in
  let MATCH_MP_TAC x =
    (fun g -> MATCH_MP_TAC x g) THEN (fun (_,concl as g) ->
      if contain_meta_variable concl then NO_TAC g else ALL_TAC g) in
  let TRY_REAL_THM = ASM (MAP_FIRST (fun x ->
    MATCH_ACCEPT_TAC x ORELSE MATCH_MP_TAC x)) !real_thms in
  let LOOP = TRY_REAL_THM ORELSE (ASM_SIMP_TAC[] THEN NO_TAC)
    ORELSE (CHANGED_TAC (ASM_SIMP_TAC[real]) THEN CONV_TAC COMPLEX_FIELD)
    ORELSE FIRST alternatives in
  (REPEAT STRIP_TAC
  THEN (fun (_,concl as g) ->
    if not (repeat rator concl = `real :complex -> bool`)
    then FAIL_TAC "bad goal" g
    else CHANGED_TAC (REPEAT (LOOP THEN REPEAT CONJ_TAC)) g)) g;;

add_real_thm REAL_MUL;;


(* ------------------------------------------------------------------------- *)
(* MAP OVER FUNCTIONS                                                        *)
(* ------------------------------------------------------------------------- *)

let fun_map = new_definition
  `fun_map (f:B->C) (g:A->B) = \x. f (g x)`;;

(* TODO remove fun_map and use composition instead *)
let FUN_MAP_ALT = prove
  (`fun_map f g = f o g`,
  REWRITE_TAC[fun_map;o_DEF]);;

let FUN_MAP_THM = prove
  (`!f g x. fun_map f g x = f (g x)`,
  REWRITE_TAC[fun_map]);;

let FUN_MAP_LID = prove
  (`!f. fun_map I f = f`,
  REWRITE_TAC[fun_map;I_DEF;ETA_AX]);;

let FUN_MAP_RID = prove
  (`!f. fun_map f I = f`,
  REWRITE_TAC[fun_map;I_DEF;ETA_AX]);;

let FUN_MAP_ID = CONJS [FUN_MAP_LID;FUN_MAP_RID];;

let fun_map2 = new_definition
  `fun_map2 (f:B->C->D) (g1:A->B) (g2:A->C) = \x. f (g1 x) (g2 x)`;;

let FUN_MAP2_THM = prove
  (`!f g1 g2 x. fun_map2 f g1 g2 x = f (g1 x) (g2 x)`,
  REWRITE_TAC[fun_map2]);;

let K_DEF = new_definition
  `K (x:A) = \y:B. x`;;

let K_THM = prove
  (`!x y. K x y = x`,
  REWRITE_TAC[K_DEF]);;

let fun_map_defs = CONJS [K_DEF;fun_map;fun_map2];;

let FUN_MAP_THMS = CONJS [K_THM;FUN_MAP_THM;FUN_MAP2_THM];;


(* --------------------------------------------------------------------------- *)
(* COMPLEX VALUED FUNCTIONS                                                    *)
(* --------------------------------------------------------------------------- *)

new_type_abbrev("cfun",`:A->complex`);;
new_type_abbrev("cfunB",`:B->complex`);;
new_type_abbrev("cfunC",`:C->complex`);;

let cfun_add = new_definition
  `cfun_add:cfun->cfun->cfun = fun_map2 (+)`;;

let cfun_smul = new_definition
  `cfun_smul (a:complex) :cfun->cfun = fun_map (( * ) a)`;;

let cfun_neg = new_definition
  `cfun_neg:cfun->cfun = fun_map (--)`;;

let cfun_sub = new_definition
  `cfun_sub:cfun->cfun->cfun = fun_map2 (-)`;;

let cfun_zero = new_definition
  `cfun_zero:cfun = K (Cx(&0))`;;

let cfun_cnj = new_definition
  `cfun_cnj:cfun->cfun = fun_map cnj`;;

let cfun_defs = CONJS [cfun_add;cfun_sub;cfun_smul;cfun_neg;cfun_cnj;cfun_zero];;

make_overloadable "%" `:A->B->B`;;
parse_as_infix("%",(25,"left"));;

let prioritize_cfun () =
  overload_interface("+",`cfun_add:cfun->cfun->cfun`);
  overload_interface("%",`cfun_smul:complex->cfun->cfun`);
  overload_interface("--",`cfun_neg : cfun->cfun`);
  overload_interface("-",`cfun_sub:cfun->cfun->cfun`);;

prioritize_cfun ();;

(* Intended restriction of FUN_EQ_THM to the type :cfun *)
let CFUN_EQ = prove
  (`!f g:cfun. f = g <=> !x. f x = g x`,
  REWRITE_TAC[FUN_EQ_THM]);;

let CFUN_TO_COMPLEX = CONJS [FUN_MAP_THMS;cfun_defs;CFUN_EQ];;


(* General tactic *)

let CFUN_ARITH_TAC =
  let lemma = MESON[] `(!x. P x <=> Q x) ==> (!x. P x) = (!x. Q x)` in
  REWRITE_TAC[CFUN_TO_COMPLEX]
  THEN (CONV_TAC COMPLEX_FIELD
    ORELSE (REPEAT STRIP_TAC THEN CONV_TAC PRENEX_CONV
      THEN MATCH_MP_TAC lemma THEN CONV_TAC COMPLEX_FIELD));;

let CFUN_ARITH t = prove(t,CFUN_ARITH_TAC);;


(* Properties *)

let CFUN_SUB = CFUN_ARITH `!f g. f - g = \x. f x - g x`;;

let CFUN_SUB_THM = CFUN_ARITH `!f g. (f - g) x = f x - g x`;;

let CFUN_ADD = CFUN_ARITH `!f g. f + g = \x. f x + g x`;;

let CFUN_SMUL = CFUN_ARITH `!a f. a % f = \x. a * f x`;;

let CFUN_NEG_LAMBDA = CFUN_ARITH `!f. --f = \x. --(f x)`;;

let CFUN_SMUL_LNEG = CFUN_ARITH `!a f. (--a) % f = --(a % f)`;;

let CFUN_SMUL_RNEG = CFUN_ARITH `!a f. a % (--f) = --(a % f)`;;

let CFUN_ADD_SYM = CFUN_ARITH `!x y. x + y = y + x`;;

let CFUN_ADD_ASSOC = CFUN_ARITH `!x y z. (x + y) + z = x + y + z`;;

let CFUN_SUB = CFUN_ARITH `!x y. x - y = x + --y`;;

let CFUN_SUB_REFL = CFUN_ARITH `!x. x - x = cfun_zero`;;

let CFUN_SMUL_LZERO = CFUN_ARITH `!x. Cx(&0) % x = cfun_zero`;;

let CFUN_ADD_LID = CFUN_ARITH `!x. cfun_zero + x = x`;;

let CFUN_ADD_RID = CFUN_ARITH `!x. x + cfun_zero = x`;;

let CFUN_SMUL_RZERO = CFUN_ARITH `!a. a % cfun_zero = cfun_zero`;;

let CFUN_ZERO_CLAUSES = 
  CONJS [CFUN_SUB_REFL;CFUN_ADD_RID;CFUN_SMUL_LZERO;CFUN_SMUL_RZERO];;

let CFUN_SMUL_SYM = CFUN_ARITH `!a b x. a % (b % x) = b % (a % x)`;;

let CFUN_SUB_REFL = CFUN_ARITH `!x. x - x = cfun_zero`;;

let CFUN_SMUL_DIS = CFUN_ARITH `!a x y. a % (x + y) = a % x + a % y`;;

let CFUN_ADD_RDISTRIB = CFUN_ARITH `!a b x. (a + b) % x = a % x + b % x`;;

let CFUN_SUB_RDISTRIB = CFUN_ARITH `!a b x. (a - b) % x = a % x - b % x`;;

let CFUN_SUB_RADD = CFUN_ARITH `!x y z. x - (y + z) = x - y - z`;;

let CFUN_ADD_RSUB = CFUN_ARITH `!x y z. x + (y - z) = (x + y) - z`;;

let CFUN_SUB_ADD = CFUN_ARITH `!x y z. (x - y) + z= (x + z) - y`;;

let CFUN_SUB_SUB = CFUN_ARITH `!x y z. x - (y - z) = x - y + z`;;

let CFUN_EQ_LSUB = CFUN_ARITH `!x y z. x - y = z <=> x = z + y`;;

let CFUN_EQ_RSUB = CFUN_ARITH `!x y z. x = y - z <=> x + z = y`;;

let CFUN_ZERO_ADD = CFUN_ARITH `!x y. y + x = x <=> y = cfun_zero`;;

let CFUN_SUB_LDISTRIB = CFUN_ARITH `!a x y. a % (x - y) = a % x - a % y`;;

let CFUN_ADD_LDISTRIB = CFUN_ARITH `!a x y. a % (x + y) = a % x + a % y`;;

let CFUN_SMUL_DISTRIB = CFUN_ARITH `!a b f. a % (b % f) = (a * b) % f`;;

let CFUN_SMUL_LID = CFUN_ARITH `!v. Cx(&1) % v = v`;;

let CFUN_SMUL_LID_NEG = CFUN_ARITH `!v. (--Cx(&1)) % v = --v`;;

let CFUN_EQ_NEG2 = CFUN_ARITH `!x y. --x = --y <=> x = y`;;

let CFUN_EQ_ADD_LCANCEL = CFUN_ARITH `!x y z. x + y = x + z <=> y = z`;;

let CFUN_EQ_ADD_RCANCEL = CFUN_ARITH `!x y z. x + z = y + z <=> x = y`;;

let CFUN_EQ_SUB_LCANCEL = CFUN_ARITH `!x y z. x - y = x - z <=> y = z`;;

let CFUN_EQ_SUB_RADD = CFUN_ARITH `!x y z. x - y = z <=> x = z + y`;;

let CFUN_SUB_ADD2 = CFUN_ARITH `!x y. y + x - y = x`;;

let CFUN_SUB_0 = CFUN_ARITH `!x y. x - y = cfun_zero <=> x = y`;;

let CFUN_ENTIRE = CFUN_ARITH
  `!a x. a % x = cfun_zero <=> a = Cx(&0) \/ x = cfun_zero`;;

let CFUN_EQ_SMUL_LCANCEL = CFUN_ARITH
  `!x y a. a % x = a % y <=> a = Cx(&0) \/ x = y`;;

(* Sub-space *)
let is_cfun_subspace = new_definition 
  `is_cfun_subspace (spc:cfun->bool) <=>
    cfun_zero IN spc
    /\ !x. x IN spc ==> (!a. a % x IN spc) /\ !y. y IN spc ==> x+y IN spc`;;

let CFUN_SUBSPACE_ZERO = prove
  (`!s. is_cfun_subspace s ==> cfun_zero IN s`,
  SIMP_TAC[is_cfun_subspace]);;

let CFUN_SUBSPACE_SMUL = prove
  (`!s a x. is_cfun_subspace s /\ x IN s ==> a%x IN s`,
  SIMP_TAC[is_cfun_subspace]);;

let CFUN_SUBSPACE_ADD = prove
  (`!s x y. is_cfun_subspace s /\ x IN s /\ y IN s ==> x+y IN s`,
  SIMP_TAC[is_cfun_subspace]);;

let CFUN_SUBSPACE_NEG = prove
  (`!s x. is_cfun_subspace s /\ x IN s ==> --x IN s`,
  SIMP_TAC[GSYM CFUN_SMUL_LID_NEG;CFUN_SUBSPACE_SMUL]);;

let CFUN_SUBSPACE_SUB = prove
  (`!s x y. is_cfun_subspace s /\ x IN s /\ y IN s ==> x-y IN s`,
  SIMP_TAC[CFUN_SUB;CFUN_SUBSPACE_NEG;CFUN_SUBSPACE_ADD]);;

let CFUN_SUBSPACE_SING_CFUNZERO = prove
  (`is_cfun_subspace {cfun_zero}`,
  SIMP_TAC[is_cfun_subspace;IN_SING;CFUN_SMUL_RZERO;CFUN_ADD_RID]);;


(* ------------------------------------------------------------------------- *)
(* EMBEDDING COMPLEX NUMBERS IN CFUNS                                        *)
(* ------------------------------------------------------------------------- *)

let SING_IND,SING_REC = define_type "singleton = SING_ELT";;

let SING_EQ = prove
  (`!x. x = SING_ELT`,
  MATCH_MP_TAC SING_IND THEN REFL_TAC);;

let cfun_of_complex = new_definition
  `cfun_of_complex = K :complex->singleton->complex`;;

let CFUN_OF_COMPLEX_ADD = prove
  (`!x y. cfun_of_complex (x+y) = cfun_of_complex x + cfun_of_complex y`,
  REWRITE_TAC[cfun_of_complex] THEN CFUN_ARITH_TAC);;

let CFUN_OF_COMPLEX_SUB = prove
  (`!x y. cfun_of_complex (x-y) = cfun_of_complex x - cfun_of_complex y`,
  REWRITE_TAC[cfun_of_complex] THEN CFUN_ARITH_TAC);;

let CFUN_OF_COMPLEX_NEG = prove
  (`!x. cfun_of_complex (--x) = -- cfun_of_complex x`,
  REWRITE_TAC[cfun_of_complex] THEN CFUN_ARITH_TAC);;

let CFUN_OF_COMPLEX_SMUL = prove
  (`!a x. cfun_of_complex (a*x) = a % cfun_of_complex x`,
  REWRITE_TAC[cfun_of_complex] THEN CFUN_ARITH_TAC);;

let CFUN_OF_COMPLEX_CNJ = prove
  (`!x. cfun_of_complex (cnj x) = cfun_cnj (cfun_of_complex x)`,
  REWRITE_TAC[cfun_of_complex] THEN CFUN_ARITH_TAC);;

let CFUN_OF_COMPLEX_ZERO = prove
  (`cfun_of_complex (Cx(&0)) = cfun_zero`,
  REWRITE_TAC[cfun_of_complex] THEN CFUN_ARITH_TAC);;

let complex_of_cfun = new_definition
  `complex_of_cfun f :complex = f SING_ELT`;;

let COMPLEX_OF_CFUN_ADD = prove
  (`!x y. complex_of_cfun (x + y) = complex_of_cfun x + complex_of_cfun y`,
  REWRITE_TAC[complex_of_cfun] THEN CFUN_ARITH_TAC);;

let COMPLEX_OF_CFUN_SUB = prove
  (`!x y. complex_of_cfun (x - y) = complex_of_cfun x - complex_of_cfun y`,
  REWRITE_TAC[complex_of_cfun] THEN CFUN_ARITH_TAC);;

let COMPLEX_OF_CFUN_NEG = prove
  (`!x. complex_of_cfun (--x) = -- complex_of_cfun x`,
  REWRITE_TAC[complex_of_cfun] THEN CFUN_ARITH_TAC);;

let COMPLEX_OF_CFUN_SMUL = prove
  (`!a x. complex_of_cfun (a % x) = a * complex_of_cfun x`,
  REWRITE_TAC[complex_of_cfun] THEN CFUN_ARITH_TAC);;

let COMPLEX_OF_CFUN_OF_COMPLEX = prove
  (`complex_of_cfun o cfun_of_complex = I`,
  REWRITE_TAC[complex_of_cfun;cfun_of_complex;o_DEF;K_THM;I_DEF]);;

let CFUN_OF_COMPLEX_OF_CFUN = prove
  (`cfun_of_complex o complex_of_cfun = I`,
  REWRITE_TAC[complex_of_cfun;cfun_of_complex;o_DEF;K_DEF;FUN_EQ_THM;I_THM]
  THEN ONCE_REWRITE_TAC[SING_EQ] THEN REWRITE_TAC[]);;


(* ------------------------------------------------------------------------- *)
(* INNER PRODUCT                                                             *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("inprod",`:cfun->cfun->complex`);;

new_type_abbrev("inner_space",`:(cfun->bool)#inprod`);;

let is_inner_space = new_definition
  `is_inner_space ((s,inprod):inner_space) <=>
    is_cfun_subspace s /\
    !x. x IN s ==>
      real (inprod x x) /\ &0 <= real_of_complex (inprod x x)
      /\ (inprod x x = Cx(&0) <=> x = cfun_zero)
      /\ !y. y IN s ==>
        cnj (inprod y x) = inprod x y /\
        (!a. inprod x (a%y) = a * (inprod x y))
        /\ !z. z IN s ==> inprod (x+y) z = inprod x z + inprod y z`;;

(* EVERY THEOREM proved using "inner_space_prove" implicitly has the assumption
 * "!s inprod. is_inner_space (s,inprod) ==>"
 *)
let inner_space_parse s = parse_term ("!s inprod. is_inner_space (s,inprod) ==> " ^ s);;
let inner_space_prove (s,p) = prove(gimp_imp (inner_space_parse s),p);;
let inner_space_g s = g (gimp_imp (inner_space_parse s));;

let full_inner_space_parse s = parse_term ("!is. is_inner_space is ==> " ^ s);;
let full_inner_space_prove (s,p) =
  prove(gimp_imp (full_inner_space_parse s),p);;
let full_inner_space_g s = g (gimp_imp (full_inner_space_parse s));;

let FORALL_INNER_SPACE_THM = prove
  (`!P. (!is:inner_space. P is) <=> !s inprod. P (s,inprod)`,
  REWRITE_TAC[FORALL_PAIR_THM]);;

(* Trivial properties *)

let INNER_SPACE_IS_SUBSPACE = inner_space_prove
  ("is_cfun_subspace s",
  SIMP_TAC[is_inner_space]);;

let INPROD_CNJ = inner_space_prove
  ("!x y. x IN s /\ y IN s ==> cnj(inprod y x) = inprod x y",
  SIMP_TAC[is_inner_space]);;

let INPROD_SELF_REAL = inner_space_prove
  ("!x. x IN s ==> real (inprod x x)",
  SIMP_TAC[is_inner_space]);;

let INPROD_SELF_POS = inner_space_prove
  ("!x. x IN s ==> &0 <= real_of_complex (inprod x x)",
  SIMP_TAC[is_inner_space]);;

let INPROD_RSMUL = inner_space_prove
  ("!x y a. x IN s /\ y IN s ==> inprod x (a%y) = a * inprod x y",
  SIMP_TAC[is_inner_space]);;

let INPROD_ADD_RDIST = inner_space_prove
  ("!x y z. x IN s /\ y IN s /\ z IN s
      ==> inprod (x+y) z = inprod x z + inprod y z",
  SIMP_TAC[is_inner_space]);;

let INPROD_ZERO_EQ = inner_space_prove
  ("!x. x IN s ==> (inprod x x = Cx(&0) <=> x = cfun_zero)",
  SIMP_TAC[is_inner_space]);;

let INPROD_ZERO = inner_space_prove
  ("inprod cfun_zero cfun_zero = Cx(&0)",
  SIMP_TAC[is_inner_space;is_cfun_subspace]);;

let INPROD_NORM = inner_space_prove
  ("!x. x IN s ==> real (inprod x x) /\ &0 <= real_of_complex (inprod x x)",
  SIMP_TAC[is_inner_space]);;

add_real_thm (MESON[INPROD_SELF_REAL]
  `!s inprod x. is_inner_space (s,inprod) /\ x IN s ==> real(inprod x x)`);;

(* More involved properties *)

let INPROD_LSMUL = inner_space_prove
  ("!x y a. x IN s /\ y IN s ==> inprod (a%x) y = cnj a * inprod x y",
  MESON_TAC[is_inner_space;is_cfun_subspace;CNJ_MUL]);;

let INPROD_LNEG = inner_space_prove
  ("!x y. x IN s /\ y IN s ==> inprod (--x) y = --inprod x y",
  MP_SIMP_TAC [GSYM CFUN_SMUL_LID_NEG;INPROD_LSMUL;CNJ_NEG;CNJ_CX;
    COMPLEX_NEG_MINUS1]);;

let INPROD_SUB_RDIST = inner_space_prove
  ("!x y z. x IN s /\ y IN s /\ z IN s ==>
      inprod (x-y) z = inprod x z - inprod y z",
  MP_SIMP_TAC[CFUN_SUB;complex_sub;INPROD_ADD_RDIST;INPROD_LNEG;
    CFUN_SUBSPACE_NEG;INNER_SPACE_IS_SUBSPACE]);;

let INPROD_RNEG = inner_space_prove
  ("!x y. x IN s /\ y IN s ==> inprod x (--y) = --inprod x y",
  MP_SIMP_TAC[GSYM CFUN_SMUL_LID_NEG;INPROD_RSMUL;COMPLEX_NEG_MINUS1]);;

let INPROD_ADD_LDIST = inner_space_prove
  ("!x y z. x IN s /\ y IN s /\ z IN s ==>
      inprod z (x+y) = inprod z x + inprod z y",
  MESON_TAC[INPROD_CNJ;INNER_SPACE_IS_SUBSPACE;CFUN_SUBSPACE_ADD;
    INPROD_ADD_RDIST;CNJ_ADD]);;

let INPROD_SUB_LDIST = inner_space_prove
  ("!x y z. x IN s /\ y IN s /\ z IN s ==>
    inprod z (x-y) = inprod z x - inprod z y",
  MP_SIMP_TAC[CFUN_SUB;complex_sub;INPROD_ADD_LDIST;INPROD_RNEG;
    CFUN_SUBSPACE_NEG;INNER_SPACE_IS_SUBSPACE]);;

let INPROD_RZERO = inner_space_prove
  ("!x. x IN s ==> inprod x cfun_zero = Cx(&0)",
  MP_SIMP_TAC[GSYM CFUN_SMUL_LZERO;INPROD_RSMUL;COMPLEX_MUL_LZERO]);;

let INPROD_LZERO = inner_space_prove
  ("!x. x IN s ==> inprod cfun_zero x = Cx(&0)",
  MP_SIMP_TAC[GSYM CFUN_SMUL_LZERO;INPROD_LSMUL;CNJ_CX;COMPLEX_MUL_LZERO]);;

let INPROD_SELF_CNJ = inner_space_prove
  ("!x. x IN s ==> cnj (inprod x x) = inprod x x",
  SIMP_TAC[GSYM REAL_CNJ;is_inner_space]);;

let INPROD_SELF_NORM = inner_space_prove
  ("!x. x IN s ==> norm (inprod x x) = real_of_complex (inprod x x)",
  MESON_TAC[is_inner_space;REAL_OF_COMPLEX;COMPLEX_NORM_CX;REAL_ABS_REFL]);;

let INPROD_SELF_RE = inner_space_prove
  ("!x. x IN s ==> real_of_complex (inprod x x) = Re (inprod x x)",
  MESON_TAC[is_inner_space;REAL_OF_COMPLEX_RE]);;

(* Surjection holds in finite dimension only *)
let INPROD_INJ = inner_space_prove
  ("!x y. x IN s /\ y IN s ==> (inprod x = inprod y <=> x = y)",
  SIMP_TAC[EQ_TO_IMP] THEN ONCE_MP_SIMP_TAC (GSYM CFUN_SUB_0)
  THEN MP_SIMP_TAC [GSYM INPROD_ZERO_EQ;INPROD_SUB_RDIST;COMPLEX_SUB_0;
    CFUN_SUBSPACE_SUB;INNER_SPACE_IS_SUBSPACE]);;

let INPROD_INJ_ALT = inner_space_prove
  ("!x y. x IN s /\ y IN s
    ==> ((!z. z IN s ==> inprod x z = inprod y z) <=> x = y)",
  SIMP_TAC[EQ_TO_IMP] THEN ONCE_MP_SIMP_TAC (GSYM CFUN_SUB_0)
  THEN MP_SIMP_TAC [GSYM INPROD_ZERO_EQ;INPROD_SUB_RDIST;CFUN_SUBSPACE_SUB;
    INNER_SPACE_IS_SUBSPACE;COMPLEX_SUB_0]
  THEN MESON_TAC [CFUN_SUBSPACE_SUB;INNER_SPACE_IS_SUBSPACE]);;

(* TODO RIESZ *)


(* ------------------------------------------------------------------------- *)
(* ORTHOGONALITY                                                             *)
(* ------------------------------------------------------------------------- *)

let are_orthogonal = new_definition
  `are_orthogonal ((s,inprod):inner_space) u v <=>
    is_inner_space (s,inprod) /\ u IN s /\ v IN s ==> inprod u v = Cx(&0)`;;

let ARE_ORTHOGONAL = inner_space_prove
  ("!u v. u IN s /\ v IN s ==>
      (are_orthogonal (s,inprod) u v <=> inprod u v = Cx(&0))",
  MESON_TAC [are_orthogonal]);;

let ARE_ORTHOGONAL_SYM = inner_space_prove
  ("!u v. u IN s /\ v IN s
      ==> (are_orthogonal (s,inprod) u v <=> are_orthogonal (s,inprod) v u)",
  SIMP_TAC[ARE_ORTHOGONAL] THEN REPEAT (STRIP_TAC ORELSE EQ_TAC)
  THEN ONCE_REWRITE_TAC[GSYM CNJ_INJ] THEN ASM_MESON_TAC[CNJ_CX;INPROD_CNJ]);;

let ARE_ORTHOGONAL_LSCALAR = inner_space_prove
  ("!u v. u IN s /\ v IN s /\ are_orthogonal (s,inprod) u v
      ==> !a. are_orthogonal (s,inprod) (a % u) v",
  MP_SIMP_TAC[are_orthogonal;INPROD_LSMUL;COMPLEX_MUL_RZERO]);;

let ORTHOGONAL_SUM_NORM = inner_space_prove
  ("!u v. u IN s /\ v IN s /\ are_orthogonal (s,inprod) u v ==>
    inprod (u+v) (u+v) = inprod u u + inprod v v",
  MP_SIMP_TAC[are_orthogonal;INPROD_ADD_LDIST;INPROD_ADD_RDIST;
    CFUN_SUBSPACE_ADD;INNER_SPACE_IS_SUBSPACE]
  THEN ONCE_REWRITE_TAC[GSYM COMPLEX_SUB_0]
  THEN (CONV_TAC o DEPTH_CONV o CHANGED_CONV) COMPLEX_POLY_CONV
  THEN MESON_TAC[INPROD_CNJ;CNJ_CX]);;

let ORTHOGONAL_DECOMPOS_WRT_CFUN = inner_space_prove
  ("!u v. u IN s /\ v IN s ==>
      let proj_v = inprod v u / inprod v v in
      let orthogonal_component = u - proj_v % v in
      u = proj_v % v + orthogonal_component
      /\ are_orthogonal (s,inprod) v orthogonal_component",
  REWRITE_TAC[LET_DEF;LET_END_DEF;CFUN_SUB_ADD2;are_orthogonal]
  THEN MP_SIMP_TAC [INPROD_SUB_LDIST;INPROD_RSMUL;CFUN_SUBSPACE_SMUL;
    INNER_SPACE_IS_SUBSPACE]
  THEN REPEAT STRIP_TAC THEN Pa.ASM_CASES_TAC "v=cfun_zero" THENL [
    ASM_MP_SIMP_TAC [CFUN_SMUL_RZERO;INPROD_LZERO;CFUN_SUBSPACE_ZERO;
    INNER_SPACE_IS_SUBSPACE];
    MP_SIMP_TAC [COMPLEX_DIV_RMUL;INPROD_ZERO_EQ]
  ] THEN SIMPLE_COMPLEX_ARITH_TAC);;

let ORTHOGONAL_DECOMPOS_WRT_CFUN_DECOMPOSITION = inner_space_prove
  ("!u v. u IN s /\ v IN s ==>
      let proj_v = inprod v u / inprod v v in
      let orthogonal_component = u - proj_v % v in
      u = proj_v % v + orthogonal_component",
  let LET_DEFs = [LET_DEF;LET_END_DEF] in
  REWRITE_TAC LET_DEFs
  THEN MESON_TAC[REWRITE_RULE LET_DEFs ORTHOGONAL_DECOMPOS_WRT_CFUN]);;

let ORTHOGONAL_DECOMPOS_WRT_CFUN_ORTHOGONAL = inner_space_prove
  ("!u v. u IN s /\ v IN s ==>
      are_orthogonal (s,inprod) v (u - (inprod v u / inprod v v) % v)",
  let LET_DEFs = [LET_DEF;LET_END_DEF] in
  REWRITE_TAC LET_DEFs
  THEN MESON_TAC[REWRITE_RULE LET_DEFs ORTHOGONAL_DECOMPOS_WRT_CFUN]);;

(* ICI *)
let SCHWARZ_INEQUALITY = inner_space_prove 
  ("!x y. x IN s /\ y IN s
      ==> norm (inprod x y) pow 2
        <= real_of_complex (inprod x x) * real_of_complex (inprod y y)",
  ONCE_MP_SIMP_TAC INPROD_SELF_RE THEN ONCE_MP_SIMP_TAC (GSYM INPROD_SELF_NORM)
  THEN REWRITE_TAC[MATCH_MP (TAUT `(A ==> B) ==> ((A ==> C) <=> (A /\ B ==>
    C))`) (SPEC_ALL (REWRITE_RULE [LET_DEF;LET_END_DEF] ORTHOGONAL_DECOMPOS_WRT_CFUN))
  THEN FIRST_X_ASSUM (wrap (CHANGED_TAC o GEN_REWRITE_TAC (PATH_CONV "rl" o
    ONCE_DEPTH_CONV)))
  THEN MP_REWRITE_TAC [ORTHOGONAL_SUM_NORM;ARE_ORTHOGONAL_LSCALAR;
    CFUN_SUBSPACE_SUB;INPROD_RSMUL;CFUN_SUBSPACE_SMUL;INNER_SPACE_IS_SUBSPACE;
    INPROD_LSMUL]
  THEN REWRITE_TAC[complex_div;CNJ_MUL;CNJ_INV]
  THEN GEN_MP_REWR_TAC rand INPROD_SELF_NORM
  THEN REWRITE_TAC[GSYM RE_MUL_CX]
  THEN MP_REWRITE_TAC [REAL_OF_COMPLEX;INPROD_SELF_REAL;
    MATCH_TRANS INPROD_SELF_CNJ (MESON[] `x=y ==> inv x = inv y`)]
  THEN REWRITE_TAC[COMPLEX_ADD_RDISTRIB;
    Pa.COMPLEX_FIELD "((x*y)*(z*t)*u)*v = (x*z)*(u*t)*(v*y)";
    ONCE_REWRITE_RULE[GSYM COMPLEX_NORM_CNJ] COMPLEX_MUL_CNJ]
  THEN CASES_REWRITE_TAC COMPLEX_MUL_RINV
  THENL [
    MP_REWRITE_TAC [INPROD_CNJ]
    THEN REWRITE_TAC[RE_ADD;RE_CX;COMPLEX_MUL_RID;GSYM CX_POW;REAL_LE_ADDR]
    THEN MP_REWRITE_TAC [GSYM REAL_OF_COMPLEX_RE;REAL_OF_COMPLEX_MUL;
      REAL_LE_MUL;INPROD_SELF_POS;INPROD_SELF_POS;CFUN_SUBSPACE_SUB;
      CFUN_SUBSPACE_SMUL;INNER_SPACE_IS_SUBSPACE ]
    THEN REAL_TAC THEN HINT_EXISTS_TAC
    THEN MP_REWRITE_TAC
      [CFUN_SUBSPACE_SUB;CFUN_SUBSPACE_SMUL;INNER_SPACE_IS_SUBSPACE];
    ASM_REWRITE_TAC[]
    THEN CONV_TAC (DEPTH_CONV (CHANGED_CONV COMPLEX_POLY_CONV))
    THEN POP_ASSUM MP_TAC THEN MP_REWR_TAC INPROD_ZERO_EQ
    THEN SIMP_TAC[] THEN MP_REWRITE_TAC [INPROD_RZERO]
    THEN REWRITE_TAC[COMPLEX_NORM_0;RE_CX] THEN ARITH_TAC
  ]);;

let SCHWARZ_INEQUALITY_ENHANCED = inner_space_prove 
  ("!x y. x IN s /\ y IN s ==>
      real_of_complex ((inprod x y - inprod y x) / (Cx(&2) * ii)) pow 2
        <= real_of_complex (inprod x x) * real_of_complex (inprod y y)",
  REPEAT STRIP_TAC
  THEN MP_REWRITE_TAC [MATCH_MP (MESON[REAL_LE_TRANS]
    `!f g. (P ==> f x y <= g x y) ==> P /\ z <= f x y ==> z <= g x y`)
    (SPEC_ALL SCHWARZ_INEQUALITY);
    MATCH_MP (REAL_ARITH `x=y+z ==> &0<=y /\ t=z ==> t<=x`) COMPLEX_SQNORM]
  THEN REWRITE_TAC[REAL_LE_POW_2]
  THEN MATCH_MP_TAC (MESON[] `(x:real) = y ==> x pow 2 = y pow 2`)
  THEN ONCE_REWRITE_TAC[GSYM CX_INJ]
  THEN REWRITE_TAC[CX_IM_CNJ;GSYM COMPLEX_INV_II;complex_div;COMPLEX_INV_MUL]
  THEN MP_REWRITE_TAC [INPROD_CNJ;REAL_OF_COMPLEX]
  THEN REWRITE_TAC[SIMPLE_COMPLEX_ARITH `x*y*inv ii=inv ii*(x*y)`;
    COMPLEX_INV_II;GSYM complex_div]
  THEN GEN_MP_REWR_TAC (follow_path "rrlrr") (GSYM INPROD_CNJ)
  THEN REWRITE_TAC[GSYM CX_IM_CNJ;REAL_CX]);;


(* ------------------------------------------------------------------------- *)
(* OPERATORS                                                                 *)
(* ------------------------------------------------------------------------- *)

(* "cop" stands for "Complex-valued function OPerator" *)
new_type_abbrev ("cop",`:cfunB->cfun`);;
new_type_abbrev ("copB",`:cfunC->cfunB`);;

let cop_add = new_definition
  `cop_add:cop->cop->cop = fun_map2 (+)`;;

let cop_sub = new_definition
  `cop_sub:cop->cop->cop = fun_map2 (-)`;;

let cop_neg = new_definition
  `cop_neg:cop->cop = fun_map (--)`;;

let cop_mul = new_definition
  `cop_mul:cop->copB->(cfunC->cfun) = fun_map`;;

let cop_smul = new_definition
  `cop_smul:complex->cop->cop = fun_map o (%)`;;

let cop_zero = new_definition
  `cop_zero:cop = K cfun_zero`;;

let cop_pow = define
  `cop_pow (op:cfun->cfun) 0 = I /\
  cop_pow op (SUC n) = cop_mul op (cop_pow op n)`;;

let cop_cnj = new_definition
  `cop_cnj:cop->cop = fun_map cfun_cnj`;;

let cop_defs = CONJS
  [cop_add;cop_sub;cop_neg;cop_mul;cop_smul;cop_zero;I_THM;cop_pow;cop_cnj];;

let prioritize_cop () =
  overload_interface("+",`cop_add:cop->cop->cop`);
  overload_interface("-",`cop_sub:cop->cop->cop`);
  overload_interface("--",`cop_neg:cop->cop`);
  overload_interface("**",`cop_mul:cop->copB->(cfunC->cfun)`);
  overload_interface("pow",`cop_pow:(cfun->cfun)->num->(cfun->cfun)`);
  overload_interface("%",`cop_smul:complex->cop->cop`);;

prioritize_cop ();;

(* Intended restriction of FUN_EQ_THM to the type :cop *)
let COP_EQ = prove
  (`!f g:cop. f = g <=> (!x. f x = g x)`,
  REWRITE_TAC[FUN_EQ_THM]);;

let COP_TO_CFUN = CONJS [FUN_MAP_THMS;o_THM;cop_defs;COP_EQ];;

let COP_POW_CONV =
  let th = REWRITE_CONV[cop_pow;cop_mul;FUN_MAP_RID] `cop_pow t (SUC 0)` in
  fun t ->
    let (h,_) = strip_comb t in
    if name_of h = "cop_pow"
    then (CHANGED_CONV (RAND_CONV (REDEPTH_CONV num_CONV)
      THENC REWRITE_CONV[cop_pow;th])) t
    else failwith "COP_POW_CONV";;

let COP_ARITH_TAC =
  let lemma = MESON[] `(!x. P x <=> Q x) ==> (!x. P x) = (!x. Q x)` in
  CONV_TAC (TOP_DEPTH_CONV COP_POW_CONV)
  THEN REWRITE_TAC[COP_TO_CFUN]
  THEN (CFUN_ARITH_TAC
    ORELSE (REPEAT STRIP_TAC THEN CONV_TAC PRENEX_CONV
      THEN MATCH_MP_TAC lemma THEN CFUN_ARITH_TAC));;

let COP_ARITH t = prove(t,COP_ARITH_TAC);;

(* Properties *)

let COP_SMUL = COP_ARITH `!a op. a % op = \x. a * op x`;;

let COP_SMUL_THM = COP_ARITH `!a op x. (a % op) x = a % op x`;;

let COP_MUL = COP_ARITH `!op1 op2. op1 ** op2 = \x. op1 (op2 x)`;;

let COP_ADD = COP_ARITH `!op1 op2. op1 + op2 = \x. op1 x + op2 x`;;

let COP_SUB_THM = COP_ARITH `!op1 op2 x. (op1 - op2) x = op1 x - op2 x`;;

let COP_ZERO_THM = COP_ARITH `cop_zero x = cfun_zero`;;

let COP_MUL_LID = COP_ARITH `!op. I ** op = op`;;

let COP_MUL_RID = COP_ARITH `!op. op ** I = op`;;

let COP_I_ID = CONJ COP_MUL_LID COP_MUL_RID;;

let COP_MUL_I_SYM = COP_ARITH `!op. op ** I = I ** op`;;

let COP_SMUL = COP_ARITH `!a op. a % op = \x. a % op x`;;

let COP_MUL_THM = COP_ARITH `!x op1 op2. (op1 ** op2) x = op1 (op2 x)`;;

let COP_SMUL_LNEG = COP_ARITH `!a op. --a % op = --(a % op)`;;

let COP_SMUL_RNEG = COP_ARITH `!a op. a % --op = --(a % op)`;;

let COP_SUB = COP_ARITH `!op1 op2. op1 - op2 = op1 + --op2`;;

let COP_NEG_NEG = COP_ARITH `!op. --(--op) = op`;;

let COP_NEG_ADD = COP_ARITH `!op1 op2. --(op1 + op2) = --op1 + --op2`;;

let COP_NEG_SUB = COP_ARITH `!op1 op2. --(op1 - op2) = --op1 + op2`;;

let COP_NEG_CLAUSES = CONJS [COP_NEG_NEG;COP_NEG_ADD;COP_NEG_SUB;COP_SUB];;

let COP_SMUL_ASSOC = COP_ARITH `!a b op. a % (b % op) = (a * b) % op`;;

let COP_SMUL_SYM = COP_ARITH `!a b op. a % (b % op) = b % (a % op)`;;

let COP_MUL_LSMUL = COP_ARITH `!op1 op2. a % op1 ** op2 = a % (op1 ** op2)`;;

let COP_ADD_SYM = COP_ARITH `!op1 op2. op1 + op2 = op2 + op1 `;;

let COP_ADD_ASSOC = COP_ARITH 
  `!op1 op2 op3. (op1 + op2) + op3  = op1 + op2 + op3 `;;

let COP_ADD_LDISTRIB = COP_ARITH 
  `!a op1 op2. a % (op1 + op2) = a % op1 + a % op2`;;

let COP_ADD_RDISTRIB = COP_ARITH `!a b op. (a + b) % op = a % op + b % op`;;

let COP_SMUL_INV_ID = COP_ARITH
  `!a op. ~(a = Cx (&0)) ==> a % (inv a % op) = op`;;

let COP_SUB_LDISTRIB = COP_ARITH `!a x y. a % (x - y) = a % x - a % y`;;

let COP_SUB_RADD = COP_ARITH `!x y z. x - (y + z) = x - y - z`;;

let COP_ADD_RSUB = COP_ARITH `!x y z. x + (y - z) = (x + y) - z`;;

let COP_SUB_SUB = COP_ARITH `!x y z. x - (y - z) = x - y + z`;;

let COP_ADD_RID = COP_ARITH `!x. x + cop_zero = x`;;

let COP_ADD_LID = COP_ARITH `!x. cop_zero + x = x`;;

let COP_ADD_SYM = COP_ARITH `!op1 op2. op1 + op2 = op2 + op1`;;

let COP_ADD_ASSOC = COP_ARITH `!x y z. (x + y) + z = x + y + z`;;

let COP_ADD_AC = COP_ARITH
  `!m n p. m + n = n + m /\ (m + n) + p = m + n + p /\ m + n + p = n + m + p`;;

let COP_MUL_ASSOC = COP_ARITH `!x y z . (x ** y) ** z = x ** y ** z`;;

let COP_SUB_REFL = COP_ARITH `!x. x - x = cop_zero`;;

let COP_SUB_ADD = COP_ARITH `!x y z. (x-y)+z= (x+z)-y`;;

let COP_NEG_INJ = COP_ARITH `!x y. --x = --y <=> x = y`;;

let COP_EQ_ADD_LCANCEL = COP_ARITH `!x y z. x + y = x + z <=> y=z`;;

let COP_EQ_ADD_RCANCEL = COP_ARITH `!x y z. x + z = y + z <=> x=y`;;

let COP_EQ_SUB_LCANCEL = COP_ARITH `!x y z. x - y = x - z <=> y=z`;;

let COP_EQ_LSUB = COP_ARITH `!x y z. x - y = z <=> x = z + y`;;

let COP_EQ_RSUB = COP_ARITH `!x y z. x = y - z <=> x + z = y`;;

let COP_MUL_LZERO = COP_ARITH `!op. cop_zero ** op = cop_zero`;;

let COP_SUB_REFL = COP_ARITH `!op. op - op = cop_zero`;;

let COP_SMUL_LID_NEG = COP_ARITH `!x. (--Cx(&1)) % x = --x`;;

let COP_ADD_RID = COP_ARITH `!op. op + cop_zero = op`;;

let COP_ADD_LID = COP_ARITH `!op. cop_zero + op = op`;;

let COP_SMUL_LID = COP_ARITH `!op. Cx(&1) % op = op`;;

let COP_SMUL_RZERO = COP_ARITH `!op. a % cop_zero = cop_zero`;;

let COP_SUB_LZERO = COP_ARITH `!op. cop_zero - op = --op`;;

let COP_ZERO_CLAUSES = CONJS
  [COP_MUL_LZERO;COP_SUB_REFL;COP_ADD_RID;COP_ADD_LID;COP_SMUL_RZERO];;

let COP_ADD_MUL_RDISTRIB =
  COP_ARITH `!op1 op2 op3. (op1 + op2) ** op3 = op1 ** op3 + op2 ** op3`;;

let COP_SUB_MUL_RDISTRIB =
  COP_ARITH `!op1 op2 op3. (op1 - op2) ** op3 = op1 ** op3 - op2 ** op3`;;

let COP_EQ_LSUB_LSUB = COP_ARITH `!x y z. x - y = z <=> x - z = y`;;


(* ------------------------------------------------------------------------- *)
(* LINEAR OPERATORS                                                          *)
(* ------------------------------------------------------------------------- *)

let is_linear_cop = new_definition
  `is_linear_cop (op:cop) <=>
    !x y. op (x + y) = op x + op y /\ !a. op (a % x) = a % (op x)`;;

let LINCOP_ADD = prove
  (`!x y op. is_linear_cop op ==> op (x + y) = op x + op y`, 
  SIMP_TAC[is_linear_cop]);;

let LINCOP_SMUL = prove
  (`!a x op. is_linear_cop op ==> op (a % x) = a % op x`, 
  SIMP_TAC[is_linear_cop]);;

let LINCOP_SUB = prove
  (`!x y op. is_linear_cop op ==> op (x - y) = op x - op y`, 
  SIMP_TAC[is_linear_cop;CFUN_SUB;GSYM CFUN_SMUL_LID_NEG]);;

let LINCOP_MUL_RSMUL = prove
  (`!a op1 op2. is_linear_cop op2 ==> op2 ** (a % op1) = a % (op2 ** op1)`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN]);;

let LINCOP_SMUL_CLAUSES = CONJS [LINCOP_MUL_RSMUL;COP_ADD_LDISTRIB;
  COP_SUB_LDISTRIB;COP_MUL_LSMUL;COP_MUL_ASSOC;COP_MUL_LID];;

let LINCOP_MUL_RMUL = prove
  (`!op1 op2. is_linear_cop op2 ==> op2 ** (a % op1) = a % (op2 ** op1)`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN]);;

let LINCOP_ADD_MUL_LDISTRIB = prove
  (`!op1 op2 op3. is_linear_cop op3 ==>
      op3 ** (op1 + op2) = op3 ** op1 + op3 ** op2`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN]);;

let LINCOP_SUB_MUL_LDISTRIB = prove
  (`!op1 op2 op3. is_linear_cop op3 ==>
      op3 ** (op1 - op2) = op3 ** op1 - op3 ** op2`, 
  SIMP_TAC[is_linear_cop;COP_TO_CFUN;LINCOP_SUB]);;

let LINCOP_MUL_DISTRIB_CLAUSES =
  CONJS[COP_ADD_MUL_RDISTRIB;COP_SUB_MUL_RDISTRIB;LINCOP_ADD_MUL_LDISTRIB;
    LINCOP_SUB_MUL_LDISTRIB];;

let LINCOP_CFUN_ZERO = prove
  (`!op. is_linear_cop op ==> op cfun_zero = cfun_zero`,
  MESON_TAC[is_linear_cop;CFUN_SMUL_LZERO]);;

let COP_POW_SMUL = prove
  (`!op. is_linear_cop op ==> !n a. (a % op) pow n = (a pow n) % (op pow n)`,
  REWRITE_TAC[is_linear_cop] THEN REPEAT (INDUCT_TAC ORELSE STRIP_TAC)
  THEN ASM_REWRITE_TAC[COP_TO_CFUN;complex_pow] THEN CFUN_ARITH_TAC);;


(* Congruence properties *)

let ADD_LINCOP = prove
  (`!op1 op2.
    is_linear_cop op1 /\ is_linear_cop op2 ==> is_linear_cop (op1 + op2)`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN] THEN REPEAT STRIP_TAC
  THEN COP_ARITH_TAC);;

let SUB_LINCOP = prove
  (`!op1 op2.
    is_linear_cop op1 /\ is_linear_cop op2 ==> is_linear_cop (op1 - op2)`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN] THEN REPEAT STRIP_TAC
  THEN COP_ARITH_TAC);;

let SMUL_LINCOP = prove
  (`!a op. is_linear_cop op ==> is_linear_cop (a % op)`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN] THEN REPEAT STRIP_TAC
  THEN COP_ARITH_TAC);;

let MUL_LINCOP = prove
  (`!op1 op2.
    is_linear_cop op1 /\ is_linear_cop op2 ==> is_linear_cop (op1 ** op2)`,
  SIMP_TAC[is_linear_cop;COP_TO_CFUN] THEN REPEAT STRIP_TAC
  THEN COP_ARITH_TAC);;

let ARITH_LINCOP_CLAUSES = CONJS
  [ADD_LINCOP;SUB_LINCOP;SMUL_LINCOP;MUL_LINCOP];;

let linearity_thms = ref [];;
let add_linearity_thm thm =
  let thm = GIMP_IMP thm in
  linearity_thms := thm :: !linearity_thms;
  let eta_thm = SIMP_RULE[ETA_AX] thm in
  if (not (equals_thm thm eta_thm))
  then linearity_thms := eta_thm :: !linearity_thms;;
let add_linearity_thms = List.iter add_linearity_thm;;

add_linearity_thms [ADD_LINCOP;SUB_LINCOP;SMUL_LINCOP;MUL_LINCOP;
  REWRITE_RULE[cop_smul] SMUL_LINCOP];;

let I_LINCOP = prove
  (`is_linear_cop I`,
  REWRITE_TAC[is_linear_cop;I_DEF]);;

add_linearity_thms [I_LINCOP;REWRITE_RULE[I_DEF] I_LINCOP];;

let ZERO_LINCOP = prove
  (`is_linear_cop cop_zero`, 
  REWRITE_TAC[is_linear_cop;COP_ZERO_THM] THEN COP_ARITH_TAC);;

add_linearity_thms [ZERO_LINCOP];;

let LINEARITY_TAC g =
  let MATCH_MP_TAC x y = MATCH_MP_TAC x y in
  let TRY_LINEARITY_THM = ASM (MAP_FIRST (fun x ->
    MATCH_ACCEPT_TAC x ORELSE MATCH_MP_TAC x)) !linearity_thms in
  let LOOP = TRY_LINEARITY_THM ORELSE (SIMP_TAC[ETA_AX] THEN TRY_LINEARITY_THM)
    ORELSE (ASM_SIMP_TAC[] THEN NO_TAC) in
  (REPEAT STRIP_TAC THEN CHANGED_TAC (REPEAT (LOOP THEN REPEAT CONJ_TAC))) g;;


(* ------------------------------------------------------------------------- *)
(* DUAL SPACE                                                                *)
(* ------------------------------------------------------------------------- *)

new_type_abbrev("cfun_dual",`:cfun->complex`);;
new_type_abbrev("cfun_dualB",`:cfunB->complex`);;

(* Note that all the above operations still apply on the dual space since
 * `:cfun_dual` is an instance of `cfun` itself.
 *)

let cfun_dual = new_definition
  `cfun_dual (spc:cfun->bool) =
    { f:cfun->complex | is_linear_cop (cfun_of_complex o f) }`;;

(*
 *let cfun_topological_dual = new_definition
 *  `cfun_topological_dual spc =
 *    { f | f IN cfun_dual spc /\ !x. f continuous (within (:cfun)) }`;;
 *)

let cop_transpose = new_definition
  `cop_transpose (f:cop) :cfun_dual->cfun_dualB = \phi. phi o f`;;


(* ------------------------------------------------------------------------- *)
(* FREQUENTLY USED OPERATORS                                                 *)
(* ------------------------------------------------------------------------- *)

let commutator = new_definition
  `commutator (op1:cfun->cfun) op2 = op1 ** op2 - op2 ** op1`;;

let COMMUTATOR_NEG = prove
  (`!op1 op2. commutator op1 op2 = -- commutator op2 op1`,
  REWRITE_TAC[commutator] THEN COP_ARITH_TAC);;

let LINCOP_COMMUTATOR = prove
  (`!op1 op2. is_linear_cop op1 /\ is_linear_cop op2
    ==> is_linear_cop (commutator op1 op2)`,
  REWRITE_TAC[commutator] THEN REPEAT STRIP_TAC THEN LINEARITY_TAC);;

add_linearity_thm LINCOP_COMMUTATOR;;

let expectation = new_definition
  `expectation (inprod:inprod) f op = inprod f (op f)`;;  

let deviation = new_definition
  `deviation (inprod:inprod) f op = op - (\x. expectation inprod f op % x)`;;

let DEVIATION_ALT = prove
  (`!inprod f op. deviation inprod f op = op - expectation inprod f op % I`,
  REWRITE_TAC[deviation] THEN COP_ARITH_TAC);;

let LINCOP_DEVIATION = prove
  (`!inprod state op. is_linear_cop op
    ==> is_linear_cop (deviation inprod state op)`,
    REWRITE_TAC[deviation;GSYM COP_SMUL] THEN LINEARITY_TAC);;

add_linearity_thm LINCOP_DEVIATION;;

let variance = new_definition
  `variance  (inprod:inprod) f op = 
    expectation inprod f (deviation inprod f op ** deviation inprod f op)`;;  

let DEVIATION_COMMUTATOR = prove
  (`!inprod op1 op2 state. is_linear_cop op1 /\ is_linear_cop op2
    ==> commutator (deviation inprod state op1) (deviation inprod state op2)
      = commutator op1 op2`,
  SIMP_TAC[DEVIATION_ALT;commutator] THEN REPEAT STRIP_TAC
  THEN REPEAT (MP_REWRITE_TAC [LINCOP_SUB_MUL_LDISTRIB] THEN CONJ_TAC)
  THEN TRY LINEARITY_TAC
  THEN ASM_SIMP_TAC[LINCOP_MUL_DISTRIB_CLAUSES;COP_MUL_LSMUL;COP_I_ID;
    LINCOP_MUL_RMUL;MESON[COP_SMUL_SYM]
      `f (a % (b % op)) (b % (a % op)) = f (a % (b % op)) (a % (b % op))`]
  THEN COP_ARITH_TAC);;

let EXPEC_ZERO_STATE = prove
  (`!s inprod op. is_linear_cop op /\ is_inner_space (s,inprod)
    ==> expectation inprod cfun_zero op = Cx(&0)`,
  MESON_TAC[expectation;INPROD_ZERO;LINCOP_CFUN_ZERO]);;


(* ------------------------------------------------------------------------- *)
(* CLOSURE                                                                   *)
(* ------------------------------------------------------------------------- *)

let is_closed_by = new_definition
  `is_closed_by s f <=> !x. x IN s ==> f x IN s`;;

let IS_CLOSED_BY_COMPOSE = prove
  (`!s f g. is_closed_by s f /\ is_closed_by s g ==> is_closed_by s (f o g)`,
  REWRITE_TAC[is_closed_by;o_DEF] THEN MESON_TAC[]);;

let IS_CLOSED_BY_I = prove
  (`!s. is_closed_by s I`,
  REWRITE_TAC[is_closed_by;I_THM]);;

let IS_CLOSED_BY_COP_ADD = prove
  (`!s op1 op2.
      is_cfun_subspace s /\ is_closed_by s op1 /\ is_closed_by s op2
        ==> is_closed_by s (op1+op2)`,
  REWRITE_TAC[is_closed_by;COP_TO_CFUN] THEN MESON_TAC[CFUN_SUBSPACE_ADD]);;

let IS_CLOSED_BY_COP_SUB = prove
  (`!s op1 op2.
      is_cfun_subspace s /\ is_closed_by s op1 /\ is_closed_by s op2
        ==> is_closed_by s (op1-op2)`,
  REWRITE_TAC[is_closed_by;COP_TO_CFUN] THEN MESON_TAC[CFUN_SUBSPACE_SUB]);;

let IS_CLOSED_BY_COP_MUL = prove
  (`!s op1 op2.
      is_closed_by s op1 /\ is_closed_by s op2 ==> is_closed_by s (op1**op2)`,
  REWRITE_TAC[is_closed_by;COP_TO_CFUN] THEN MESON_TAC[]);;

let IS_CLOSED_BY_COP_SMUL = prove
  (`!s a op.
      is_cfun_subspace s /\ is_closed_by s op ==> is_closed_by s (a % op)`,
  REWRITE_TAC[is_closed_by;COP_TO_CFUN] THEN MESON_TAC[CFUN_SUBSPACE_SMUL]);;

let IS_CLOSED_BY_COMMUTATOR = prove
  (`!s a op.
      is_cfun_subspace s /\ is_closed_by s op1 /\ is_closed_by s op2
        ==> is_closed_by s (commutator op1 op2)`,
  REWRITE_TAC[commutator] 
  THEN MESON_TAC[IS_CLOSED_BY_COP_MUL;IS_CLOSED_BY_COP_SUB]);;

(* ------------------------------------------------------------------------- *)
(* HERMITIAN                                                                 *)
(* ------------------------------------------------------------------------- *)

let is_hermitian = new_definition
  `is_hermitian ((s,inprod):inner_space) op1 op2 <=>
    is_inner_space (s,inprod) ==>
      is_closed_by s op1 /\ is_closed_by s op2
      /\ is_linear_cop op1 /\ is_linear_cop op2
      /\ !x y. x IN s /\ y IN s ==> inprod x (op1 y) = inprod (op2 x) y`;;

let LINCOP_LHERM = full_inner_space_prove
  ("!op1 op2. is_hermitian is op1 op2 ==> is_linear_cop op1",
  SIMP_TAC[FORALL_INNER_SPACE_THM;is_hermitian]);;

let LINCOP_RHERM = full_inner_space_prove
  ("!op1 op2. is_hermitian is op1 op2 ==> is_linear_cop op2",
  SIMP_TAC[FORALL_INNER_SPACE_THM;is_hermitian]);;

let ADD_HERM = full_inner_space_prove
  ("!op1 op2 op3 op4.
    is_hermitian is op1 op2 /\ is_hermitian is op3 op4
    ==> is_hermitian is (op1+op3) (op2+op4)",
  REWRITE_TAC[FORALL_INNER_SPACE_THM;is_hermitian;is_closed_by]
  THEN SIMP_HORN_TAC THEN REPEAT STRIP_TAC THEN TRY LINEARITY_TAC
  THEN REWRITE_TAC[COP_TO_CFUN] THENL map MP_REWRITE_TAC [
    [CFUN_SUBSPACE_ADD;INNER_SPACE_IS_SUBSPACE];
    [CFUN_SUBSPACE_ADD;INNER_SPACE_IS_SUBSPACE];
    [INPROD_ADD_LDIST;INPROD_ADD_RDIST]
  ] THEN ASM_MESON_TAC[]);;

let SUB_HERM = full_inner_space_prove
  ("!op1 op2 op3 op4. 
    is_hermitian is op1 op2 /\ is_hermitian is op3 op4
      ==> is_hermitian is (op1-op3) (op2-op4)",
  REWRITE_TAC[FORALL_INNER_SPACE_THM;is_hermitian;is_closed_by]
  THEN SIMP_HORN_TAC THEN REPEAT STRIP_TAC THEN TRY LINEARITY_TAC
  THEN REWRITE_TAC[COP_TO_CFUN] THENL map MP_REWRITE_TAC [
    [CFUN_SUBSPACE_SUB;INNER_SPACE_IS_SUBSPACE];
    [CFUN_SUBSPACE_SUB;INNER_SPACE_IS_SUBSPACE];
    [INPROD_SUB_LDIST;INPROD_SUB_RDIST]
  ] THEN ASM_MESON_TAC[]);;

let MUL_HERM = full_inner_space_prove
  ("!op1 op2 op3 op4.
    is_hermitian is op1 op2 /\ is_hermitian is op3 op4  
      ==> is_hermitian is (op1**op3) (op4**op2)",
  REWRITE_TAC[FORALL_INNER_SPACE_THM;is_hermitian;is_closed_by]
  THEN SIMP_HORN_TAC THEN REPEAT STRIP_TAC THEN TRY LINEARITY_TAC
  THEN REWRITE_TAC[COP_TO_CFUN] THEN REWRITE_TAC[cop_mul;fun_map]
  THEN ASM_MESON_TAC[]);;

let SMUL_HERM = full_inner_space_prove
  ("!a op1 op2 op3 op4.
    is_hermitian is op1 op2 /\ is_hermitian is op3 op4
      ==> is_hermitian is (a % op1) (cnj a % op2)",
  REWRITE_TAC[FORALL_INNER_SPACE_THM;is_hermitian;is_closed_by]
  THEN SIMP_HORN_TAC THEN REPEAT STRIP_TAC THEN TRY LINEARITY_TAC
  THEN REWRITE_TAC[COP_TO_CFUN] THENL map MP_REWRITE_TAC [
    [CFUN_SUBSPACE_SMUL;INNER_SPACE_IS_SUBSPACE];
    [CFUN_SUBSPACE_SMUL;INNER_SPACE_IS_SUBSPACE];
    [INPROD_LSMUL;INPROD_RSMUL]
  ] THEN ASM_MESON_TAC[CNJ_CNJ]);;

let ZERO_HERM = prove
  (`!is. is_hermitian is cop_zero cop_zero`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM;is_hermitian;is_closed_by;ZERO_LINCOP;
   COP_ZERO_THM]
  THEN REPEAT STRIP_TAC
  THENL map MP_REWRITE_TAC [
    [CFUN_SUBSPACE_ZERO;INNER_SPACE_IS_SUBSPACE];
    [CFUN_SUBSPACE_ZERO;INNER_SPACE_IS_SUBSPACE];
    [INPROD_RZERO;INPROD_LZERO];
  ]);;
  
let ARITH_HERM_CLAUSES = CONJS [ADD_HERM;SUB_HERM;MUL_HERM;SMUL_HERM];;

let HERM_SYM = prove
  (`!is op1 op2.
    is_hermitian is op1 op2 <=> is_hermitian is op2 op1`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM;is_hermitian;is_closed_by]
  THEN MESON_TAC[CX_INJ;INPROD_CNJ]);;

let HERM_UNIQUENESS = prove
  (`!s inprod op1 op2 op3.
      is_inner_space (s,inprod)
      /\ is_hermitian (s,inprod) op1 op2 /\ is_hermitian (s,inprod) op1 op3
        ==> !x. x IN s ==> op2 x = op3 x`,
  REWRITE_TAC[is_hermitian;COP_EQ;is_closed_by] THEN SIMP_HORN_TAC 
  THEN REPEAT STRIP_TAC THEN MP_REWRITE_TAC [GSYM INPROD_INJ_ALT]
  THEN ASM_MESON_TAC[]);;

let HERM_UNIQUENESS_ALT = prove
  (`!s inprod op1 op2 op3. 
    is_inner_space (s,inprod) /\
    is_hermitian (s,inprod) op2 op1 /\ is_hermitian (s,inprod) op3 op1
      ==> !x. x IN s ==> op2 x = op3 x`,
  MESON_TAC [HERM_SYM;HERM_UNIQUENESS]);;

let HERM_PROP_ADVANCED = inner_space_prove
  ("!a b op1 op2 op3 op4 op5.
    is_hermitian (s,inprod) op1 op2 /\ is_hermitian (s,inprod) op3 op4
    /\ is_hermitian (s,inprod) op5 (a % op1 + b % op3)
      ==> !x. x IN s ==> op5 x = (cnj a % op2 + cnj b % op4) x",
   REWRITE_TAC[COP_EQ] THEN REPEAT STRIP_TAC
   THEN MATCH_MP_TAC (GIMP_IMP HERM_UNIQUENESS_ALT)
   THEN Pa.EXISTS_TAC "s" THEN REPEAT HINT_EXISTS_TAC
  THEN ASM_MESON_TAC[ARITH_HERM_CLAUSES;CNJ_CNJ;HERM_SYM]);;


(* ------------------------------------------------------------------------- *)
(* SELF ADJOINT                                                              *)
(* ------------------------------------------------------------------------- *)

let is_self_adjoint = new_definition
  `is_self_adjoint is op <=> is_hermitian is op op`;;

let IS_SELF_ADJOINT =
  REWRITE_RULE[FORALL_INNER_SPACE_THM;is_hermitian] is_self_adjoint;;

let LINCOP_SELF_ADJ = full_inner_space_prove
  ("!op. is_self_adjoint is op ==> is_linear_cop op",
  MESON_TAC[is_self_adjoint;LINCOP_LHERM]);;

let SELF_ADJ_INPROD = inner_space_prove
  ("!op1 op2. is_self_adjoint (s,inprod) op1 /\ is_closed_by s op2
    ==> !x y. x IN s /\ y IN s
      ==> inprod x ((op1 ** op2) y) = inprod (op1 x) (op2 y)",
  REWRITE_TAC[IS_SELF_ADJOINT;COP_MUL;is_closed_by] THEN MESON_TAC[]);;
  
let ADD_SELF_ADJ = full_inner_space_prove
  ("!op1 op2. is_self_adjoint is op1 /\ is_self_adjoint is op2
    ==> is_self_adjoint is (op1 + op2)",
  MESON_TAC[is_self_adjoint;ADD_HERM]);;

let SUB_SELF_ADJ = full_inner_space_prove
  ("!op1 op2. is_self_adjoint is op1 /\ is_self_adjoint is op2
    ==> is_self_adjoint is (op1 - op2)",
  MESON_TAC[is_self_adjoint;SUB_HERM]);;

let SMUL_SELF_ADJ = full_inner_space_prove
  ("!a op. real a /\ is_self_adjoint is op ==> is_self_adjoint is (a % op)",
  MESON_TAC[is_self_adjoint;SMUL_HERM;REAL_CNJ]);;

let MUL_SELF_ADJ = full_inner_space_prove
  ("!op1 op2.
    is_self_adjoint is op1 /\ is_self_adjoint is op2 /\ op1 ** op2 = op2 ** op1
    ==> is_self_adjoint is (op1 ** op2)",
  MESON_TAC[is_self_adjoint;MUL_HERM]);;

let I_SELF_ADJ = prove
  (`!is. is_self_adjoint is I`,
  REWRITE_TAC[FORALL_INNER_SPACE_THM;IS_SELF_ADJOINT;I_LINCOP;I_THM;
    IS_CLOSED_BY_I]);;

let ZERO_SELF_ADJ = prove
  (`!is. is_self_adjoint is cop_zero`,
  REWRITE_TAC[is_self_adjoint;ZERO_HERM]);;

let selfadjoint_thms = ref [];;
let add_selfadjoint_thm thm =
  let thm = GIMP_IMP thm in
  selfadjoint_thms := thm :: !selfadjoint_thms;
  let eta_thm = SIMP_RULE[ETA_AX] thm in
  if (not (equals_thm thm eta_thm))
  then selfadjoint_thms := eta_thm :: !selfadjoint_thms;;
let add_selfadjoint_thms = List.iter add_selfadjoint_thm;;

let rec SELF_ADJOINT_TAC g =
  let MATCH_MP_TAC x y = MATCH_MP_TAC x y in
  let TRY_SELFADJOINT_THM =
    ASM (MAP_FIRST (fun x ->
      MATCH_ACCEPT_TAC x ORELSE MATCH_MP_TAC x)) !selfadjoint_thms in
  let LOOP =
    TRY_SELFADJOINT_THM ORELSE (SIMP_TAC[ETA_AX] THEN TRY_SELFADJOINT_THM)
    ORELSE (ASM_SIMP_TAC[] THEN NO_TAC) ORELSE LINEARITY_TAC
    ORELSE REAL_TAC ~alternatives:[SELF_ADJOINT_TAC;LINEARITY_TAC] in
  (REPEAT STRIP_TAC
  THEN (fun (_,c as g) ->
    let head = fst (strip_comb c) in
    if (name_of head = "is_self_adjoint"
      && can (type_match `:inner_space->cop->bool` (type_of head)) [])
    then CHANGED_TAC (REPEAT (LOOP THEN REPEAT CONJ_TAC)) g
    else FAIL_TAC "bad goal" g)) g;;

let REAL_TAC ?(alternatives=[]) =
  REAL_TAC ~alternatives:(SELF_ADJOINT_TAC::LINEARITY_TAC::alternatives);;

add_selfadjoint_thms [ADD_SELF_ADJ;SUB_SELF_ADJ;SMUL_SELF_ADJ;
  REWRITE_RULE[COP_SMUL] SMUL_SELF_ADJ;MUL_SELF_ADJ;I_SELF_ADJ;ZERO_SELF_ADJ];;

let ANTI_COMMUTATOR_SELF_ADJ = full_inner_space_prove
  ("!op1 op2. is_self_adjoint is op1 /\ is_self_adjoint is op2
    ==> is_self_adjoint is (op1 ** op2 + op2 ** op1)",
  REWRITE_TAC[FORALL_INNER_SPACE_THM;IS_SELF_ADJOINT] THEN REPEAT STRIP_TAC
  THEN TRY LINEARITY_TAC
  THENL [
    MP_REWRITE_TAC[IS_CLOSED_BY_COP_ADD;IS_CLOSED_BY_COP_MUL;
      IS_CLOSED_BY_COP_MUL;INNER_SPACE_IS_SUBSPACE]
    THEN ASM_SIMP_TAC[];
    MP_REWRITE_TAC[IS_CLOSED_BY_COP_ADD;IS_CLOSED_BY_COP_MUL;
      IS_CLOSED_BY_COP_MUL;INNER_SPACE_IS_SUBSPACE]
    THEN ASM_SIMP_TAC[];
    REWRITE_TAC[COP_MUL;COP_ADD]
    THEN MP_REWRITE_TAC[INPROD_ADD_LDIST;INPROD_ADD_RDIST]
    THEN REPEAT (POP_ASSUM MP_TAC) THEN SIMP_HORN_TAC
    THEN REWRITE_TAC[is_closed_by] THEN ASM_MESON_TAC[COMPLEX_ADD_SYM]
  ]);;

add_selfadjoint_thm ANTI_COMMUTATOR_SELF_ADJ;;

let NEG_SELF_ADJ = full_inner_space_prove
  ("!op. is_linear_cop op /\ is_self_adjoint is op
    ==> is_self_adjoint is (--op)",
  ONCE_REWRITE_TAC[GSYM COP_SUB_LZERO] THEN SELF_ADJOINT_TAC);;

add_selfadjoint_thm NEG_SELF_ADJ;;

let SCALAR_II_HERM = inner_space_prove
  ("!op. is_linear_cop op /\ (!x y. inprod (op x) y = -- (inprod x (op y)))
      /\ is_closed_by s op
        ==> is_self_adjoint (s,inprod) (ii % op)",
  REWRITE_TAC[IS_SELF_ADJOINT;COP_SMUL_THM]
  THEN REPEAT STRIP_TAC
  THENL [
    MP_REWRITE_TAC[IS_CLOSED_BY_COP_SMUL;INNER_SPACE_IS_SUBSPACE];
    MP_REWRITE_TAC[IS_CLOSED_BY_COP_SMUL;INNER_SPACE_IS_SUBSPACE];
    LINEARITY_TAC;
    LINEARITY_TAC;
    MP_REWRITE_TAC[INPROD_LSMUL;INPROD_RSMUL]
    THEN REWRITE_TAC[CNJ_II;COMPLEX_NEG_MUL2]
    THEN ASM_MESON_TAC[is_closed_by]
  ]);;

add_selfadjoint_thm SCALAR_II_HERM;;

let COMMUTATOR_ANTI_HERM = inner_space_prove
  ("!op1 op2. is_self_adjoint (s,inprod) op1 /\ is_self_adjoint (s,inprod) op2
    ==> !x y. x IN s /\ y IN s
      ==> inprod (commutator op1 op2 x) y = --(inprod x (commutator op1 op2 y))",
  REWRITE_TAC[commutator;IS_SELF_ADJOINT;COP_MUL_THM;COP_SUB_THM;is_closed_by]
  THEN SIMP_HORN_TAC THEN REPEAT STRIP_TAC
  THEN MP_REWRITE_TAC[INPROD_SUB_LDIST;INPROD_SUB_RDIST]
  THEN REWRITE_TAC[COMPLEX_NEG_SUB]
  THEN ASM_MESON_TAC[]);;

add_selfadjoint_thm COMMUTATOR_ANTI_HERM;;

let II_COMMUTATOR_HERM = full_inner_space_prove
  ("!op1 op2. is_self_adjoint is op1 /\ is_self_adjoint is op2
    ==> is_self_adjoint is (ii % commutator op1 op2)",
  REWRITE_TAC[FORALL_INNER_SPACE_THM;IS_SELF_ADJOINT;COP_SMUL_THM]
  THEN SIMP_HORN_TAC THEN REPEAT STRIP_TAC
  THENL [
    MP_REWRITE_TAC [INPROD_RSMUL;INPROD_LSMUL];
    LINEARITY_TAC;
    ASM_MESON_TAC[IS_CLOSED_BY_COMMUTATOR;IS_CLOSED_BY_COP_SMUL;
      INNER_SPACE_IS_SUBSPACE]
  ]
  THEN REWRITE_TAC[CNJ_II;COMPLEX_MUL_LNEG;GSYM COMPLEX_MUL_RNEG;
    COMPLEX_EQ_MUL_LCANCEL;II_NZ]
  THEN ONCE_REWRITE_TAC[COMPLEX_FIELD `x = --y <=> y = --x:complex`]
  THEN MP_REWRITE_TAC [GIMP_IMP COMMUTATOR_ANTI_HERM]
  THEN REWRITE_TAC[is_self_adjoint;is_hermitian]
  THEN ASM_MESON_TAC[is_closed_by;IS_CLOSED_BY_COMMUTATOR;
    INNER_SPACE_IS_SUBSPACE]);;
   
add_selfadjoint_thm II_COMMUTATOR_HERM;;

let EXPEC_HERM_REAL = inner_space_prove
  ("!op state. is_self_adjoint (s,inprod) op /\ state IN s
    ==> real (expectation inprod state op)", 
  REWRITE_TAC[IS_SELF_ADJOINT;expectation;is_closed_by]
  THEN SIMP_HORN_TAC THEN REPEAT STRIP_TAC THEN REWRITE_TAC[REAL_CNJ]
  THEN ASM_MESON_TAC[INPROD_CNJ]);;

add_real_thms [EXPEC_HERM_REAL; REWRITE_RULE[expectation] EXPEC_HERM_REAL];;

let DEVIATION_HERM = inner_space_prove
  ("!op state. is_self_adjoint (s,inprod) op /\ state IN s
    ==> is_self_adjoint (s,inprod) (deviation inprod state op)",
  REWRITE_TAC[DEVIATION_ALT] THEN SELF_ADJOINT_TAC THEN ASM_MESON_TAC[]);;

add_selfadjoint_thms [DEVIATION_HERM; REWRITE_RULE[deviation] DEVIATION_HERM];;

let VARIANCE_REAL = inner_space_prove
  ("!op state.  state IN s /\ is_self_adjoint (s,inprod) op
    ==> real (variance inprod state op)", 
  REWRITE_TAC[variance] THEN REAL_TAC THEN HINT_EXISTS_TAC
  THEN SELF_ADJOINT_TAC);;

add_real_thm VARIANCE_REAL;;


(* ------------------------------------------------------------------------- *)
(* EIGEN VALUES AND VECTORS                                                  *)
(* ------------------------------------------------------------------------- *)

let is_eigen_pair = new_definition
  `is_eigen_pair (op:cfun->cfun) (x,a) <=>
    is_linear_cop op ==> op x = a % x /\ ~(x = cfun_zero)`;;

let EIGEN_PAIR_SMUL = prove
  (`!op v x. is_eigen_pair op (x,v)
    ==> !a. ~(a = Cx(&0)) ==> is_eigen_pair op (a % x,v)`,
  SIMP_TAC[is_eigen_pair;CFUN_ENTIRE;LINCOP_SMUL;CFUN_SMUL_SYM]);;

let EIGEN_PAIR_ADD = prove
  (`!op v x y. is_eigen_pair op (x,v) /\ is_eigen_pair op (y,v)
        /\ ~(x + y = cfun_zero)
          ==> is_eigen_pair op (x+y,v)`,
  SIMP_TAC[is_eigen_pair;LINCOP_ADD;CFUN_ADD_LDISTRIB]);;

let EIGEN_SPACE_THM = prove
  (`!op. is_linear_cop op ==>
    !a. is_cfun_subspace ({ x | is_eigen_pair op (x,a) } UNION { cfun_zero })`,
  SIMP_TAC[is_cfun_subspace;IN_ELIM_THM;IN_UNION;IN_SING;CFUN_ENTIRE]
  THEN REPEAT STRIP_TAC THEN ASM_SIMP_TAC[CFUN_ADD_RID;CFUN_ADD_LID]
  THEN ASM_MESON_TAC[EIGEN_PAIR_SMUL;EIGEN_PAIR_ADD]);;

let is_eigen_val = new_definition
  `is_eigen_val (op:cfun->cfun) a <=> ?x. is_eigen_pair op (x,a)`;;

let is_eigen_fun = new_definition
  `is_eigen_fun (op:cfun->cfun) x <=> ?a. is_eigen_pair op (x,a)`;;
