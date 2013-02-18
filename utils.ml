let EQ_TO_IMP = TAUT `!P Q. (P <=> Q) <=> (P ==> Q) /\ (Q==>P)`;;

module Pa :
  sig
    val CONTEXT_TAC : ((string * pretype) list -> tactic) -> tactic
    val PARSE_IN_CONTEXT : (term -> tactic) -> (string -> tactic)
    val EXISTS_TAC : string -> tactic
    val SUBGOAL_THEN : string -> thm_tactic -> tactic
    val SUBGOAL_TAC : string -> string -> tactic list -> tactic
    val ASM_CASES_TAC : string -> tactic
    val BOOL_CASES_TAC : string -> tactic
    val SPEC_TAC : string * string -> tactic
    val SPEC : string -> thm -> thm
    val SPECL : string list -> thm -> thm
    val GEN : string -> thm -> thm
    val GENL : string list -> thm -> thm
    val X_GEN_TAC : string -> tactic
    val REAL_ARITH : string -> thm
    val REAL_FIELD : string -> thm
    val REAL_RING : string -> thm
    val ARITH_RULE : string -> thm
    val NUM_RING : string -> thm
    val INT_ARITH : string -> thm
    val call_with_interface : (unit -> 'a) -> (term -> 'b) -> string -> 'b
  end
  =
  struct
    let parse_preterm = fst o parse_preterm o lex o explode

    let CONTEXT_TAC ttac (asms,c as g) =
      let vs = frees c @ freesl (map (concl o snd) asms) in
      ttac (map (fun x -> name_of x,pretype_of_type(type_of x)) vs) g

    let PARSE_IN_CONTEXT ttac s =
      CONTEXT_TAC (fun env ->
        ttac (term_of_preterm (retypecheck env (parse_preterm s))))

    let type_of_forall = type_of o fst o dest_forall

    let force_type ?(env=[]) s ty =
      let pty = pretype_of_type ty in
      term_of_preterm (retypecheck env (Typing(parse_preterm s,pty)))

    let BOOL_CONTEXT_TAC ttac s =
      CONTEXT_TAC (fun env -> ttac (force_type ~env s bool_ty))

    let SUBGOAL_THEN s ttac = BOOL_CONTEXT_TAC (C SUBGOAL_THEN ttac) s
    let SUBGOAL_TAC l s tacs = BOOL_CONTEXT_TAC (C (SUBGOAL_TAC l) tacs) s

    let ASM_CASES_TAC = BOOL_CONTEXT_TAC ASM_CASES_TAC
    let BOOL_CASES_TAC = BOOL_CONTEXT_TAC BOOL_CASES_TAC

    let EXISTS_TAC s (_,c as g) =
      CONTEXT_TAC (fun env ->
        EXISTS_TAC (force_type ~env s (type_of (fst (dest_exists c))))) g
        
    let SPEC_TAC (u,x) =
      PARSE_IN_CONTEXT (fun u' -> SPEC_TAC (u',force_type x (type_of u'))) u

    let SPEC s th = SPEC (force_type s (type_of_forall (concl th))) th

    let SPECL tms th =
      try rev_itlist SPEC tms th with Failure _ -> failwith "SPECL"

    let GEN s th =
      GEN (try find ((=) s o name_of) (frees (concl th)) with _ -> parse_term s)
        th

    let GENL = itlist GEN

    let X_GEN_TAC s (_,c as g) = X_GEN_TAC (force_type s (type_of_forall c)) g

    let call_with_interface p f s =
      let i = !the_interface in
      p ();
      let res = f (parse_term s) in
      the_interface := i;
      res

    let [REAL_ARITH;REAL_FIELD;REAL_RING] =
      map (call_with_interface prioritize_real) [REAL_ARITH;REAL_FIELD;REAL_RING]
    let [ARITH_RULE;NUM_RING] =
      map (call_with_interface prioritize_num) [ARITH_RULE;NUM_RING]
    let INT_ARITH = call_with_interface prioritize_int INT_ARITH
  end;;

module Pa =
  struct
    include Pa
    let COMPLEX_FIELD = call_with_interface prioritize_complex COMPLEX_FIELD;;
    let SIMPLE_COMPLEX_ARITH =
      call_with_interface prioritize_complex SIMPLE_COMPLEX_ARITH;
  end;;

(*needs "/Volumes/NO NAME/Quantum/mp_simp.ml";;*)
needs "/media/C81B-2C26/Quantum/mp_simp.ml";;

let wrap f x = f [x];;

let CONJS xs = end_itlist CONJ xs;;

let rec fixpoint f x =
  let y = f x in
  if y = x then y else fixpoint f y;;

let gimp_imp =
  let rec self vars premisses t =
    try
      let v,b = dest_forall t in
      self (v::vars) premisses b
    with _ ->
      try
        let p,c = dest_imp t in
        self vars (p::premisses) c
      with _ ->
        let body =
          match premisses with
          |[] -> t
          |_::_ -> mk_imp(list_mk_conj (rev premisses),t)
        in
        list_mk_forall(rev vars,body)
  in
  self [] [];;

let GIMP_IMP_CONV t = MESON[](mk_eq(t,gimp_imp t));;

let GIMP_IMP = CONV_RULE GIMP_IMP_CONV;;  

let MATCH_TRANS thm1 thm2 =
  GEN_ALL (DISCH_ALL (MATCH_MP thm2 (UNDISCH (SPEC_ALL thm1))));;

(*
let THEN1 = ...*)

