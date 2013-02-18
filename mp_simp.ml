(****************************)
(* UTILS                    *)
(****************************)

let seq x f = f x;;

let strip_conj = binops `(/\)`;;

let rec tryfind_fun fs x =
  match fs with
  |[] -> failwith "tryfind_fun"
  |f::fs' -> try f x with _ -> tryfind_fun fs' x;;

let rec SPEC_VARS th =
  try
    let v,th' = SPEC_VAR th in
    let vs,th'' = SPEC_VARS th' in
    v::vs,th''
  with _ -> [],th;;

let MAP_FORALL_BODY f th =
  let vs,th = SPEC_VARS th in
  GENL vs (f th);;

let UNDISCH_TERM th =
  let p = (fst o dest_imp o concl) th in
  p,UNDISCH th;;

let MAP_CONCLUSION f th =
  let p,th = UNDISCH_TERM th in
  DISCH p (f th);;

let VARIANT_CONV av t =
  let vs = variables t in
  let mapping = filter (fun (x,y) -> x <> y) (zip vs (variants av vs)) in
  let ALPHA_CONV' u = ALPHA_CONV (assoc (bndvar u) mapping) u in
  DEPTH_CONV ALPHA_CONV' t;;

let VARIANT_RULE = CONV_RULE o VARIANT_CONV;;

let PART_MATCH_GEN =
  let rec match_bvs t1 t2 acc =
    try let v1,b1 = dest_abs t1
        and v2,b2 = dest_abs t2 in
        let n1 = fst(dest_var v1) and n2 = fst(dest_var v2) in
        let newacc = if n1 = n2 then acc else insert (n1,n2) acc in
        match_bvs b1 b2 newacc
    with Failure _ -> try
        let l1,r1 = dest_comb t1
        and l2,r2 = dest_comb t2 in
        match_bvs l1 l2 (match_bvs r1 r2 acc)
    with Failure _ -> acc in
  fun partfn th ->
    let bvs = (fst o strip_forall o concl) th in
    let sth = SPEC_ALL th in
    let bod = concl sth in
    let pbod = partfn bod in
    let lconsts = intersect (frees (concl th)) (freesl(hyp th)) in
    fun tm ->
      let bvms = match_bvs tm pbod [] in
      let abod = deep_alpha bvms bod in
      let ath = EQ_MP (ALPHA bod abod) sth in
      let (_,s,_ as insts) = term_match lconsts (partfn abod) tm in
      let fth = INSTANTIATE insts ath in
      if hyp fth <> hyp ath then failwith "PART_MATCH: instantiated hyps" else
      let tm' = partfn (concl fth) in
      let dom = snd (unzip s) in
      let fth = GENL (map (instantiate insts) (subtract bvs dom)) fth in
      if Pervasives.compare tm' tm = 0 then fth else
      try SUBS[ALPHA tm' tm] fth
      with Failure _ -> failwith "PART_MATCH: Sanity check failure";; 

(****************************)
(* CORE TACTIC              *)
(****************************)

let qpath t qu = function
  |"r"::"b"::path' ->
      let b = rand t in
      qu (bndvar b) (body b) path'
  |_ -> failwith "qpath";;

let upath t un = function
  |"r"::path' -> un (rand t) path'
  |_ -> failwith "upath";;

let bpath t left right = function
  |"l"::"r"::path' -> left (lhand t) (rand t) path'
  |"r"::path' -> right (rand t) (lhand t) path'
  |_ -> failwith "bpath";;

let indep_vars th =
  let p,c = (dest_imp o concl o SPEC_ALL) th in
  subtract (union (frees p) (frees (rhs c))) (frees (lhs c));;

let GEN_IMP_REWR_CONV av =
  let part_match = GEN_PART_MATCH (lhs o snd o strip_forall o snd o dest_imp) in
  fun th t ->
    let th' = part_match th t in
    VARIANT_RULE av (GENL (indep_vars th') th');;

let atomic_mp_simp =
  let pr = ref `T` and bvs = ref [] in
  let update_pr (u,th) = pr := u; th and update_bvs (vs,th) = bvs := vs; th in
  let UNDISCH_TERM = update_pr o UNDISCH_TERM in
  let SPEC_VARS = update_bvs o SPEC_VARS in
  let base av th = UNDISCH_TERM o SPEC_VARS o GEN_IMP_REWR_CONV av th in
  let eq p th t =
    EQ_IMP_RULE (PATH_CONV (implode p) (base (variables t) th) t) in
  let common sel lem th t p = 
    let t = (CONV_RULE (REWR_CONV lem) o DISCH !pr o sel) (eq p th t) in
    PURE_REWRITE_RULE[LEFT_FORALL_IMP_THM;RIGHT_FORALL_IMP_THM]
      (GENL !bvs t)
  in
  let IMP_IMP_SYM = TAUT `A==>B==>C <=> B==>A==>C` in
  fun _ -> function true -> common snd IMP_IMP | false -> common fst IMP_IMP_SYM;;

let deep_mp base_ctx atomic_case =
  let impl = TAUT `!B A A'. (A==>A') ==> (A'==>B) ==> (A==>B)` in
  let impr = TAUT `!B A' A. (A'==>A) ==> (B==>A') ==> (B==>A)` in
  let disjr = TAUT `!B A' A. (A'==>A) ==> (B\/A') ==> (B\/A)` in
  let disjl = TAUT `!B A' A. (A'==>A) ==> (A'\/B) ==> (A\/B)` in
  let conjr = TAUT `!B A' A. (A'==>A) ==> (B/\A') ==> (B/\A)` in
  let conjl = TAUT `!B A' A. (A'==>A) ==> (A'/\B) ==> (A/\B)` in
  let mono_quant = GEN_ALL o function "!" -> MONO_FORALL |"?" -> MONO_EXISTS in
  fun th ->
    let rec dispatch ctx pos t p =
      let app' c pos lem t u x = MATCH_MP (SPEC u lem) (dispatch c pos t x) in
      let app = app' ctx and app'' x = app' (strip_conj (lhand t) @ ctx) x in
      seq p (match p with
      |[] -> atomic_case ctx pos th t
      |_::_ ->
        match name_of (fst (strip_comb t)) with
        |"/\\" -> bpath t (app pos conjl) (app pos conjr)
        |"\\/" -> bpath t (app pos disjl) (app pos disjr)
        |"==>" -> bpath t (app (not pos) impl) (app'' pos impr)
        |"~" -> upath t (fun t ->
            PURE_ONCE_REWRITE_RULE[NOT_FORALL_THM] 
               o MATCH_MP (GEN_ALL MONO_NOT) o dispatch [] (not pos) t)
        |"!"|"?" as q -> qpath t (fun v b ->
            MATCH_MP (mono_quant q) o GEN v o dispatch ctx pos b)
        |_ -> atomic_case ctx pos th t)
    in
    fun t -> dispatch base_ctx true t o explode;;

(* TODO
 * - Generaliser a n'importe quelle relation transitive? (see
 * SCHWARZ_INEQUALITY_ENHANCED)
 * - Generalize to "P1 ==> ... ==> Pn ==> l = r"
 *)
let CORE_PURE_MP_SIMP_TAC =
  let PART_MATCH = PART_MATCH (lhs o snd o strip_forall o snd o dest_imp) in
  fun path ths ->
    let PART_MATCH = tryfind_fun (map PART_MATCH ths) in
    fun (_,c as g) ->
      let th = ref TRUTH in
      let match_term t = try th := PART_MATCH t; true with _ -> false in
      let path' = path ^ find_path match_term (follow_path path c) in
      MATCH_MP_TAC (deep_mp [] atomic_mp_simp !th c path') g;;

(******************************************************)
(* PRE&POST-PROCESSING                                *)
(*                                                    *)
(* A bit of preprocessing to handle more situations:  *)
(* - non-conditional rewrites (for uniformity only)   *)
(* - cases where the conclusion is not an equality    *)
(******************************************************)

(* For any theorem of the form `!xyz. P`, returns `!xyz. T ==> P` unless P is
 * already an implication. *)
let TIMP_INTRO = 
  let IMPT_INTRO = CONV_RULE (REWR_CONV (TAUT `t <=> T ==> t`)) in
  MAP_FORALL_BODY (fun t -> if is_imp (concl t) then t else IMPT_INTRO t);;

(* Expects a theorem of the form `!xyz. P ==> C`
 * Returns `!xyz. P ==> C = T` *)
let GEQT_INTRO1 = MAP_FORALL_BODY (MAP_CONCLUSION EQT_INTRO);;

(* Expects a theorem of the form `!xyz. P ==> !xyz. C`
 * Returns `!xyz. P ==> !xyz. (C = T)` *)
let GEQT_INTRO2 = MAP_FORALL_BODY (MAP_CONCLUSION (MAP_FORALL_BODY EQT_INTRO));;

let mk_mp_rewrites th =
  let th = TIMP_INTRO th in
  let ths1 = 
    try if (is_eq o snd o dest_imp o concl o SPEC_ALL) th then [th] else []
    with _ -> []
  in
  let ths2 = try [GEQT_INTRO2 th] with _ -> [] in
  union [GEQT_INTRO1 th] (union ths2 ths1);;

let PURE_MP_SIMP_TAC = CORE_PURE_MP_SIMP_TAC "" o mk_mp_rewrites;;

(* Simplification of Horn clauses
 * (which frequently appear when using MP_SIMP_TAC) *)
let rec simp_horn_conv =
  let fact (x,y) = if x = [] then y else fail () in
  let rec tl = function [] -> [] | _::xs -> xs in
  fun l ->
    let fixpoint = ref true in
    let l' =
      rev_itlist (fun (hs,cs) (dones,todos) ->
        let facts = flat (mapfilter fact (dones@todos)) in
        let f = filter (not o C mem facts) in
        let hs' = f hs in
        let cs' = filter (not o C mem hs') (f cs) in
        if not (hs' = hs) or not (cs' = cs) then fixpoint := false;
        if (cs' = [] && cs <> [])
        then (dones,tl todos)
        else ((hs',cs')::dones),tl todos)
      l ([],tl l)
    in
    if !fixpoint then l else simp_horn_conv (fst l');;

let horns_of_term =
  fun t -> map (fun t ->
    try
      let h,c = dest_imp t in
      strip_conj h,strip_conj c
    with _ -> [],[t]) (strip_conj t);;

let term_of_horns =
  let term_of_horn = function
    |[],cs -> list_mk_conj cs
    |_,[] -> (print_endline "ici";`T`)
    |hs,cs -> mk_imp (list_mk_conj hs,list_mk_conj cs)
  in
  list_mk_conj o map term_of_horn;;

let SIMP_HORN_CONV t =
  TAUT (mk_eq (t,((term_of_horns o simp_horn_conv o horns_of_term) t)));;

let SIMP_HORN_TAC =
  ASSUM_LIST (fun xs ->
    MP_TAC (CONJS xs) THEN REWRITE_TAC[IMP_IMP]
    THEN CONV_TAC (TOP_DEPTH_CONV (CHANGED_CONV SIMP_HORN_CONV))
    THEN ASM_REWRITE_TAC[]);;

let atomic_hint_exists ctx pos _ t _ =
  if not pos then failwith "atomic_hint_exists" else
  let vs,t' = strip_exists t in
  let hyp_match c h =
    let dom,lcs = partition (C mem vs) (variables c) in
    if dom = [] then fail () else term_match lcs c h,subtract vs dom
  in
  let (_,ws,_ as i),os = tryfind (C tryfind ctx o hyp_match) (strip_conj t') in
  let instantiated_t = list_mk_exists (os,instantiate i t') in
  let MY_EXISTS_TAC (_,c as g) =
    let v,_ = dest_exists c in
    EXISTS_TAC (if mem v os then v else try rev_assoc v ws with _ -> v) g
  in
  prove(mk_imp(instantiated_t,t),
    DISCH_THEN (REPEAT_TCL CHOOSE_THEN ASSUME_TAC) THEN REPEAT MY_EXISTS_TAC
    THEN POP_ASSUM ACCEPT_TAC);;

(*
 *let atomic_hint_exists ctx pos _ t _ =
 *  if not pos then failwith "atomic_hint_exists" else
 *  let v,t' = dest_exists t in
 *  let vs,t'' = strip_exists t' in
 *  let hyp_match c h =
 *   ignore (check (not o exists (C mem vs) o frees) c);
 *   term_match (subtract (frees c) [v]) c h
 *  in
 *  let (_,subs,_) = tryfind (C tryfind ctx o hyp_match) (strip_conj t'') in
 *  let witness =
 *    match subs with
 *    |[] -> v
 *    |[t,u] when u = v -> t
 *    |_ -> failwith "atomic_hint_exists not applicable"
 *  in
 *  let instantiated_t = rhs (concl (BETA_CONV (mk_comb (rand t,witness)))) in
 *  DISCH instantiated_t (EXISTS (t,witness) (ASSUME instantiated_t));;
 *)

let HINT_EXISTS_TAC (asms,c as g) =
  let hs = map (concl o snd) asms in
  MATCH_MP_TAC (deep_mp hs atomic_hint_exists TRUTH c (find_path is_exists c)) g;;

let ONCE_MP_SIMP_TAC x =
  PURE_MP_SIMP_TAC x
  THEN REPEAT (FIRST (map CHANGED_TAC
    [HINT_EXISTS_TAC;SIMP_HORN_TAC;ASM_SIMP_TAC[]]));;

let MP_SIMP_TAC = REPEAT o CHANGED_TAC o MAP_EVERY (REPEAT o ONCE_MP_SIMP_TAC);;

let ASM_MP_SIMP_TAC = ASM MP_SIMP_TAC;;

let CASES_REWRITE_TAC th (_,c as g) =
  let PART_MATCH =
    let concl = snd o dest_imp in
    let body = snd o strip_forall o concl in
    try PART_MATCH (lhs o body) th
    with _ ->
      let f1 = PART_MATCH concl th and f2 = PART_MATCH body th in
      fun t -> try f1 t with _ -> f2 t
  in
  let th = ref TRUTH in
  ignore (find_term (fun t -> try th := PART_MATCH t; true with _ -> false) c);
  (ASM_CASES_TAC (lhand (concl !th)) THENL [
    POP_ASSUM (fun x -> REWRITE_TAC[MP !th x] THEN ASSUME_TAC x);
    POP_ASSUM (ASSUME_TAC o REWRITE_RULE[NOT_CLAUSES])]) g;;

(*
 (* TODO Allow to provide a list of theorems instead of just assumptions.
 * Very simple on paper: abstract away the hypotheses.
 * However the theorems that one would want to use in this context would be
 * universal theorems which fucks up everything.
 *)
let HINT_EXISTS_TAC (hs,c as g) =
   let hs = map snd hs in
   let v,c' = dest_exists c in
   let vs,c' = strip_exists c' in
   let hyp_match c h =
     ignore (check (not o exists (C mem vs) o frees) c);
     term_match (subtract (frees c) [v]) c (concl h), h
   in
   let (_,subs,_),h = tryfind (C tryfind hs o hyp_match) (strip_conj c') in
   let witness =
     match subs with
       |[] -> v
       |[t,u] when u = v -> t
       |_ -> failwith "HINT_EXISTS_TAC not applicable"
   in
   (EXISTS_TAC witness THEN REWRITE_TAC hs) g;; *)
