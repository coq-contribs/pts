type __ = Obj.t
let __ = let rec f _ = Obj.repr f in Obj.repr f

type nat =
  | O
  | S of nat

type ('a, 'b) sum =
  | Inl of 'a
  | Inr of 'b

type ('a, 'b) prod =
  | Pair of 'a * 'b

type 'a sig0 = 'a
  (* singleton inductive, whose constructor was exist *)

type 'a sig2 = 'a
  (* singleton inductive, whose constructor was exist2 *)

type ('a, 'p) sigT =
  | ExistT of 'a * 'p

type 'a exc = 'a option

(** val value : 'a1 -> 'a1 option **)

let value x =
  Some x

(** val error : 'a1 option **)

let error =
  None

(** val pred : nat -> nat **)

let pred = function
  | O -> O
  | S u -> u

(** val plus : nat -> nat -> nat **)

let rec plus n m =
  match n with
    | O -> m
    | S p -> S (plus p m)

(** val eq_nat_dec : nat -> nat -> bool **)

let rec eq_nat_dec n m =
  match n with
    | O -> (match m with
              | O -> true
              | S m0 -> false)
    | S n0 -> (match m with
                 | O -> false
                 | S m0 -> eq_nat_dec n0 m0)

(** val lt_eq_lt_dec : nat -> nat -> bool option **)

let rec lt_eq_lt_dec n m =
  match n with
    | O -> (match m with
              | O -> Some false
              | S n0 -> Some true)
    | S n0 -> (match m with
                 | O -> None
                 | S m0 -> lt_eq_lt_dec n0 m0)

(** val le_lt_dec : nat -> nat -> bool **)

let rec le_lt_dec n m =
  match n with
    | O -> true
    | S n0 -> (match m with
                 | O -> false
                 | S m0 -> le_lt_dec n0 m0)

(** val le_gt_dec : nat -> nat -> bool **)

let le_gt_dec n m =
  le_lt_dec n m

type 'a list =
  | Nil
  | Cons of 'a * 'a list

(** val list_item : 'a1 list -> nat -> 'a1 option **)

let rec list_item e n =
  match e with
    | Nil -> None
    | Cons (h, l) -> (match n with
                        | O -> Some h
                        | S k -> list_item l k)

(** val max_nat : nat -> nat -> nat **)

let max_nat n m =
  if le_gt_dec n m then m else n

type decide = bool

type 'a ppal_dec = 'a option

type 'sort term =
  | Srt of 'sort
  | Ref of nat
  | Abs of 'sort term * 'sort term
  | App of 'sort term * 'sort term
  | Prod of 'sort term * 'sort term

(** val lift_rec : nat -> 'a1 term -> nat -> 'a1 term **)

let rec lift_rec n t k =
  match t with
    | Srt s -> Srt s
    | Ref i -> Ref (if le_gt_dec k i then plus n i else i)
    | Abs (a, m) -> Abs ((lift_rec n a k), (lift_rec n m (S k)))
    | App (u, v) -> App ((lift_rec n u k), (lift_rec n v k))
    | Prod (a, b) -> Prod ((lift_rec n a k), (lift_rec n b (S k)))

(** val lift : nat -> 'a1 term -> 'a1 term **)

let lift n n0 =
  lift_rec n n0 O

(** val subst_rec : 'a1 term -> 'a1 term -> nat -> 'a1 term **)

let rec subst_rec ts t k =
  match t with
    | Srt s -> Srt s
    | Ref i ->
        (match lt_eq_lt_dec k i with
           | Some s -> if s then Ref (pred i) else lift k ts
           | None -> Ref i)
    | Abs (a, m) -> Abs ((subst_rec ts a k), (subst_rec ts m (S k)))
    | App (u, v) -> App ((subst_rec ts u k), (subst_rec ts v k))
    | Prod (a, b) -> Prod ((subst_rec ts a k), (subst_rec ts b (S k)))

(** val subst : 'a1 term -> 'a1 term -> 'a1 term **)

let subst n m =
  subst_rec n m O

type 'sort decl =
  | Ax of 'sort term
  | Def of 'sort term * 'sort term

(** val typ_of_decl : 'a1 decl -> 'a1 term **)

let typ_of_decl = function
  | Ax t -> t
  | Def (m, t) -> t

type 'sort env = 'sort decl list

type 'sort basic_rule =
  | Build_Basic_rule

type 'sort subtyping_rule =
  'sort basic_rule
  (* singleton inductive, whose constructor was Build_Subtyping_rule *)

type 'sort pTS_sub_spec =
  'sort subtyping_rule
  (* singleton inductive, whose constructor was Build_PTS_sub_spec *)

(** val is_a_sort : 'a1 term -> decide **)

let is_a_sort = function
  | Srt s -> true
  | _ -> false

type 'sort red_to_sort_dec = 'sort ppal_dec

type 'sort red_to_wf_prod_dec = ('sort term, 'sort term) prod option

type 'sort pTS_algos = { pa_lift : (nat -> 'sort term -> 'sort term);
                         pa_subst : ('sort term -> 'sort term -> 'sort term);
                         pa_infer_axiom : ('sort -> 'sort ppal_dec);
                         pa_least_sort : ('sort env -> 'sort term -> __ ->
                                         'sort red_to_sort_dec);
                         pa_infer_rule : ('sort -> 'sort -> 'sort);
                         pa_least_prod : ('sort env -> 'sort term -> __ ->
                                         'sort red_to_wf_prod_dec);
                         pa_le_type_dec : ('sort env -> 'sort term -> 'sort
                                          term -> __ -> __ -> decide) }

(** val pa_lift :
    'a1 pTS_sub_spec -> 'a1 pTS_algos -> nat -> 'a1 term -> 'a1 term **)

let pa_lift _ x = x.pa_lift

(** val pa_subst :
    'a1 pTS_sub_spec -> 'a1 pTS_algos -> 'a1 term -> 'a1 term -> 'a1 term **)

let pa_subst _ x = x.pa_subst

(** val pa_infer_axiom :
    'a1 pTS_sub_spec -> 'a1 pTS_algos -> 'a1 -> 'a1 ppal_dec **)

let pa_infer_axiom _ x = x.pa_infer_axiom

(** val pa_infer_rule :
    'a1 pTS_sub_spec -> 'a1 pTS_algos -> 'a1 -> 'a1 -> 'a1 **)

let pa_infer_rule _ x = x.pa_infer_rule

type 'sort type_error =
  | Under of 'sort term * 'sort type_error
  | Expected_type of 'sort term * 'sort term * 'sort term
  | Topsort of 'sort
  | Db_error of nat
  | Lambda_topsort of 'sort term * 'sort
  | Not_a_type of 'sort term * 'sort term
  | Not_a_fun of 'sort term * 'sort term
  | Apply_err of 'sort term * 'sort term * 'sort term * 'sort term

type 'sort infer_ppal_type = ('sort term, 'sort type_error sig2) sum

type 'sort wft_dec =
  | Wft_ok
  | Wft_fail of 'sort type_error

type 'sort check_dec =
  | Chk_ok
  | Chk_fail of 'sort type_error

type 'sort decl_dec =
  | Dcl_ok
  | Dcl_fail of 'sort type_error

type 'sort pTS_TC = { ptc_inf_ppal_type : ('sort env -> 'sort term -> __ ->
                                          'sort infer_ppal_type);
                      ptc_chk_typ : ('sort env -> 'sort term -> 'sort term ->
                                    __ -> 'sort check_dec);
                      ptc_add_typ : ('sort env -> 'sort term -> __ -> 'sort
                                    decl_dec);
                      ptc_add_def : ('sort env -> 'sort term -> 'sort term ->
                                    __ -> 'sort decl_dec);
                      ptc_chk_wk : ('sort env -> 'sort term -> 'sort term ->
                                   __ -> __ -> 'sort check_dec);
                      ptc_chk_wft : ('sort env -> 'sort term -> __ -> 'sort
                                    wft_dec) }

(** val fix_chk_wk :
    'a1 pTS_sub_spec -> 'a1 pTS_algos -> ('a1 term -> 'a1 env -> __ -> 'a1
    infer_ppal_type) -> 'a1 env -> 'a1 term -> 'a1 term -> 'a1 check_dec **)

let fix_chk_wk the_PTS the_algos fix_inference e t t0 =
  match fix_inference t e __ with
    | Inl s ->
        if the_algos.pa_le_type_dec e s t0 __ __
        then Chk_ok
        else Chk_fail (Expected_type (t, s, t0))
    | Inr s -> Chk_fail s

(** val fix_add_typ :
    'a1 pTS_sub_spec -> 'a1 pTS_algos -> ('a1 term -> 'a1 env -> __ -> 'a1
    infer_ppal_type) -> 'a1 env -> 'a1 term -> 'a1 decl_dec **)

let fix_add_typ the_PTS the_algos fix_inference e t =
  match fix_inference t e __ with
    | Inl s ->
        (match the_algos.pa_least_sort e s __ with
           | Some s0 -> Dcl_ok
           | None -> Dcl_fail (Not_a_type (t, s)))
    | Inr s -> Dcl_fail s

(** val infer_ref :
    'a1 pTS_sub_spec -> 'a1 pTS_algos -> 'a1 env -> nat -> 'a1
    infer_ppal_type **)

let infer_ref the_PTS the_algos e n =
  match list_item e n with
    | Some s -> Inl (the_algos.pa_lift (S n) (typ_of_decl s))
    | None -> Inr (Db_error n)

(** val infer_app :
    'a1 pTS_sub_spec -> 'a1 pTS_algos -> ('a1 term -> 'a1 env -> __ -> 'a1
    infer_ppal_type) -> 'a1 env -> 'a1 term -> 'a1 term -> 'a1
    infer_ppal_type **)

let infer_app the_PTS the_algos fix_inference e u v =
  match fix_inference u e __ with
    | Inl s ->
        (match the_algos.pa_least_prod e s __ with
           | Some s0 ->
               let Pair (dom, rng) = s0 in
               (match fix_chk_wk the_PTS the_algos fix_inference e v dom with
                  | Chk_ok -> Inl (the_algos.pa_subst v rng)
                  | Chk_fail err -> Inr
                      (match err with
                         | Expected_type (v0, tv, t) -> Apply_err (u, (Prod
                             (dom, rng)), v0, tv)
                         | _ -> err))
           | None -> Inr (Not_a_fun (u, s)))
    | Inr s -> Inr s

(** val infer_abs :
    'a1 pTS_sub_spec -> 'a1 pTS_algos -> ('a1 term -> 'a1 env -> __ -> 'a1
    infer_ppal_type) -> 'a1 env -> 'a1 term -> 'a1 term -> 'a1
    infer_ppal_type **)

let infer_abs the_PTS the_algos fix_inference e a m =
  match fix_add_typ the_PTS the_algos fix_inference e a with
    | Dcl_ok ->
        (match fix_inference m (Cons ((Ax a), e)) __ with
           | Inl s ->
               (match s with
                  | Srt s0 ->
                      (match the_algos.pa_infer_axiom s0 with
                         | Some s1 -> Inl (Prod (a, s))
                         | None -> Inr (Lambda_topsort ((Abs (a, m)), s0)))
                  | _ -> Inl (Prod (a, s)))
           | Inr s -> Inr (Under (a, s)))
    | Dcl_fail err -> Inr err

(** val infer_prod :
    'a1 pTS_sub_spec -> 'a1 pTS_algos -> ('a1 term -> 'a1 env -> __ -> 'a1
    infer_ppal_type) -> 'a1 env -> 'a1 term -> 'a1 term -> 'a1
    infer_ppal_type **)

let infer_prod the_PTS the_algos fix_inference e a b =
  match fix_inference a e __ with
    | Inl x ->
        (match the_algos.pa_least_sort e x __ with
           | Some x0 ->
               (match fix_inference b (Cons ((Ax a), e)) __ with
                  | Inl x1 ->
                      (match the_algos.pa_least_sort (Cons ((Ax a), e)) x1 __ with
                         | Some x2 -> Inl (Srt
                             (the_algos.pa_infer_rule x0 x2))
                         | None -> Inr (Under (a, (Not_a_type (b, x1)))))
                  | Inr x1 -> Inr (Under (a, x1)))
           | None -> Inr (Not_a_type (a, x)))
    | Inr x -> Inr x

(** val full_ppal_type :
    'a1 pTS_sub_spec -> 'a1 pTS_algos -> 'a1 term -> 'a1 env -> 'a1
    infer_ppal_type **)

let rec full_ppal_type the_PTS the_algos t e =
  match t with
    | Srt s ->
        (match the_algos.pa_infer_axiom s with
           | Some x -> Inl (Srt x)
           | None -> Inr (Topsort s))
    | Ref n -> infer_ref the_PTS the_algos e n
    | Abs (a, m) ->
        infer_abs the_PTS the_algos (fun t0 e0 _ ->
          full_ppal_type the_PTS the_algos t0 e0) e a m
    | App (u, v) ->
        infer_app the_PTS the_algos (fun t0 e0 _ ->
          full_ppal_type the_PTS the_algos t0 e0) e u v
    | Prod (a, b) ->
        infer_prod the_PTS the_algos (fun t0 e0 _ ->
          full_ppal_type the_PTS the_algos t0 e0) e a b

(** val tmp_add_typ :
    'a1 pTS_sub_spec -> 'a1 pTS_algos -> 'a1 env -> 'a1 term -> 'a1 decl_dec **)

let tmp_add_typ the_PTS the_algos e t =
  fix_add_typ the_PTS the_algos (fun x x0 _ ->
    full_ppal_type the_PTS the_algos x x0) e t

(** val tmp_check_typ_when_wf :
    'a1 pTS_sub_spec -> 'a1 pTS_algos -> 'a1 env -> 'a1 term -> 'a1 term ->
    'a1 check_dec **)

let tmp_check_typ_when_wf the_PTS the_algos e t t0 =
  fix_chk_wk the_PTS the_algos (fun x x0 _ ->
    full_ppal_type the_PTS the_algos x x0) e t t0

(** val full_type_checker :
    'a1 pTS_sub_spec -> 'a1 pTS_algos -> 'a1 pTS_TC **)

let full_type_checker the_PTS the_algos =
  { ptc_inf_ppal_type = (fun e t _ -> full_ppal_type the_PTS the_algos t e);
    ptc_chk_typ = (fun e t t0 _ ->
    if is_a_sort t0
    then tmp_check_typ_when_wf the_PTS the_algos e t t0
    else (match tmp_add_typ the_PTS the_algos e t0 with
            | Dcl_ok -> tmp_check_typ_when_wf the_PTS the_algos e t t0
            | Dcl_fail err -> Chk_fail err)); ptc_add_typ = (fun x x0 _ ->
    tmp_add_typ the_PTS the_algos x x0); ptc_add_def = (fun e t t0 _ ->
    match tmp_add_typ the_PTS the_algos e t0 with
      | Dcl_ok ->
          (match tmp_check_typ_when_wf the_PTS the_algos e t t0 with
             | Chk_ok -> Dcl_ok
             | Chk_fail x -> Dcl_fail x)
      | Dcl_fail x -> Dcl_fail x); ptc_chk_wk = (fun x x0 x1 _ _ ->
    tmp_check_typ_when_wf the_PTS the_algos x x0 x1); ptc_chk_wft =
    (fun x x0 _ ->
    if is_a_sort x0
    then Wft_ok
    else (match tmp_add_typ the_PTS the_algos x x0 with
            | Dcl_ok -> Wft_ok
            | Dcl_fail err -> Wft_fail err)) }

(** val r_rt_basic_rule : 'a1 basic_rule -> 'a1 basic_rule **)

let r_rt_basic_rule = function
  | Build_Basic_rule -> Build_Basic_rule

(** val union_basic_rule :
    'a1 basic_rule -> 'a1 basic_rule -> 'a1 basic_rule **)

let union_basic_rule x x0 =
  let Build_Basic_rule = x in let Build_Basic_rule = x0 in Build_Basic_rule

(** val canonical_subtyping : 'a1 basic_rule -> 'a1 subtyping_rule **)

let canonical_subtyping x =
  r_rt_basic_rule x

(** val cR_WHNF_convert_hn :
    ('a1 -> 'a1 -> decide) -> 'a1 basic_rule -> ('a1 env -> 'a1 term -> __ ->
    'a1 term sig2) -> 'a1 env -> 'a1 term -> 'a1 term -> decide **)

let cR_WHNF_convert_hn eq_sort_dec the_Rule whnf0 e x y =
  let rec f x0 x1 x2 _ _ =
    match x1 with
      | Srt x3 -> (match x2 with
                     | Srt s -> eq_sort_dec x3 s
                     | _ -> false)
      | Ref x3 -> (match x2 with
                     | Ref n -> eq_nat_dec x3 n
                     | _ -> false)
      | Abs (a, m) ->
          (match x2 with
             | Abs (t, t0) ->
                 if f x0 (whnf0 x0 a __) (whnf0 x0 t __) __ __
                 then f (Cons ((Ax t), x0)) (whnf0 (Cons ((Ax t), x0)) m __)
                        (whnf0 (Cons ((Ax t), x0)) t0 __) __ __
                 else false
             | _ -> false)
      | App (u0, v0) ->
          (match x2 with
             | App (t, t0) ->
                 if f x0 (whnf0 x0 u0 __) (whnf0 x0 t __) __ __
                 then f x0 (whnf0 x0 v0 __) (whnf0 x0 t0 __) __ __
                 else false
             | _ -> false)
      | Prod (a, b) ->
          (match x2 with
             | Prod (t, t0) ->
                 if f x0 (whnf0 x0 a __) (whnf0 x0 t __) __ __
                 then f (Cons ((Ax t), x0)) (whnf0 (Cons ((Ax t), x0)) b __)
                        (whnf0 (Cons ((Ax t), x0)) t0 __) __ __
                 else false
             | _ -> false)
  in f e x y __ __

type 'sort cTS_spec =
  'sort basic_rule
  (* singleton inductive, whose constructor was Build_CTS_spec *)

(** val head_reduct : 'a1 cTS_spec -> 'a1 basic_rule **)

let head_reduct cTS_spec0 =
  cTS_spec0

type 'sort subtype_dec_CTS = { scts_whnf : ('sort env -> 'sort term -> __ ->
                                           'sort term sig2);
                               scts_convert_hn : ('sort env -> 'sort term ->
                                                 'sort term -> __ -> __ ->
                                                 decide);
                               scts_rt_univ_dec : ('sort -> 'sort -> decide) }

(** val scts_rt_univ_dec :
    'a1 cTS_spec -> 'a1 subtype_dec_CTS -> 'a1 -> 'a1 -> decide **)

let scts_rt_univ_dec _ x = x.scts_rt_univ_dec

(** val cR_WHNF_inv_cumul_dec :
    'a1 cTS_spec -> 'a1 subtype_dec_CTS -> 'a1 env -> 'a1 term -> 'a1 term ->
    decide **)

let cR_WHNF_inv_cumul_dec the_CTS the_scts e x y =
  let whnf0 = fun x0 x1 -> the_scts.scts_whnf x0 x1 __ in
  let rec f x0 x1 x2 _ _ =
    match x1 with
      | Srt x3 ->
          (match x2 with
             | Srt s -> the_scts.scts_rt_univ_dec x3 s
             | _ -> false)
      | Ref n -> the_scts.scts_convert_hn x0 (Ref n) x2 __ __
      | Abs (t, t0) -> the_scts.scts_convert_hn x0 (Abs (t, t0)) x2 __ __
      | App (t, t0) -> the_scts.scts_convert_hn x0 (App (t, t0)) x2 __ __
      | Prod (a, b) ->
          (match x2 with
             | Prod (t, t0) ->
                 if f x0 (whnf0 x0 t) (whnf0 x0 a) __ __
                 then f (Cons ((Ax t), x0)) (whnf0 (Cons ((Ax t), x0)) b)
                        (whnf0 (Cons ((Ax t), x0)) t0) __ __
                 else false
             | _ -> false)
  in f e x y __ __

(** val cR_WHNF_cumul_dec :
    'a1 cTS_spec -> 'a1 subtype_dec_CTS -> 'a1 env -> 'a1 term -> 'a1 term ->
    decide **)

let cR_WHNF_cumul_dec the_CTS the_scts e x y =
  let whnf0 = fun x0 x1 -> the_scts.scts_whnf x0 x1 __ in
  cR_WHNF_inv_cumul_dec the_CTS the_scts e (whnf0 e x) (whnf0 e y)

type 'sort norm_sound_CTS = { ncts_axiom : ('sort -> 'sort ppal_dec);
                              ncts_rule : ('sort -> 'sort -> 'sort sig2) }

(** val ncts_axiom :
    'a1 cTS_spec -> 'a1 norm_sound_CTS -> 'a1 -> 'a1 ppal_dec **)

let ncts_axiom _ x = x.ncts_axiom

(** val ncts_rule :
    'a1 cTS_spec -> 'a1 norm_sound_CTS -> 'a1 -> 'a1 -> 'a1 sig2 **)

let ncts_rule _ x = x.ncts_rule

(** val cts_prim_algos :
    'a1 cTS_spec -> 'a1 subtype_dec_CTS -> 'a1 norm_sound_CTS -> 'a1
    pTS_algos **)

let cts_prim_algos the_CTS the_scts the_ncts =
  { pa_lift = (fun x x0 -> lift x x0); pa_subst = (fun x x0 -> 
    subst x x0); pa_infer_axiom = (fun x -> the_ncts.ncts_axiom x);
    pa_least_sort = (fun x x0 _ ->
    match the_scts.scts_whnf x x0 __ with
      | Srt s -> Some s
      | _ -> None); pa_infer_rule = (fun x x0 -> the_ncts.ncts_rule x x0);
    pa_least_prod = (fun x x0 _ ->
    match the_scts.scts_whnf x x0 __ with
      | Prod (t0, t1) -> Some (Pair (t0, t1))
      | _ -> None); pa_le_type_dec = (fun e u v _ _ ->
    cR_WHNF_cumul_dec the_CTS the_scts e u v) }

(** val app_list : 'a1 term list -> 'a1 term -> 'a1 term **)

let rec app_list args t =
  match args with
    | Nil -> t
    | Cons (hd, tl) -> app_list tl (App (t, hd))

(** val beta_rule : 'a1 basic_rule **)

let beta_rule =
  Build_Basic_rule

(** val delta_rule : 'a1 basic_rule **)

let delta_rule =
  Build_Basic_rule

(** val delta_reduce : nat -> 'a1 env -> 'a1 term option **)

let delta_reduce n e =
  match list_item e n with
    | Some s ->
        (match s with
           | Ax t -> None
           | Def (d, t) -> Some (lift (S n) d))
    | None -> None

(** val beta_delta_rule : 'a1 basic_rule **)

let beta_delta_rule =
  union_basic_rule beta_rule delta_rule

(** val bd_whnf_rec :
    'a1 env -> 'a1 term -> 'a1 term list -> 'a1 term sig2 **)

let rec bd_whnf_rec x x0 x1 =
  match x0 with
    | Srt s -> app_list x1 (Srt s)
    | Ref n ->
        (match delta_reduce n x with
           | Some x2 -> bd_whnf_rec x x2 x1
           | None -> app_list x1 (Ref n))
    | Abs (t0, t1) ->
        (match x1 with
           | Nil -> Abs (t0, t1)
           | Cons (t2, l) -> bd_whnf_rec x (subst t2 t1) l)
    | App (t0, t1) -> bd_whnf_rec x t0 (Cons (t1, x1))
    | Prod (t0, t1) -> app_list x1 (Prod (t0, t1))

(** val beta_delta_whnf : 'a1 env -> 'a1 term -> 'a1 term sig2 **)

let beta_delta_whnf e t =
  bd_whnf_rec e t Nil

type gen_sort =
  | Gprop
  | Gset
  | Gtype of nat
  | Gtypeset of nat

type calc =
  | Pos
  | Neg

type srt_v6 =
  | Sprop of calc
  | Stype of nat

(** val calc_dec : calc -> calc -> decide **)

let calc_dec c c' =
  match c with
    | Pos -> (match c' with
                | Pos -> true
                | Neg -> false)
    | Neg -> (match c' with
                | Pos -> false
                | Neg -> true)

(** val v6_sort_dec : srt_v6 -> srt_v6 -> decide **)

let v6_sort_dec s s' =
  match s with
    | Sprop c ->
        (match s' with
           | Sprop c0 -> calc_dec c c0
           | Stype n -> false)
    | Stype n ->
        (match s' with
           | Sprop c -> false
           | Stype n0 -> eq_nat_dec n n0)

(** val univ_v6_dec : srt_v6 -> srt_v6 -> decide **)

let univ_v6_dec s s' =
  match s with
    | Sprop c ->
        (match s' with
           | Sprop c' -> calc_dec c c'
           | Stype n -> true)
    | Stype n ->
        (match s' with
           | Sprop c -> false
           | Stype n' -> le_gt_dec n n')

(** val v6_inf_axiom : srt_v6 -> srt_v6 **)

let v6_inf_axiom = function
  | Sprop c -> Stype O
  | Stype n -> Stype (S n)

(** val v6_inf_rule : srt_v6 -> srt_v6 -> srt_v6 sig2 **)

let v6_inf_rule x1 x2 =
  match x1 with
    | Sprop c -> x2
    | Stype n ->
        (match x2 with
           | Sprop c' -> Sprop c'
           | Stype n' -> Stype (max_nat n n'))

(** val sort_of_gen : gen_sort -> srt_v6 exc **)

let sort_of_gen = function
  | Gprop -> value (Sprop Neg)
  | Gset -> value (Sprop Pos)
  | Gtype n -> value (Stype n)
  | Gtypeset n -> error

(** val gen_of_sort : srt_v6 -> gen_sort **)

let gen_of_sort = function
  | Sprop c -> (match c with
                  | Pos -> Gset
                  | Neg -> Gprop)
  | Stype n -> Gtype n

type trm_v6 = srt_v6 term

type env_v6 = srt_v6 env

(** val v6 : srt_v6 cTS_spec **)

let v6 =
  beta_delta_rule

(** val v6_pts : srt_v6 pTS_sub_spec **)

let v6_pts =
  canonical_subtyping Build_Basic_rule

(** val whnf : env_v6 -> trm_v6 -> trm_v6 sig2 **)

let whnf e t =
  beta_delta_whnf e t

(** val bd_conv_hnf : env_v6 -> trm_v6 -> trm_v6 -> decide **)

let bd_conv_hnf e x y =
  cR_WHNF_convert_hn v6_sort_dec beta_delta_rule (fun x0 x1 _ -> 
    whnf x0 x1) e x y

(** val v6_is_subtype_dec : srt_v6 subtype_dec_CTS **)

let v6_is_subtype_dec =
  { scts_whnf = (fun x x0 _ -> whnf x x0); scts_convert_hn =
    (fun x x0 x1 _ _ -> bd_conv_hnf x x0 x1); scts_rt_univ_dec =
    univ_v6_dec }

(** val v6_is_norm_sound : srt_v6 norm_sound_CTS **)

let v6_is_norm_sound =
  { ncts_axiom = (fun s -> Some (v6_inf_axiom s)); ncts_rule = v6_inf_rule }

(** val infer_type : env_v6 -> trm_v6 -> srt_v6 infer_ppal_type **)

let infer_type e t =
  (full_type_checker (canonical_subtyping Build_Basic_rule)
    (cts_prim_algos v6 v6_is_subtype_dec v6_is_norm_sound)).ptc_inf_ppal_type
    e t __

(** val check_wf_type : env_v6 -> trm_v6 -> srt_v6 wft_dec **)

let check_wf_type e t =
  (full_type_checker (canonical_subtyping Build_Basic_rule)
    (cts_prim_algos v6 v6_is_subtype_dec v6_is_norm_sound)).ptc_chk_wft e t
    __

(** val check_type : env_v6 -> trm_v6 -> trm_v6 -> srt_v6 check_dec **)

let check_type e t t0 =
  (full_type_checker (canonical_subtyping Build_Basic_rule)
    (cts_prim_algos v6 v6_is_subtype_dec v6_is_norm_sound)).ptc_chk_typ e t
    t0 __

(** val add_type : env_v6 -> trm_v6 -> srt_v6 decl_dec **)

let add_type e t =
  (full_type_checker (canonical_subtyping Build_Basic_rule)
    (cts_prim_algos v6 v6_is_subtype_dec v6_is_norm_sound)).ptc_add_typ e t
    __

(** val add_def : env_v6 -> trm_v6 -> trm_v6 -> srt_v6 decl_dec **)

let add_def e t t0 =
  (full_type_checker (canonical_subtyping Build_Basic_rule)
    (cts_prim_algos v6 v6_is_subtype_dec v6_is_norm_sound)).ptc_add_def e t
    t0 __

