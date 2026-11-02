(**************************************************************************)
(*                                                                        *)
(*     Alt-Ergo: The SMT Solver For Software Verification                 *)
(*     Copyright (C) --- OCamlPro SAS                                     *)
(*                                                                        *)
(*     This file is distributed under the terms of OCamlPro               *)
(*     Non-Commercial Purpose License, version 1.                         *)
(*                                                                        *)
(*     As an exception, Alt-Ergo Club members at the Gold level can       *)
(*     use this file under the terms of the Apache Software License       *)
(*     version 2.0.                                                       *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     The Alt-Ergo theorem prover                                        *)
(*                                                                        *)
(*     Sylvain Conchon, Evelyne Contejean, Francois Bobot                 *)
(*     Mohamed Iguernelala, Stephane Lescuyer, Alain Mebsout              *)
(*                                                                        *)
(*     CNRS - INRIA - Universite Paris Sud                                *)
(*                                                                        *)
(*     ---------------------------------------------------------------    *)
(*                                                                        *)
(*     More details can be found in the directory licenses/               *)
(*                                                                        *)
(**************************************************************************)

module A = Xliteral
module X = Shostak.Combine
module Ex = Explanation
module E = Expr
module LX = Uf.LX
module XMap = Shostak.MXH
module XSet = Shostak.SXH

(* The theory of arrays with extensionality, using global domains on the
   representatives of the union-find:

   - known values: [a[i] = v], from [(select a i)] and [a = (store _ i v)]

   - edges: [a --i-- b], from [b = (store a i _)] or [a = (store b i _)]

   [a[k] = v] gives [b[k] = v] through [a --i-- b] if [k <> i], otherwise a case
   split on [k = i]. Two values [a[k] = v] and [a[k] = w] give [v = w]. *)

let src = Logs.Src.create ~doc:"Arrays_rel" __MODULE__

module Log = (val Logs.src_log src : Logs.LOG)

let timer = Timers.M_Arrays

type eq = X.r * X.r * Ex.t

let add_loc k a locs =
  XMap.update k
    (function None -> Some (XSet.singleton a) | Some s -> Some (XSet.add a s))
    locs

module Domain = struct
  type t =
    { values : (X.r * Ex.t) XMap.t XMap.t;
      (* [a -> k -> (v, ex)]: [a[k] = v] with the explanation [ex]. *)
      edges : Ex.t XMap.t XMap.t XMap.t;
      (* [a -> b -> i -> ex]: the edge [a --i-- b] with the explanation [ex].
         The edges are stored in both directions. *)
      value_locs : XSet.t XMap.t;
      (* Map of indices to the arrays that have a value at this index. *)
      edge_locs : XSet.t XMap.t;
      (* Map of indices to the arrays that have an edge labelled by this
         index. *)
      split_locs : LX.Set.t XMap.t;
      (* Map of indices to the case splits on this index. *)
      dirty : XSet.t;
      (* Arrays whose values have to be propagated again through their edges. *)
      split_todo : LX.Set.t;
      (* Case splits whose indices have been merged with others. *)
      eqs : eq list (* Deduced equalities that have not been propagated yet. *)
    }

  type _ Uf.id += Id : t Uf.id

  let empty =
    { values = XMap.empty;
      edges = XMap.empty;
      value_locs = XMap.empty;
      edge_locs = XMap.empty;
      split_locs = XMap.empty;
      dirty = XSet.empty;
      split_todo = LX.Set.empty;
      eqs = []
    }

  let pp ppf t =
    let pp_value ppf (k, (v, _)) = Fmt.pf ppf "[%a] = %a" X.print k X.print v in
    let pp_values ppf (a, m) =
      Fmt.pf ppf "%a%a" X.print a
        Fmt.(iter_bindings ~sep:sp XMap.iter pp_value)
        m
    in
    Fmt.pf ppf "@[<v>Arrays values:@,  %a@]"
      Fmt.(iter_bindings ~sep:cut XMap.iter pp_values)
      t.values

  (* Indices and arrays can be of any type. *)
  let filter_ty _ = true

  let init _ t = t

  exception Inconsistent of Ex.t

  let values_of a t =
    Option.value ~default:XMap.empty (XMap.find_opt a t.values)

  (* Add the value [a[k] = v]. If [a] already has a value at [k], deduce the
     equality of the two values instead. Returns [true] if the known value is
     new. *)
  let add_value a k ((v, ex) as rd) t =
    let m = values_of a t in
    match XMap.find k m with
    | v', ex' -> { t with eqs = (v, v', Ex.union ex ex') :: t.eqs }, false
    | exception Not_found ->
      ( { t with
          values = XMap.add a (XMap.add k rd m) t.values;
          value_locs = add_loc k a t.value_locs
        },
        true )

  (* Add the edge [a --i-- b] in both directions. *)
  let add_edge a i b ex t =
    let add_dir a b edges =
      let am = Option.value ~default:XMap.empty (XMap.find_opt a edges) in
      let im = Option.value ~default:XMap.empty (XMap.find_opt b am) in
      if XMap.mem i im
      then edges
      else XMap.add a (XMap.add b (XMap.add i ex im) am) edges
    in
    if X.equal a b
    then t
    else
      { t with
        edges = add_dir a b (add_dir b a t.edges);
        edge_locs = add_loc i a (add_loc i b t.edge_locs)
      }

  (* The index [rr] is replaced by [nrr]: the values at [rr], the edges labelled
     by [rr] and the case splits on [rr] are moved to [nrr]. *)
  let subst_index ~ex rr nrr t =
    let t =
      match XMap.find rr t.value_locs with
      | exception Not_found -> t
      | arrs ->
        let t = { t with value_locs = XMap.remove rr t.value_locs } in
        XSet.fold
          (fun a t ->
            let m = values_of a t in
            match XMap.find rr m with
            | exception Not_found -> t
            | v, ex_v ->
              let t =
                { t with
                  values = XMap.add a (XMap.remove rr m) t.values;
                  dirty = XSet.add a t.dirty
                }
              in
              fst (add_value a nrr (v, Ex.union ex ex_v) t))
          arrs t
    in
    let t =
      match XMap.find rr t.edge_locs with
      | exception Not_found -> t
      | arrs ->
        let edges =
          XSet.fold
            (fun a edges ->
              match XMap.find a edges with
              | exception Not_found -> edges
              | am ->
                let am =
                  XMap.map
                    (fun im ->
                      match XMap.find rr im with
                      | exception Not_found -> im
                      | e -> XMap.add nrr (Ex.union ex e) (XMap.remove rr im))
                    am
                in
                XMap.add a am edges)
            arrs t.edges
        in
        { t with
          edges;
          edge_locs = XSet.fold (add_loc nrr) arrs (XMap.remove rr t.edge_locs);
          dirty = XSet.union arrs t.dirty
        }
    in
    match XMap.find rr t.split_locs with
    | exception Not_found -> t
    | lits ->
      let split_locs = XMap.remove rr t.split_locs in
      let s =
        Option.value ~default:LX.Set.empty (XMap.find_opt nrr split_locs)
      in
      { t with
        split_locs = XMap.add nrr (LX.Set.union lits s) split_locs;
        split_todo = LX.Set.union lits t.split_todo
      }

  (* The array [rr] is replaced by [nrr]: its values and edges are moved to
     [nrr]. *)
  let subst_array ~ex rr nrr t =
    let t =
      match XMap.find rr t.values with
      | exception Not_found -> t
      | m ->
        let t = { t with values = XMap.remove rr t.values } in
        XMap.fold
          (fun k (v, ex_v) t -> fst (add_value nrr k (v, Ex.union ex ex_v) t))
          m t
    in
    let t =
      match XMap.find rr t.edges with
      | exception Not_found -> t
      | am ->
        let t = { t with edges = XMap.remove rr t.edges } in
        XMap.fold
          (fun b im t ->
            let bm = XMap.remove rr (XMap.find b t.edges) in
            let t = { t with edges = XMap.add b bm t.edges } in
            XMap.fold (fun i e t -> add_edge nrr i b (Ex.union ex e) t) im t)
          am t
    in
    if XMap.mem nrr t.values && XMap.mem nrr t.edges
    then { t with dirty = XSet.add nrr t.dirty }
    else t

  let subst ~ex rr nrr t =
    (* A value can be used both as an index and as an array if we have arrays
       indexed by arrays. *)
    subst_array ~ex rr nrr (subst_index ~ex rr nrr t)
end

let get_domain uf = Uf.GlobalDomains.find (module Domain) (Uf.domains uf)

let set_domain uf dom = Uf.GlobalDomains.add (module Domain) dom (Uf.domains uf)

(* The value [a[k] = v] with its explanation. *)
type value =
  { a : X.r;
    k : X.r;
    v : X.r;
    ex : Ex.t
  }

type t =
  { splits : value list LX.Map.t;
    (* Map of the case splits [k = i] to the values to add if [k <> i]. *)
    order : LX.t Util.MI.t;
    (* The case splits by creation order. *)
    stamps : int LX.Map.t;
    (* The position of each case split in [order], to remove it. *)
    next_stamp : int;
    (* The position of the next case split in [order]. *)
    new_terms : E.Set.t
        (* Terms produced by the theory that are sent to the instantiation
           engine. *)
  }

let empty uf =
  ( { splits = LX.Map.empty;
      order = Util.MI.empty;
      stamps = LX.Map.empty;
      next_stamp = 0;
      new_terms = E.Set.empty
    },
    (* The domain is only registered when the first select or store term is
       added: without arrays, the union-find does not update it. *)
    Uf.domains uf )

let same_class uf r1 r2 =
  X.equal r1 r2 || X.equal (fst (Uf.find_r uf r1)) (fst (Uf.find_r uf r2))

(* [r1] and [r2] are distinct if their union is inconsistent. *)
let are_distinct uf r1 r2 =
  let r1, ex1 = Uf.find_r uf r1 in
  let r2, ex2 = Uf.find_r uf r2 in
  try
    ignore (Uf.union uf r1 r2 (Ex.union ex1 ex2));
    Th_util.Unknown
  with Ex.Inconsistent (ex, classes) -> Th_util.Entailed { ex; classes }

let add_split env (dom : Domain.t) k i value =
  let lit = LX.mk_eq k i in
  match LX.Map.find lit env.splits with
  | ps -> { env with splits = LX.Map.add lit (value :: ps) env.splits }, dom
  | exception Not_found ->
    let n = env.next_stamp in
    let add_lit r locs =
      XMap.update r
        (function
          | None -> Some (LX.Set.singleton lit)
          | Some s -> Some (LX.Set.add lit s))
        locs
    in
    ( { env with
        splits = LX.Map.add lit [value] env.splits;
        order = Util.MI.add n lit env.order;
        stamps = LX.Map.add lit n env.stamps;
        next_stamp = n + 1
      },
      { dom with split_locs = add_lit k (add_lit i dom.split_locs) } )

let remove_split env lit =
  match LX.Map.find lit env.stamps with
  | exception Not_found -> env
  | n ->
    { env with
      splits = LX.Map.remove lit env.splits;
      order = Util.MI.remove n env.order;
      stamps = LX.Map.remove lit env.stamps
    }

(* The term [(select b k)] is given to the instantiation engine. *)
let add_new_term uf env b k =
  (* A term of the class of [r]. *)
  let term r =
    match X.term_extract r with
    | Some t, _ -> Some t
    | None, _ -> E.Set.min_elt_opt (Uf.rclass_of uf r)
  in
  match term b, term k with
  | Some b, Some k ->
    { env with new_terms = E.Set.add (E.ArraysEx.select b k) env.new_terms }
  | _ -> env

(* Add the value [b[k] = v] and push it on [todo] if it is new. *)
let add_value uf (env, dom, todo) b k v ex =
  let b, ex_b = Uf.find_r uf b in
  let k, ex_k = Uf.find_r uf k in
  let ex = Ex.union ex (Ex.union ex_b ex_k) in
  let dom, is_new = Domain.add_value b k (v, ex) dom in
  if is_new
  then add_new_term uf env b k, dom, { a = b; k; v; ex } :: todo
  else env, dom, todo

(* Propagate the value [a[k] = v] through the edge [a --i-- b]. *)
(* For the edge [a --i-- b] and the value [a[i] = v]: if [b[i] = v] too,
   then [a = b], since [a] and [b] agree on all the other indices. *)
let check_edge uf (env, (dom : Domain.t), todo) { a; k = i; v; ex } b eex =
  let i, ex_i = Uf.find_r uf i in
  match XMap.find i (Domain.values_of b dom) with
  | exception Not_found -> env, dom, todo
  | w, ex_w ->
    let v, ex_v = Uf.find_r uf v in
    let w, ex_w' = Uf.find_r uf w in
    if X.equal v w && not (same_class uf a b)
    then
      let ex = List.fold_left Ex.union ex [ex_i; ex_w; ex_v; ex_w'; eex] in
      env, { dom with eqs = (a, b, ex) :: dom.eqs }, todo
    else env, dom, todo

let cross uf acc ({ k; v; ex; _ } as value) b i eex =
  if same_class uf k i
  then check_edge uf acc value b eex
  else
    let ex = Ex.union ex eex in
    match are_distinct uf k i with
    | Entailed { ex = ex_d; _ } -> add_value uf acc b k v (Ex.union ex ex_d)
    | Unknown ->
      let env, dom, todo = acc in
      let env, dom = add_split env dom k i { a = b; k; v; ex } in
      (* As the value may only be propagated during the case-split search of the
         theory, its term is given to the instantiation engine now. *)
      add_new_term uf env b k, dom, todo

(* Propagate the values of [todo] through the edges of their arrays. *)
let rec propagate uf (env, (dom : Domain.t), todo) =
  match todo with
  | [] -> env, dom
  | ({ a; _ } as value) :: todo ->
    let am = Option.value ~default:XMap.empty (XMap.find_opt a dom.edges) in
    propagate uf
      (XMap.fold
         (fun b im acc ->
           XMap.fold (fun i eex acc -> cross uf acc value b i eex) im acc)
         am (env, dom, todo))

(* Propagate again the values of the arrays whose values or edges changed. *)
let process_dirty uf env (dom : Domain.t) =
  let todo =
    XSet.fold
      (fun a todo ->
        let a, _ = Uf.find_r uf a in
        XMap.fold
          (fun k (v, ex) todo -> { a; k; v; ex } :: todo)
          (Domain.values_of a dom) todo)
      dom.dirty []
  in
  propagate uf (env, { dom with dirty = XSet.empty }, todo)

(* Decide the case splits [lits] whose indices are now equal or distinct. *)
let resolve_splits uf env dom lits =
  propagate uf
    (LX.Set.fold
       (fun lit ((env, dom, todo) as acc) ->
         match LX.Map.find lit env.splits, LX.view lit with
         | exception Not_found -> acc
         | ps, A.Eq (k, i) -> (
           if same_class uf k i
           then remove_split env lit, dom, todo
           else
             match are_distinct uf k i with
             | Th_util.Entailed { ex; _ } ->
               List.fold_left
                 (fun acc { a = b; k; v; ex = ex_p } ->
                   add_value uf acc b k v (Ex.union ex ex_p))
                 (remove_split env lit, dom, todo)
                 ps
             | Th_util.Unknown -> acc)
         | _ -> acc)
       lits (env, dom, []))

(* The case splits that may be decided by the literals of [la]. *)
let decided_splits uf (dom : Domain.t) la =
  let locs acc r =
    match XMap.find (fst (Uf.find_r uf r)) dom.split_locs with
    | s -> LX.Set.union s acc
    | exception Not_found -> acc
  in
  List.fold_left
    (fun acc (a, _, _, _) ->
      match a with
      | A.Eq _ -> LX.Set.add (LX.make a) acc
      | A.Distinct (false, l) -> List.fold_left locs acc l
      | _ -> acc)
    dom.split_todo la

let flush_eqs uf (dom : Domain.t) =
  let eqs =
    List.filter (fun (v, w, _) -> not (same_class uf v w)) (List.rev dom.eqs)
  in
  eqs, { dom with eqs = [] }

(* For each disequality [r <> s] where [r] and [s] are two arrays, we produce
   the formula: exists i:ty. (select r i) <> (select s i), where [ty] denotes
   the type of indices of [r] and [s]. *)
let extensionality_pair (env, acc) dep r s =
  match X.type_info r, X.term_extract r, X.term_extract s with
  | Ty.Tfarray (ty, _), (Some t1, _), (Some t2, _) ->
    let i = E.fresh_name ty in
    let g1 = E.ArraysEx.select t1 i in
    let g2 = E.ArraysEx.select t2 i in
    let d = E.mk_distinct ~iff:false [g1; g2] in
    let env =
      { env with new_terms = E.Set.add g2 (E.Set.add g1 env.new_terms) }
    in
    env, (Literal.LTerm d, dep, Th_util.Other) :: acc
  | _ -> env, acc

let extensionality acc (a, _, dep, _) =
  match a with
  | A.Distinct (false, (_ :: _ :: _ as l)) ->
    let rec aux acc = function
      | [] | [_] -> acc
      | r :: rl ->
        aux
          (List.fold_left (fun acc s -> extensionality_pair acc dep r s) acc rl)
          rl
    in
    aux acc l
  | _ -> acc

let assume env uf la =
  let dom = get_domain uf in
  let env, domains, l =
    if XMap.is_empty dom.values && LX.Map.is_empty env.splits
    then
      (* No select or store terms: nothing to propagate. *)
      env, Uf.domains uf, []
    else
      let env, dom = process_dirty uf env dom in
      let lits = decided_splits uf dom la in
      let env, dom =
        resolve_splits uf env { dom with split_todo = LX.Set.empty } lits
      in
      let eqs, dom = flush_eqs uf dom in
      let l =
        List.rev_map
          (fun (v, w, ex) -> Literal.LSem (LX.mkv_eq v w), ex, Th_util.Other)
          eqs
      in
      env, set_domain uf dom, l
  in
  let env, l = List.fold_left extensionality (env, l) la in
  env, domains, { Sig_rel.assume = l; remove = [] }

let two = Numbers.Q.from_int 2

(* Split on the most recent case split [k = i]. *)
let case_split env _uf ~for_model:_ =
  match Util.MI.max_binding env.order with
  | _, lit ->
    Log.debug (fun k -> k "case split@ %a" LX.print lit);
    [LX.view lit, true, Th_util.CS (Th_util.Th_arrays, two)]
  | exception Not_found -> []

let optimizing_objective _env _uf _o = None

let query _ _ _ = Th_util.Unknown

(* Register the value and the edge of the select and store terms. *)
let add env uf r t =
  let register env dom =
    let { E.f; xs; _ } = E.term_view t in
    match f, xs with
    | Symbols.Op Select, [a; i] ->
      let v, ex_v = Uf.find_r uf r in
      let ra, ex_a = Uf.find uf a in
      let ri, ex_i = Uf.find uf i in
      let ex = Ex.union ex_v (Ex.union ex_a ex_i) in
      propagate uf (add_value uf (env, dom, []) ra ri v ex)
    | Symbols.Op Store, [a; i; v] ->
      let s, ex_s = Uf.find_r uf r in
      let ra, ex_a = Uf.find uf a in
      let ri, ex_i = Uf.find uf i in
      let rv, ex_v = Uf.find uf v in
      let env, dom, todo =
        add_value uf (env, dom, []) s ri rv (Ex.union ex_s (Ex.union ex_i ex_v))
      in
      let dom =
        Domain.add_edge ra ri s (Ex.union ex_a (Ex.union ex_i ex_s)) dom
      in
      (* The values of both arrays are propagated through the new edge. *)
      let dom = { dom with dirty = XSet.add ra (XSet.add s dom.dirty) } in
      let env, dom = propagate uf (env, dom, todo) in
      process_dirty uf env dom
    | _ -> env, dom
  in
  match E.term_view t with
  | { f = Op (Select | Store); _ } ->
    let env, dom = process_dirty uf env (get_domain uf) in
    let env, dom = register env dom in
    let eqs, dom = flush_eqs uf dom in
    env, set_domain uf dom, List.map (fun (v, w, ex) -> LX.mkv_eq v w, ex) eqs
  | _ -> env, Uf.domains uf, []

let new_terms env = env.new_terms

let instantiate ~do_syntactic_matching:_ _ env _ _ = env, []

let assume_th_elt t th_elt _ =
  match th_elt.Expr.extends with
  | Util.Arrays -> failwith "This Theory does not support theories extension"
  | _ -> t
