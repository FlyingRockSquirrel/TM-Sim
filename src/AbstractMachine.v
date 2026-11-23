From Stdlib Require Export Nat List Lia StrictProp.          
From stdpp Require Export gmap. 

Set Allow StrictProp.

Inductive HTerm :=
| HVar : nat -> HTerm
| HApp : HTerm -> HTerm -> HTerm
| HAbs : nat -> HTerm -> HTerm
| HAddr : nat -> HTerm.

Inductive Term :=
| Var : nat -> Term
| App : Term -> Term -> Term
| Abs : nat -> Term -> Term.

Fixpoint subst substin substout body :=
match body with
| HVar i =>
  if Nat.eqb i substout then substin else HVar i
| HApp t u => HApp (subst substin substout t) (subst substin substout u)
| HAbs n t => 
  if Nat.eqb n substout then HAbs n t 
    else HAbs n (subst substin substout t)
| HAddr n => HAddr n
end. 

Fixpoint is_closed_aux (vars : list nat) (t : HTerm) : Prop := 
  match t with
  | HVar n => In n vars
  | HApp t1 t2 => is_closed_aux vars t1 /\ is_closed_aux vars t2
  | HAbs n t' => is_closed_aux (n::vars) t'
  | HAddr _ => True
  end.  

Definition is_closed (t : HTerm) : Prop :=
  is_closed_aux nil t. 

Fixpoint t_subst substin substout body :=
match body with
| Var i =>
  if Nat.eqb i substout then substin else Var i
| App t u => App (t_subst substin substout t) (t_subst substin substout u)
| Abs n t => 
  if Nat.eqb n substout then Abs n t 
    else Abs n (t_subst substin substout t)
end. 

Lemma subst_is_closed_noop_aux : 
  forall t n t' aux, 
    ~In n aux ->
    is_closed_aux aux t ->
    subst t' n t = t.
Proof. 
  induction t; intros n' t' aux H H0.
  - simpl in *.
    destruct (n =? n') eqn:neq; simpl; try reflexivity. 
    eapply Nat.eqb_eq in neq. subst.
    exfalso. apply H. apply H0.
  - simpl in *.
    rewrite (IHt1 _ _ aux); try rewrite (IHt2 _ _ aux); try assumption; try tauto.
  - simpl in *. destruct (n =? n') eqn:neq; try reflexivity.
    eapply Nat.eqb_neq in neq.
    rewrite (IHt _ _ (n :: aux)); try reflexivity.
    + unfold not. intros. destruct H1; try congruence.
    + assumption.
  - simpl. reflexivity.        
Qed. 

Lemma subst_is_closed_noop :
  forall t n t', 
    is_closed t ->
      subst t' n t = t.
Proof.
  intros. eapply (subst_is_closed_noop_aux _ _ _ nil).
  - simpl. intros H0. inversion H0.
  - eapply H.
Qed.  

Fixpoint t_step t : option Term :=
  match t with
  | App (Abs n t1) t2 => Some (t_subst t2 n t1)
  | App t1 t2 =>
    match t_step t1 with
    | Some t1' => Some (App t1' t2)
    | None => None
    end
  | _ => None
  end.

Fixpoint HTunfold substin n body :=
match body with
| HVar i => HVar i
| HApp t u => HApp (HTunfold substin n t) (HTunfold substin n u)
| HAbs n' t => HAbs n' (HTunfold substin n t)
| HAddr n' => 
  if Nat.eqb n n' then substin else HAddr n'
end. 

Fixpoint term_to_hterm (t : Term) : HTerm :=
  match t with
  | Var n => HVar n
  | App t1 t2 => HApp (term_to_hterm t1) (term_to_hterm t2)
  | Abs n t => HAbs n (term_to_hterm t)
  end.

Fixpoint hterm_to_term (t : HTerm) : option Term :=
  match t with
  | HVar n => Some (Var n)
  | HApp t1 t2 => 
    match (hterm_to_term t1, hterm_to_term t2) with
    | (Some t1', Some t2') => Some (App t1' t2')
    | _ => None
    end
  | HAbs n t =>
    match (hterm_to_term t) with
    | Some t' => Some (Abs n t')
    | None => None
    end
  | _ => None
  end.

Lemma term_to_hterm_roundtrip_noop :
  forall t, 
    hterm_to_term (term_to_hterm t) = Some t.
Proof. 
  induction t; simpl; intros.
  - reflexivity.
  - rewrite IHt1; rewrite IHt2. reflexivity.
  - rewrite IHt. reflexivity.
Qed.

Lemma hterm_to_term_roundtrip_noop : 
  forall t t', 
    hterm_to_term t = Some t' ->
    term_to_hterm t' = t.
Proof.
  induction t; intros; simpl in *.
  - inversion H; subst. simpl. reflexivity.
  - destruct (hterm_to_term t1) eqn:t1eq; try discriminate.
    destruct (hterm_to_term t2) eqn:t2eq; try discriminate.
    inversion H; subst.
    specialize (IHt1 _ eq_refl).
    specialize (IHt2 _ eq_refl).
    simpl. subst. congruence.
  - destruct (hterm_to_term t) eqn:teq; try discriminate.
    specialize (IHt _ eq_refl).
    inversion H; subst. simpl. reflexivity.
  - discriminate.
Qed.      


Global Instance HTerm_eq_dec : 
  EqDecision HTerm.
Proof.
  unfold EqDecision. intros. unfold Decision.
  revert x. revert y. 
  induction y; induction x; try (right; congruence).
  - destruct (PeanoNat.Nat.eq_dec n n0); [left|right]; congruence.
  - specialize (IHy1 x1). specialize (IHy2 x2). 
    destruct IHy1; destruct IHy2; try (right; congruence).
    left. congruence.
  - specialize (IHy x).
    destruct (PeanoNat.Nat.eq_dec n n0); [|right]; try congruence.
    subst.
    destruct IHy; [left | right]; try congruence.
  - destruct (PeanoNat.Nat.eq_dec n n0); [left|right]; congruence.
Qed. 


Lemma wf_dec (H : gmap nat (HTerm * nat)) : 
  forall nxt, 
  Decision (forall n, nxt <= n -> H !! n  = None).
Proof.
  intros. unfold Decision.
  pose proof set_Exists_dec (C := gset nat) (A := nat) (fun x => nxt <= x) (dom H).
  destruct H0.
  - right. unfold not. intros.
    unfold set_Exists in s.
    destruct s.
    specialize (H0 x).
    destruct H1.
    specialize (H0 H2).
    pose proof elem_of_dom H x.
    destruct H3.
    specialize (H3 H1).
    unfold is_Some in H3.
    destruct H3.
    congruence.
  - left. intros. unfold set_Exists in n. unfold not in n.
    pose proof not_elem_of_dom H n0.
    destruct H1. eapply H1. unfold not. intros. eapply n. exists n0. 
    split; tauto.
Qed.  

Record Heap := 
  { 
    H : gmap nat (HTerm * nat); 
    nxt : nat; 
    wf : Squash (forall n, nxt <= n -> H !! n  = None)
  }. 

  (* Check (_ : EqDecision (gmap nat nat)). *)

Global Instance Heap_eq_dec : 
  EqDecision Heap.
Proof.
  unfold EqDecision.
  intros. unfold Decision. destruct x. destruct y.
  destruct (gmap_eq_dec _ H0 H1); [|right; try congruence].
  destruct (PeanoNat.Nat.eq_dec nxt0 nxt1); [|right].
  2:{ unfold not. intros. eapply n. inversion H2. reflexivity. }
  subst.
  left. reflexivity.
Qed.  


Lemma del_preserves_nxt (H : gmap nat (HTerm * nat)) : 
  forall nxt, 
    Squash (forall n, nxt <= n -> H !! n  = None) ->
    forall n', 
      Squash (forall n, nxt <= n -> (delete n' H) !! n  = None).
Proof.
  intros.
  destruct H0.
  econstructor.
  intros.   
  specialize (e _ H0).
  pose proof PeanoNat.Nat.eq_dec n n'.
  destruct H1.
  - subst. rewrite lookup_delete_eq. reflexivity.
  - rewrite lookup_delete_ne; try congruence.
Qed.   

Definition del_heap (Hp : Heap) n : Heap :=
  {|
    H := delete n (H Hp); 
    nxt := (nxt Hp);
    wf := del_preserves_nxt (H Hp) (nxt Hp) (wf Hp) n
  |}.

Definition lookup_heap Hp n : option HTerm :=
  option_map fst ((H Hp) !! n).

Definition lookup_heap_full Hp n : option (HTerm * nat) :=
  (H Hp) !! n. 

Definition dom_heap Hp :=
  dom (H Hp). 

Definition card_dom_heap Hp :=
  size (dom_heap Hp). 

Lemma insert_inc_next (Hp : Heap) : 
  forall t (n' : nat), 
    Squash (forall n, (S (nxt Hp)) <= n -> (insert (nxt Hp) (t, n') (H Hp)) !! n  = None).
Proof.
  intros. pose proof (wf Hp).
  destruct H0. rename e into H0.
  econstructor. intros.  
  destruct (PeanoNat.Nat.eq_dec n (nxt Hp)).
  - rewrite e in *. lia.
  - destruct (le_lt_dec (nxt Hp) n).
    + specialize (H0 n l).
      rewrite lookup_insert_ne; try congruence.
    + lia.
Qed.



Definition insert_heap (Hp : Heap) t n :=
  {|
    H := insert (nxt Hp) (t, n) (H Hp); 
    nxt := S (nxt Hp);
    wf := insert_inc_next Hp t n
  |}.




Lemma empty_heap_wf : 
  Squash (forall n, 0 <= n -> ((∅ : gmap nat (HTerm * nat))) !! n  = None).
Proof.
  econstructor. intros.
  exact (lookup_empty (M := gmap nat) (A := (HTerm * nat)) n).
Defined. 

(* Search squash.  *)

Definition empty_heap : Heap :=
  {|
    H := ∅;
    nxt := 0;
    wf :=  empty_heap_wf
  |}.

Lemma empty_heap_lookup : 
  forall n, 
    lookup_heap empty_heap n = None. 
Proof. 
  intros. unfold empty_heap. unfold lookup_heap. simpl. rewrite lookup_empty. reflexivity. 
Qed.     

Inductive HeapConstructible : Heap -> Prop :=
  | EmptyConstructible : 
    HeapConstructible empty_heap
  | InsertionConstructible :
    forall Hp t n,
      HeapConstructible Hp ->
      HeapConstructible (insert_heap Hp t n)
  | DeletionConstructible : 
    forall Hp n, 
      HeapConstructible Hp ->
      HeapConstructible (del_heap Hp n).

Lemma Heap_eq_ext : 
  forall Hp Hp',
    (H Hp) = (H Hp') -> (nxt Hp) = (nxt Hp') -> Hp = Hp'.
Proof.
  intros. destruct Hp. destruct Hp'. simpl in *.
  subst.
  reflexivity.
Qed.     
  
Lemma unsquash {P : Prop} (d : Decision P) (s : Squash P) : P.
Proof.
  destruct d; try auto.
  enough sEmpty.
  destruct H0.
  destruct s.
  exfalso; eapply n. eassumption.     
Qed. 

Lemma delete_top_wf (Hp : Heap) : 
  forall n', 
  (nxt Hp) = S n' ->
  Squash (∀ n : nat, (nxt Hp) ≤ n → (H Hp) !! n = None) ->
  Squash (∀ n : nat, n' ≤ n → (H (del_heap Hp (n'))) !! n = None). 
Proof.
  intros.
  destruct H1.
  rename e into H1.
  econstructor.   
  rewrite H0 in *. intros.  
  destruct (PeanoNat.Nat.eq_dec n' n).
  - subst. destruct Hp. simpl. rewrite lookup_delete_eq. reflexivity.
  - specialize (H1 n ltac:(lia)). destruct Hp. simpl.
    rewrite lookup_delete_ne; try congruence.
    simpl in H1. eauto.
Defined.        

Definition delete_top (Hp : Heap) : Heap :=
match (nxt Hp) as y return ((nxt Hp) = y) -> Heap with
  | 0 => (fun _ => Hp)
  | S n => fun heq =>
    {|
      H := (H (del_heap Hp (n)));
      nxt := n;
      wf := (delete_top_wf Hp n heq (wf Hp))
    |}
end eq_refl. 

  

Lemma all_heaps_constructible :
  forall Hp, 
  HeapConstructible Hp.
Proof.
  intros. destruct Hp. revert wf0. revert H0.
  induction nxt0.
  - intros. 
    assert ({| H := H0; nxt := 0; wf := wf0 |} = empty_heap); [|rewrite H1; econstructor]. 
    unfold empty_heap.
    eapply Heap_eq_ext; simpl; try congruence. 
    pose proof unsquash (wf_dec _ 0) wf0.
    eapply map_eq.
    intros. specialize (H1 i ltac:(lia)).
    rewrite H1.
    rewrite lookup_empty. 
    reflexivity.
  - intros.
    destruct (H0 !! (nxt0)) eqn:heq.
    + pose (delete_top {| H := H0; nxt := S nxt0; wf := wf0 |}) as h0.
      unfold delete_top in h0.
      simpl in h0.
      specialize (IHnxt0 (H h0) (wf h0)).
      unfold h0 in IHnxt0. simpl in IHnxt0.
      destruct p as (p, n'). 
      enough ({| H := H0; nxt := S nxt0; wf := wf0 |} = insert_heap h0 p n').
      {
       rewrite H1. econstructor. unfold h0. eassumption.     
      }
      unfold insert_heap. eapply Heap_eq_ext.
      * simpl. eapply map_eq. intros.
        destruct (PeanoNat.Nat.eq_dec i nxt0).
        -- rewrite lookup_insert. rewrite e. unfold decide. unfold decide_rel. destruct (Nat.eq_dec nxt0 nxt0); try congruence. 
        -- rewrite lookup_insert_ne; try congruence. rewrite lookup_delete_ne; try congruence.
      * simpl. reflexivity.      
    + pose (delete_top {| H := H0; nxt := S nxt0; wf := wf0 |}) as h0.
      unfold delete_top in h0.
      simpl in h0.
      specialize (IHnxt0 (H h0) (wf h0)).
      unfold h0 in IHnxt0. simpl in IHnxt0.
      enough ({| H := H0; nxt := S nxt0; wf := wf0 |} = del_heap (insert_heap h0 (HAddr nxt0) 0) nxt0).
      {
       rewrite H1. econstructor. econstructor. unfold h0. eassumption.     
      }
      unfold insert_heap. unfold del_heap. eapply Heap_eq_ext.
      * simpl. eapply map_eq. intros.
        destruct (PeanoNat.Nat.eq_dec i nxt0).
        -- rewrite lookup_delete; try congruence. rewrite lookup_insert. rewrite e. unfold decide. unfold decide_rel. destruct (Nat.eq_dec nxt0 nxt0); congruence. 
        -- rewrite lookup_delete_ne; try congruence. rewrite lookup_insert_ne; try congruence. rewrite lookup_delete_ne; try congruence.
      * simpl. reflexivity.
Qed. 

Lemma constructible_induction_helper (P : Heap -> Prop) : 
  (forall hp, HeapConstructible hp -> P hp) -> 
  forall hp, P hp.
Proof.
  intros. eapply H0. eapply all_heaps_constructible.
Qed. 


Lemma heap_induction (P : Heap -> Prop) : 
  P empty_heap ->
  (forall Hp,
    P Hp -> ((forall t n, P (insert_heap Hp t n)) /\ (forall n, P (del_heap Hp n)))) ->
  forall Hp, 
  P Hp.
Proof.
  intros. 
  pose proof HeapConstructible_ind.
  specialize (H2 P H0). 
  eapply H2.
  - intros. specialize (H1 Hp0 H4).
    destruct H1. eapply H1.
  - intros. specialize (H1 Hp0 H4).
    destruct H1. eapply H5.
  - eapply all_heaps_constructible.
Qed.  

Lemma card_bound :
forall Hp, 
  card_dom_heap Hp <= nxt Hp.
Proof.
  eapply heap_induction. 
  - unfold empty_heap. simpl. unfold card_dom_heap. unfold dom_heap.
    simpl. rewrite dom_empty. rewrite size_empty. lia.
  - intros. split.
    + intros. unfold insert_heap. simpl. unfold card_dom_heap.
      unfold dom_heap. simpl. rewrite dom_insert. rewrite size_union; destruct Hp.
      { 
        unfold nxt. rewrite size_singleton.  unfold card_dom_heap in H0. unfold dom_heap in H0. simpl in *. lia.  
      }
      unfold nxt.
      unfold H.
      rewrite disjoint_singleton_l.
      eapply not_elem_of_dom.
      eapply (unsquash (wf_dec _ _) (wf0) nxt0 ltac:(lia)).
    + intros. unfold del_heap. simpl. unfold card_dom_heap in *. unfold dom_heap in *. unfold H in *. destruct Hp. unfold nxt in *.
      rewrite dom_delete.    
      rewrite size_difference_alt.
      lia.
Qed. 

Definition configuration := (HTerm * Heap * nat)%type. 

(* Search  *)

Fixpoint ast_size t : nat :=
  match t with
  | HVar _ => 1
  | HApp t1 t2 => 1 + ast_size t1 + ast_size t2
  | HAbs _ t => 1 + ast_size t
  | HAddr _ => 1
  end.

Fixpoint vars t : gset nat :=
match t with
  | HVar n => union {[n]} ∅
  | HApp t1 t2 => union (vars t1) (vars t2)
  | HAbs n t => union {[n]} (vars t)
  | HAddr _ => ∅
  end.

Fixpoint addrs t : gset nat :=
match t with
  | HVar n => ∅
  | HApp t1 t2 => union (addrs t1) (addrs t2)
  | HAbs n t => (addrs t)
  | HAddr n => union {[n]} ∅
  end.

Fixpoint parameterized_size_hterm t n : nat :=
  match t with
  | HVar _ => Nat.log2_up n
  | HApp t1 t2 => 1 + parameterized_size_hterm t1 n + parameterized_size_hterm t2 n
  | HAbs _ t => 1 + parameterized_size_hterm t n
  | HAddr n => Nat.log2_up n
  end.




Definition heap_dag (Hp : Heap) : Prop :=
  forall n t,
  lookup_heap Hp n = Some t ->
  forall n',
  (elem_of n' (addrs t)) ->
  n' < n. 

Definition heap_missless (Hp : Heap) : Prop :=
  forall n t,
    lookup_heap Hp n = Some t ->
      forall n',
        (elem_of n' (addrs t)) ->
        exists t', 
          lookup_heap Hp n' = Some t'.

Definition term_valid_heap t Hp : Prop :=
  forall n, 
    elem_of n (addrs t) ->
    elem_of n (dom_heap Hp).

Definition heap_closed Hp : Prop :=
  forall n t, 
    lookup_heap Hp n = Some t ->
    is_closed t.

 

Definition valid_config (config : configuration) : Prop :=
  let '(t, Hp, v_size) := config in 
  heap_dag (Hp) /\
  heap_missless (Hp) /\
  term_valid_heap t Hp.


(* subterm t1 t2 = t1 is a subterm of t2 *)
Inductive Subterm : HTerm -> HTerm -> Prop :=
| HAppSTL :
  forall t1 t2 t_sub, 
    Subterm t_sub t1 ->
    Subterm t_sub (HApp t1 t2)
| HAppSTR : 
  forall t1 t2 t_sub, 
    Subterm t_sub t2 ->
    Subterm t_sub (HApp t1 t2)
| HAbsST : 
  forall n t t_sub, 
    Subterm t_sub t ->
    Subterm t_sub (HAbs n t)
| HReflST : 
  forall t, 
    Subterm t t. 

      (* | HCHole : EHContext (* hole *)
  | AbsHCon : EHContext -> HTerm -> EHContext (* hole in caller *)
  | ArgHCon : HTerm -> EHContext -> EHContext (* hole in arg *)
  | LamHCon : nat -> EHContext -> EHContext. hole lambda body *)


Lemma subst_addr_subset : 
  forall t1 n t2, 
    forall n', 
      elem_of n' (addrs (subst t2 n t1)) ->
      elem_of n' (addrs (HApp (HAbs n t1) t2)). 
Proof.
  induction t1.
  - simpl. intros. destruct (n =? n0) eqn:neq.
    + rewrite elem_of_union. right. eassumption. 
    + simpl in H0. rewrite elem_of_empty in H0. contradiction.
  - intros. simpl in *.
    specialize (IHt1_1 n t2 n').
    specialize (IHt1_2 n t2 n').
    rewrite elem_of_union in H0.
    destruct H0.
    + specialize (IHt1_1 H0).
      rewrite elem_of_union in IHt1_1.
      destruct IHt1_1.
      * eapply elem_of_union. left. eapply elem_of_union. left; assumption.
      * eapply elem_of_union. right; assumption.
    + specialize (IHt1_2 H0).
      rewrite elem_of_union in IHt1_2.
      destruct IHt1_2.
      * eapply elem_of_union. left. eapply elem_of_union. right. assumption.
      * eapply elem_of_union. right. assumption.
  - intros. simpl in *. destruct (n =? n0) eqn:neq.
    + simpl in H0.  
      eapply elem_of_union. left. assumption.
    + simpl in H0. 
      eapply IHt1; eassumption.
  - intros. simpl in *. eapply elem_of_union. left. assumption.
Qed. 

Lemma subterm_dom_subset : 
  forall t t', 
    Subterm t' t ->
    subseteq (addrs t') (addrs t). 
Proof. 
  induction t; intros. 
  - inversion H0; subst. 
    simpl in *.  set_solver. 
  - inversion H0; subst. 
    + simpl.  specialize (IHt1 _ H3).
      set_solver. 
    + simpl in *. specialize (IHt2 _ H3).
      set_solver. 
    + set_solver. 
  - simpl in *. inversion H0; subst; simpl;[ eapply IHt; try eassumption|].
    set_solver. 
  - inversion H0; subst. set_solver. 
Qed.  

Lemma subset_term_valid_heap :
  forall t t' Hp,
  subseteq (addrs t) (addrs t') ->
  term_valid_heap t' Hp ->
  term_valid_heap t Hp. 
Proof. 
  intros. unfold term_valid_heap in *. intros. eapply H1; try eassumption.
  set_solver.
Qed.    

Lemma subterm_term_valid_heap : 
  forall t t' Hp, 
    Subterm t' t ->
    term_valid_heap t Hp ->
    term_valid_heap t' Hp. 
Proof. 
  intros. 
  unfold term_valid_heap in *; intros. 
  pose proof subterm_dom_subset t t' H0.
  specialize (H1 n).
  set_solver. 
Qed.

Lemma app_valid_heap : 
  forall t t' Hp, 
    term_valid_heap t Hp ->
    term_valid_heap t' Hp ->
    term_valid_heap (HApp t t') Hp.
Proof. 
  intros. unfold term_valid_heap in *; intros.
  simpl in *. eapply elem_of_union in H2. destruct H2. 
  + unfold dom_heap in *; destruct Hp; simpl in *. 
    eapply H0; eassumption. 
  + unfold dom_heap in *; destruct Hp; simpl in *. 
    eapply H1; eassumption.
Qed.  

Lemma elem_dom_heap_wf : 
  forall Hp n, 
    n ∈ dom_heap Hp ->
    n < nxt Hp. 
Proof. 
  intros. unfold dom_heap in H0. destruct Hp. simpl in *.
  pose proof (unsquash (wf_dec _ _ ) wf0). 
  pose proof elem_of_dom H1 n.
  destruct H3; clear H4.
  specialize (H3 H0). unfold is_Some in H3.
  destruct (Nat.le_dec nxt0 n ).
  + specialize (H2 n l).
    destruct H3. congruence.
  + lia.
Qed.     


Lemma insert_heap_mono : 
  forall n n' Hp t t',
    lookup_heap Hp n = Some t ->
    lookup_heap (insert_heap Hp t' n') n = Some t.
Proof.
  intros.
  destruct Hp; simpl. unfold lookup_heap in *. simpl in *.
  pose proof unsquash (wf_dec _ _) wf0.
  rewrite lookup_insert_ne; try eassumption.
  unfold not. intros.
  specialize (H2 n ltac:(lia)).
  destruct (H1 !! n); simpl in H0; try congruence. 
Qed.  


Lemma HTunfold_not_in :
  forall t substin Hp v_size n, 
    valid_config (t, Hp, v_size) ->
    lookup_heap Hp n = Some substin ->
    not (elem_of n (addrs (HTunfold substin n t))).
Proof. 
  induction t; intros.
  - simpl in *. set_solver.
  - simpl in *. unfold not. intros.
    eapply elem_of_union in H2. destruct H2.
    + eapply IHt1; try eassumption; try tauto.  
      destruct H0 as (dag, (full, vld)).
      split; try split; try tauto.
      eapply subterm_term_valid_heap; [|eapply vld].
      econstructor. econstructor.
    + eapply IHt2; try eassumption; try tauto.  
      destruct H0 as (dag, (full, vld)).
      split; try split; try tauto.
      eapply subterm_term_valid_heap; [|eapply vld].
      econstructor; econstructor. 
  - simpl in *. unfold not. intros. eapply IHt; try eassumption.
  - simpl in *. unfold not. intros.
    destruct (Nat.eqb n0 n) eqn:neq. 
    + eapply Nat.eqb_eq in neq. subst.
      destruct H0 as (dag, (full, vld)).
      unfold heap_dag in dag.
      specialize (dag n substin H1 n H2).
      lia.   
    + simpl in H2. eapply Nat.eqb_neq in neq. set_solver.
Qed.

Lemma HTunfold_upper_bound : 
  forall t substin Hp v_size n, 
    valid_config (t, Hp, v_size) ->
    lookup_heap Hp n = Some substin ->
    (forall n', 
      n < n' -> not (elem_of n' (addrs t))) ->
    forall n', 
      n <= n' -> not (elem_of n' (addrs (HTunfold substin n t))).
Proof. 
  induction t; intros; destruct H0 as (dag, (full, vld)).
  - simpl in *; set_solver.
  - simpl in *; unfold not. intros. eapply elem_of_union in H0. destruct H0.
    + eapply IHt1; try eapply H1; try tauto; try eapply H0; try lia.
      {
       split; try split; try tauto.
       eapply subterm_term_valid_heap; [|eapply vld]. repeat econstructor. 
      }
      intros. unfold not. intros. specialize (H2 n'0 H4).
      eapply H2. set_solver.
    + eapply IHt2; try eapply H1; try tauto; try eapply H0; try lia.
      {
       split; try split; try tauto.
       eapply subterm_term_valid_heap; [|eapply vld]. 
       eapply HAppSTR. econstructor. 
      }
      intros. unfold not. intros. specialize (H2 n'0 H4).
      eapply H2. set_solver.
  - simpl in *; eapply IHt; try eapply H1; try tauto; try eapply H0; try lia.
  - unfold not. intros; simpl in *. destruct (Nat.eqb n0 n) eqn:neq.
    + eapply Nat.eqb_eq in neq; subst. 
      specialize (dag n substin H1 n' H0).
      lia.
    + eapply Nat.eqb_neq in neq. 
      specialize (H2 n').
      unfold not in H2. eapply H2.
      * simpl in H0. eapply elem_of_union in H0. destruct H0; [|set_solver].
        rewrite elem_of_singleton in H0. subst. lia.
      * simpl in H0. set_solver.
Qed. 

Lemma HTunfold_preserves_valid_config : 
  forall t substin Hp v_size n,
    valid_config (t, Hp, v_size) ->
    lookup_heap Hp n = Some substin ->
    valid_config ((HTunfold substin n t), Hp, v_size). 
Proof.
  induction t; intros; destruct H0 as (dag, (full, vld)).
  - simpl in *. split; try split; try tauto.
  - split; try split; try tauto. simpl.       
    eapply app_valid_heap. 
    + eapply IHt1; try eassumption.
      split; try split; try eassumption.
      eapply subterm_term_valid_heap; [|eapply vld].
      repeat econstructor.
    + eapply IHt2; try eassumption.
      split; try split; try eassumption.
      eapply subterm_term_valid_heap; [|eapply vld].
      eapply HAppSTR; econstructor. 
  - simpl in *. split; try split; try tauto.
    unfold term_valid_heap. intros.
    specialize (IHt substin Hp n0 n0 ltac:(tauto) H1).
    destruct IHt as (?, (?, vld1)).
    eapply vld1. eassumption.
  - simpl in *. split; try split; try tauto.
    destruct (n0 =? n) eqn:neq.
    + rewrite Nat.eqb_eq in neq. subst.
      unfold term_valid_heap; intros.
      specialize (full n substin H1 n0 H0).
      destruct full. unfold dom_heap; destruct Hp; simpl in *.
      eapply elem_of_dom. 
      unfold lookup_heap in H2. simpl in H2. 
      destruct (H3 !! n0); simpl in *; try congruence; eexists; reflexivity.  
    + assumption.
  Unshelve. 
  all: apply 0. 
Qed. 

Fixpoint HT_unfold_abstract n Hp t :=
  match n with
  | 0 => 
    match lookup_heap Hp 0 with
    | Some t' => HTunfold t' 0 t
    | None => t
    end
  | S n' => 
    match lookup_heap Hp (S n') with
    | Some t' => HT_unfold_abstract n' Hp (HTunfold t' (S n') t)
    | None => HT_unfold_abstract n' Hp t
    end
  end. 

Definition HT_unfold_concrete Hp t :=
  HT_unfold_abstract (nxt Hp) Hp t. 

Lemma HT_unfold_abstract_at_n :
  forall n Hp t v_size, 
    valid_config (t, Hp, v_size) ->
    (forall n', 
      n < n' -> not (elem_of n' (addrs t))) ->
    forall n', 
      n <= n' ->
    not (elem_of n' (addrs (HT_unfold_abstract n Hp t))).
Proof.
  induction n; intros; destruct H0 as (dag, (full, vld)).
  - unfold not. intros. simpl in H0.
    destruct (lookup_heap Hp 0) eqn:lkupeq; simpl in H0.
    + eapply HTunfold_upper_bound; try eassumption; try split; try split; try eassumption. 
    + eapply H1; [|eassumption].
      eapply Nat.lt_eq_cases in H2.
      destruct H2; try lia. subst. exfalso. 
      specialize (vld 0 H0).     
      destruct Hp; unfold dom_heap in vld; simpl in vld.
      eapply elem_of_dom in vld.
      destruct vld; unfold lookup_heap in lkupeq; simpl in lkupeq.
      destruct (H2 !! 0); simpl in *; congruence. 
  - unfold not. intros.
    simpl in H0.
    destruct (lookup_heap Hp (S n)) eqn:lkuphp.
    + specialize (IHn Hp (HTunfold h (S n) t) v_size).
      eapply IHn; [ | | | eapply H0]; try lia.
      2:{
        intros. eapply HTunfold_upper_bound; try eassumption.
        split; try split; tauto.    
      }
      eapply HTunfold_preserves_valid_config; try eassumption.
      split; try split; eassumption.   
    + eapply IHn; try eassumption; try lia.
      * split; try split; eassumption.
      * intros. unfold not. intros. 
        assert (S n <= n'0) as ineq by lia.  
        eapply Nat.lt_eq_cases in ineq.
        eapply H1; try eassumption.  
        destruct ineq; try lia. subst. exfalso. 
        specialize (vld (S n) H4).     
        destruct Hp; unfold dom_heap in vld; simpl in vld.
        eapply elem_of_dom in vld.
        destruct vld; unfold lookup_heap in lkuphp; simpl in lkuphp.
        destruct (H5 !! S n); simpl in *; try congruence. 
    Unshelve. 
    all:apply 0.
Qed. 

Lemma HT_unfold_abstract_all : 
  forall n Hp t v_size, 
    valid_config (t, Hp, v_size) ->
    (forall n', 
      n < n' -> not (elem_of n' (addrs t))) ->
    forall n', 
    not (elem_of n' (addrs (HT_unfold_abstract n Hp t))).
Proof. 
  induction n; intros.
  - pose proof HT_unfold_abstract_at_n 0 Hp t v_size H0 H1 n' ltac:(lia).
    assumption.
  - unfold not. intros.
    simpl in H0.
    simpl in H2. 
    destruct (lookup_heap Hp (S n)) eqn:lkuphp.
    + specialize (IHn Hp (HTunfold h (S n) t) v_size).
      simpl in H2. 
      (* eapply IHn.  *)
      eapply IHn; [ | | eapply H2]; try lia.
      2:{
        intros. eapply HTunfold_upper_bound; try eassumption.
      }
      eapply HTunfold_preserves_valid_config; try eassumption.
    + eapply IHn; try eassumption; try lia.
      intros. unfold not. intros. 
      assert (S n <= n'0) as ineq by lia.  
      eapply Nat.lt_eq_cases in ineq.
      eapply H1; try eassumption.  
      destruct ineq; try lia. subst. exfalso. 
      destruct H0 as (dag, (full, vld)).
      specialize (vld (S n) H4).     
      destruct Hp; unfold dom_heap in vld; simpl in vld.
      eapply elem_of_dom in vld.
      destruct vld; unfold lookup_heap in lkuphp; simpl in lkuphp.
      destruct (H0 !! S n); simpl in *; try congruence. 
    Unshelve. 
    all:apply 0.
Qed.

Lemma HT_unfold_concrete_clean : 
  forall Hp t v_size, 
    valid_config (t, Hp, v_size) ->
    forall n', 
    not (elem_of n' (addrs (HT_unfold_concrete Hp t))).
Proof. 
  unfold HT_unfold_concrete. 
  intros; eapply HT_unfold_abstract_all; try eassumption.
  intros. 
  destruct H0 as (dag, (full, vld)).
  unfold not; intros. 
  specialize (vld n'0 H0).
  unfold dom_heap in vld. destruct Hp; simpl in *.
  pose proof unsquash (wf_dec _ _) wf0.
  specialize (H3 n'0 ltac:(lia)).
  eapply elem_of_dom in vld.
  destruct vld. congruence.
Qed. 

(* (subst (HAddr (nxt Hp)) n t1, insert_heap Hp t2, v_size) *)



Lemma HTunfold_no_instance : 
forall t n t', 
  n ∉ addrs t' ->
  HTunfold t n t' = t'.
Proof. 
  induction t'.
  - intros. simpl in *.  reflexivity.
  - intros. simpl in *. 
    rewrite not_elem_of_union in H0.
    destruct H0.
    rewrite IHt'1; try assumption. 
    rewrite IHt'2; try assumption. 
    reflexivity.
  - intros. simpl in *. rewrite IHt'; try assumption; reflexivity. 
  - intros; simpl in *.  
    destruct (n =? n0) eqn:neq. 
    + rewrite not_elem_of_union in H0.
      destruct H0. 
      rewrite not_elem_of_singleton in H0. 
      rewrite Nat.eqb_eq in neq. congruence. 
    + reflexivity. 
Qed.  

Lemma HT_unfold_abstract_addr : 
  forall n' Hp n t v_size, 
    lookup_heap Hp n = Some t ->
    valid_config ((HAddr n), Hp, v_size) ->
    n <= n' ->
    HT_unfold_abstract n' Hp (HAddr n) = HT_unfold_abstract n' Hp t.
Proof. 
  induction n'; intros. 
  - eapply Nat.lt_eq_cases in H2. destruct H2; try lia.
    subst.
    simpl in *. rewrite H0.
    rewrite HTunfold_no_instance; try reflexivity.
    destruct H1 as (dag, (full, vld)).
    unfold not. intros.
    specialize (dag 0 t H0 0 H1).
    lia.   
  - unfold HT_unfold_abstract; fold HT_unfold_abstract. 
    eapply Nat.lt_eq_cases in H2. destruct H2. 
    + destruct (lookup_heap Hp (S n')); [|eapply IHn'; try eassumption; try lia].
      rewrite HTunfold_no_instance; [rewrite HTunfold_no_instance; [eapply IHn'; try assumption; try lia|]|]; destruct H1 as (dag, (full, vld)).
      * unfold not. intros. 
        specialize (dag n t H0 (S n') H1).
        lia.
      * unfold not. intros. simpl in H1. rewrite elem_of_union in H1.
        destruct H1; [|set_solver].
        apply elem_of_singleton in H1. lia.
    + rewrite H2 in *. rewrite H0.
      simpl. destruct (n' =? n') eqn:neq; [|rewrite Nat.eqb_neq in neq; try congruence].
      rewrite HTunfold_no_instance; try reflexivity.
      unfold not. intros.    
      destruct H1 as (dag, (full, vld)).
      specialize (dag (S n') t H0 (S n') H3).
      lia.
    Unshelve. 
    apply 0.
Qed.         
       


Lemma HT_unfold_concrete_addr : 
  forall Hp n t v_size, 
    lookup_heap Hp n = Some t ->
    valid_config ((HAddr n), Hp, v_size) ->
    HT_unfold_concrete Hp (HAddr n) = HT_unfold_concrete Hp t.
Proof.
  intros. unfold HT_unfold_concrete.
  eapply HT_unfold_abstract_addr; try eassumption.
  destruct H1 as (dag, (full, vld)).
  destruct Hp. simpl in *.
  pose proof unsquash (wf_dec _ _) wf0 n.
  pose proof Nat.le_dec nxt0 n.
  destruct H3; [|lia]. 
  specialize (H2 l).
  unfold lookup_heap in H0. simpl in H0. rewrite H2 in H0. simpl in H0. discriminate.
Qed.      

Lemma HT_unfold_abstract_app : 
  forall n Hp t1 t2, 
    HT_unfold_abstract n Hp (HApp t1 t2) = HApp (HT_unfold_abstract n Hp t1) (HT_unfold_abstract n Hp t2).
Proof. 
  induction n; intros.
  - simpl in *. destruct (lookup_heap Hp 0); reflexivity.
  - simpl. destruct (lookup_heap Hp (S n)); eapply IHn.
Qed.

Lemma HT_unfold_abstract_abs : 
  forall n Hp n' t, 
    HT_unfold_abstract n Hp (HAbs n' t) = HAbs n' (HT_unfold_abstract n Hp t).
Proof. 
  induction n; intros.
  - simpl in *. destruct (lookup_heap Hp 0); reflexivity.
  - simpl. destruct (lookup_heap Hp (S n)); eapply IHn.
Qed.

Lemma HT_unfold_concrete_app : 
  forall Hp t1 t2, 
    HT_unfold_concrete Hp (HApp t1 t2) = HApp (HT_unfold_concrete Hp t1) (HT_unfold_concrete Hp t2).
Proof.
  intros. unfold HT_unfold_concrete. eapply HT_unfold_abstract_app.
Qed.  

Fixpoint HT_gc_abstract n t acc : Heap :=
  match n with
  | 0 => 
    match lookup_heap acc 0 with
    | Some t' => if HTerm_eq_dec (HTunfold t' 0 t) t then del_heap acc 0 else acc
    | None => acc
    end
  | S n' => 
    match lookup_heap acc (S n') with
    | Some t' => if HTerm_eq_dec (HTunfold t' (S n') t) t then HT_gc_abstract n' (HTunfold t' (S n') t) (del_heap acc (S n')) else HT_gc_abstract n' (HTunfold t' (S n') t) acc
    | None => HT_gc_abstract n' t acc
    end
  end.

Definition HT_gc_concrete t acc : Heap := HT_gc_abstract (nxt acc) t acc.


Lemma HT_unfold_abstract_domain : 
  forall n Hp Hp', 
    (forall n', n' <= n -> lookup_heap Hp n' = lookup_heap Hp' n') ->
  forall t, 
    HT_unfold_abstract n Hp t = HT_unfold_abstract n Hp' t.
Proof.  
  induction n; intros Hp Hp' H t.
  - simpl in *. specialize (H 0 ltac:(lia)).
    rewrite H. 
    destruct (lookup_heap Hp' 0); reflexivity.
  - simpl. pose proof (H (S n) ltac:(lia)) as H'.
    rewrite H'. destruct (lookup_heap Hp' (S n)); eapply IHn; intros; eapply H; try lia.
Qed.   

Lemma HT_gc_abstract_out_of_domain : 
  forall n t Hp, 
    forall n', 
      n < n' -> 
    lookup_heap (HT_gc_abstract n t Hp) n' = lookup_heap Hp n'. 
Proof.  
  induction n; intros t Hp n' H.
  - simpl. destruct (lookup_heap Hp 0) eqn:lkup.
    + destruct (HTerm_eq_dec (HTunfold h 0 t) t); try reflexivity.
      unfold lookup_heap. unfold del_heap. simpl. rewrite lookup_delete_ne; try lia.
      reflexivity.
    + reflexivity.
  - simpl. destruct (lookup_heap Hp (S n)).
    + destruct (HTerm_eq_dec (HTunfold h (S n) t) t).
      2:{ rewrite IHn; try lia. reflexivity.  }
      assert (lookup_heap Hp n' = lookup_heap (del_heap Hp (S n)) n').
      { unfold lookup_heap, del_heap. simpl. rewrite lookup_delete_ne; try lia. reflexivity. } 
      rewrite H0. apply IHn.  
      lia.
    + apply IHn. lia.   
Qed.   


Lemma gc_preserves_None : 
  forall n n' t Hp,
  lookup_heap Hp n' = None ->
  lookup_heap (HT_gc_abstract n t Hp) n' = None.
Proof.
  induction n; intros.
  - simpl. destruct (lookup_heap Hp 0) eqn:lkup; try assumption.
    destruct (HTerm_eq_dec (HTunfold h 0 t) t); try assumption.
    unfold del_heap. unfold lookup_heap. simpl.
    destruct (PeanoNat.Nat.eq_dec n' 0); subst.
    + rewrite lookup_delete_eq. simpl. reflexivity.
    + rewrite lookup_delete_ne; try congruence.
      apply H0.
  - simpl. destruct (lookup_heap Hp (S n)) eqn:lkup.
    + destruct (HTerm_eq_dec (HTunfold h (S n) t) t) eqn:teq.
      * rewrite e. eapply IHn. destruct (PeanoNat.Nat.eq_dec (S n) (n')); subst.
        -- unfold lookup_heap. unfold del_heap. simpl. rewrite lookup_delete_eq.
          simpl. reflexivity.
        -- unfold lookup_heap. unfold del_heap. simpl. rewrite lookup_delete_ne; try congruence. apply H0.
      * apply IHn. assumption.    
    + apply IHn; try eassumption.
Qed.           


Lemma unfold_gc_noop : 
  forall n t Hp,
    HT_unfold_abstract n Hp t = HT_unfold_abstract n (HT_gc_abstract n t Hp) t.
Proof.
  induction n; intros t Hp.
  - simpl in *. destruct (lookup_heap Hp 0) eqn:lkup; try congruence.
    + destruct (HTerm_eq_dec (HTunfold h 0 t) t); simpl.
      * unfold lookup_heap. unfold del_heap. simpl.
        rewrite lookup_delete_eq. simpl. assumption.
      * rewrite lkup. reflexivity.
    + rewrite lkup; reflexivity.
  - simpl. destruct (lookup_heap Hp (S n)) eqn:lkup. 
    + destruct (HTerm_eq_dec (HTunfold h (S n) t) t).
      * rewrite e.
        pose proof HT_unfold_abstract_domain n Hp ((del_heap Hp (S n))).
        rewrite H0 at 1.
        2:{ intros. unfold lookup_heap. unfold del_heap. simpl. rewrite lookup_delete_ne; try lia. reflexivity. }
        pose proof gc_preserves_None n (S n) t (del_heap Hp (S n)) as H1.
        unfold lookup_heap, del_heap in H1. simpl in H1.
        rewrite lookup_delete_eq in H1. simpl in H1.
        specialize (H1 eq_refl).
        unfold lookup_heap. unfold del_heap. rewrite H1. eapply IHn.
      * pose proof HT_gc_abstract_out_of_domain n (HTunfold h (S n) t) Hp (S n) ltac:(lia).
        rewrite H0. rewrite lkup. eapply IHn.    
    + rewrite HT_gc_abstract_out_of_domain; try lia.
      rewrite lkup. eapply IHn.
Qed.     

Lemma gc_preserves_nxt :  
  forall n t Hp, 
    nxt Hp = nxt (HT_gc_abstract n t Hp).
Proof.
  induction n; intros t Hp.
  - simpl. destruct (lookup_heap Hp 0); simpl; try reflexivity.
    destruct (HTerm_eq_dec (HTunfold h 0 t) t); try reflexivity.
  - simpl. destruct (lookup_heap Hp (S n)); simpl; try (eapply IHn; eauto).
    destruct (HTerm_eq_dec (HTunfold h (S n) t) t); simpl; try (eapply IHn; eauto).
    assert (nxt Hp = nxt (del_heap Hp (S n))) by (unfold del_heap; simpl; reflexivity).
    rewrite H0. eapply IHn.    
Qed.   
 
Lemma unfold_gc_conctere_noop : 
  forall t Hp, 
    HT_unfold_concrete Hp t = HT_unfold_concrete (HT_gc_concrete t Hp) t.
Proof.
  intros. unfold HT_unfold_concrete. unfold HT_gc_concrete.
  rewrite <- gc_preserves_nxt.  
  eapply unfold_gc_noop.
Qed.    

Lemma valid_config_app :  
  forall t1 t2 Hp v_size, 
    valid_config (HApp t1 t2, Hp, v_size) ->
    valid_config (t1, Hp, v_size) /\ valid_config (t2, Hp, v_size).
Proof.
  intros t1 t2 Hp v_size H0. 
  destruct H0 as (dag, (full, vld)).
  split; split; try split; try tauto.
  - unfold term_valid_heap. intros.
    specialize (vld n).
    simpl in vld.
    eapply vld; set_solver.
  - unfold term_valid_heap. intros.
    specialize (vld n).
    simpl in vld.
    eapply vld; set_solver.
Qed. 

Lemma valid_config_abs :  
  forall n t Hp v_size, 
    valid_config (HAbs n t, Hp, v_size) ->
    valid_config (t, Hp, v_size).
Proof.
  intros n t Hp v_size H0. 
  destruct H0 as (dag, (full, vld)).
  split; try split; try tauto.
Qed. 

Lemma to_term_clean_term : 
  forall t, 
    (forall n, n ∉ addrs t) ->
    exists t', hterm_to_term t = Some t'.
Proof. 
  induction t; intros H.
  - simpl in H. simpl. eexists; reflexivity.
  - simpl in *.
    specialize (IHt1 ltac:(intros; specialize (H n); set_solver)).
    specialize (IHt2 ltac:(intros; specialize (H n); set_solver)).
    destruct IHt1 as (?, IHt1); destruct IHt2 as (?, IHt2).
    rewrite IHt1; rewrite IHt2.
    eexists; reflexivity.
  - simpl in *.  
    specialize (IHt H).
    destruct IHt as (?, IHt).
    rewrite IHt.
    eexists; reflexivity.
  - simpl in H. specialize (H n). set_solver.
Qed.    

Lemma unfold_to_term : 
  forall t Hp v_size, 
    valid_config (t, Hp, v_size) ->
    exists t', 
      hterm_to_term (HT_unfold_concrete Hp t) = Some t'. 
Proof. 
  intros t Hp v_size H.
  eapply to_term_clean_term.
  eapply HT_unfold_concrete_clean. eassumption.     
Qed. 

Lemma hterm_to_term_subst_comm :
  forall t2 t1 t1' t2' n, 
    hterm_to_term t1 = Some t1' ->
    hterm_to_term t2 = Some t2' ->
    hterm_to_term (subst t1 n t2) = Some (t_subst t1' n t2').
Proof.
  induction t2; intros t1 t1' t2' n' H H0; try discriminate. 
  - simpl in *. inversion H0; subst. unfold t_subst.
    destruct (n =? n') eqn:neq; try assumption.
  - simpl in *.   
    destruct (hterm_to_term t2_1) eqn:t2_1eq; try discriminate.
    destruct (hterm_to_term t2_2) eqn:t2_2eq; try discriminate. 
    inversion H0; subst.
    rewrite (IHt2_1 t1 t1' t n' H eq_refl).
    rewrite (IHt2_2 t1 t1' t0 n' H eq_refl).
    simpl. reflexivity.
  - simpl in *.    
    destruct (hterm_to_term t2) eqn:t2eq; try discriminate.
    inversion H0; subst. simpl.    
    destruct (n =? n') eqn:neq; try congruence; [simpl; rewrite t2eq; reflexivity|]. 
    simpl. 
    rewrite (IHt2 t1 t1' t n' H eq_refl).
    reflexivity.
Qed.   

Lemma HTunfold_subst_comm : 
  forall t1 h n t2 n', 
    is_closed h ->
    HTunfold h n (subst t2 n' t1) = subst (HTunfold h n t2) n' (HTunfold h n t1).
Proof.
  induction t1; intros h n1 t2 n2 H.
  - simpl. destruct (n =? n2); reflexivity.
  - simpl; try rewrite <- IHt1_1; try rewrite <- IHt1_2; try
    reflexivity; try assumption. 
  - simpl. rewrite <- IHt1; try destruct (n =? n2); try reflexivity; try assumption. 
  - simpl. destruct (n1 =? n); simpl; try reflexivity.
    rewrite subst_is_closed_noop; try reflexivity; try assumption.
Qed.  

Lemma HT_unfold_abstract_subst_comm : 
  forall n Hp t1 n' t2, 
    heap_closed Hp ->
    HT_unfold_abstract n Hp (subst t1 n' t2) = subst (HT_unfold_abstract n Hp t1) n' (HT_unfold_abstract n Hp t2).
Proof.
  induction n; intros Hp t1 n' t2 hclos.
  - simpl. 
    destruct (lookup_heap Hp 0) eqn:lkup; try reflexivity.
    eapply HTunfold_subst_comm.
    eapply hclos. apply lkup.
  - simpl. destruct (lookup_heap Hp (S n)) eqn:lkup.
    + rewrite HTunfold_subst_comm; [|eapply hclos; eassumption].
      eapply IHn; assumption.
    + eapply IHn. assumption.
Qed. 

Lemma  HT_unfold_concrete_subst_comm : 
    forall Hp t1 n' t2, 
    heap_closed Hp ->
    HT_unfold_concrete Hp (subst t1 n' t2) = subst (HT_unfold_concrete Hp t1) n' (HT_unfold_concrete Hp t2).
Proof.
  intros. unfold HT_unfold_concrete in *. eapply HT_unfold_abstract_subst_comm. assumption.
Qed.    