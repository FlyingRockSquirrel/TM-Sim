From Stdlib Require Import Nat List Lia StrictProp.          
From stdpp Require Import gmap. 

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

Fixpoint t_subst substin substout body :=
match body with
| Var i =>
  if Nat.eqb i substout then substin else Var i
| App t u => App (t_subst substin substout t) (t_subst substin substout u)
| Abs n t => 
  if Nat.eqb n substout then Abs n t 
    else Abs n (t_subst substin substout t)
end. 

Fixpoint unfold substin n body :=
match body with
| HVar i => HVar i
| HApp t u => HApp (unfold substin n t) (unfold substin n u)
| HAbs n t => unfold substin n t
| HAddr n => substin
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


Lemma wf_dec (H : gmap nat HTerm) : 
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
    H : gmap nat HTerm; 
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


Lemma del_preserves_nxt (H : gmap nat HTerm) : 
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
  (H Hp) !! n.

Lemma insert_inc_next (Hp : Heap) : 
  forall t, 
    Squash (forall n, (S (nxt Hp)) <= n -> (insert (nxt Hp) t (H Hp)) !! n  = None).
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

Definition insert_heap (Hp : Heap) t :=
  {|
    H := insert (nxt Hp) t (H Hp); 
    nxt := S (nxt Hp);
    wf := insert_inc_next Hp t
  |}.

Definition dom_heap Hp :=
  dom (H Hp). 

Definition card_dom_heap Hp :=
  size (dom_heap Hp). 


Lemma empty_heap_wf : 
  Squash (forall n, 0 <= n -> ((∅ : gmap nat HTerm)) !! n  = None).
Proof.
  econstructor. intros.
  exact (lookup_empty (M := gmap nat) (A := HTerm) n).
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
    forall Hp t,
      HeapConstructible Hp ->
      HeapConstructible (insert_heap Hp t)
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
    + pose (delete_top {| H := H0; nxt := S nxt0; wf := wf0 |}).
      unfold delete_top in h0.
      simpl in h0.
      specialize (IHnxt0 (H h0) (wf h0)).
      unfold h0 in IHnxt0. simpl in IHnxt0.
      enough ({| H := H0; nxt := S nxt0; wf := wf0 |} = insert_heap h0 h).
      {
       rewrite H1. econstructor. unfold h0. eassumption.     
      }
      unfold insert_heap. eapply Heap_eq_ext.
      * simpl. eapply map_eq. intros.
        destruct (PeanoNat.Nat.eq_dec i nxt0).
        -- rewrite lookup_insert. rewrite e. unfold decide. unfold decide_rel. destruct (Nat.eq_dec nxt0 nxt0); congruence. 
        -- rewrite lookup_insert_ne; try congruence. rewrite lookup_delete_ne; try congruence.
      * simpl. reflexivity.      
    + pose (delete_top {| H := H0; nxt := S nxt0; wf := wf0 |}) as h0.
      unfold delete_top in h0.
      simpl in h0.
      specialize (IHnxt0 (H h0) (wf h0)).
      unfold h0 in IHnxt0. simpl in IHnxt0.
      enough ({| H := H0; nxt := S nxt0; wf := wf0 |} = del_heap (insert_heap h0 (HAddr nxt0)) nxt0).
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
    P Hp -> ((forall t, P (insert_heap Hp t)) /\ (forall n, P (del_heap Hp n)))) ->
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


Inductive EHContext :=
  | HCHole : EHContext (* hole *)
  | AbsHCon : EHContext -> HTerm -> EHContext (* hole in caller *)
  | ArgHCon : HTerm -> EHContext -> EHContext (* hole in arg *)
  | LamHCon : nat -> EHContext -> EHContext. (* hole lambda body *)

Fixpoint fill_hole C t :=
  match C with
  | HCHole => t
  | AbsHCon C' t' => HApp (fill_hole C' t) t'
  | ArgHCon t' C' => HApp t' (fill_hole C' t)
  | LamHCon n C' => HAbs n (fill_hole C' t)
  end. 

Fixpoint cbn_context (t : HTerm) : option (EHContext * HTerm) :=
match t with
| HApp (HAbs n t1) t2 => Some (HCHole, (HApp (HAbs n t1) t2))
(* | HApp (HAddr n) (t1) => (HCHole, (HApp (HAddr n) (t1))) *)
| HApp t1 t2 => 
  match cbn_context t1 with
  | Some (C, t) => Some (AbsHCon C t2, t)
  | None => None
  end
| HAddr n => Some (HCHole, (HAddr n))
| _ => None
end.

Inductive CBNContextRel : HTerm -> (EHContext * HTerm) -> Prop :=
| CBNVLeft :
  forall n t1 t2, 
    CBNContextRel (HApp (HAbs n t1) t2)  (HCHole, (HApp (HAbs n t1) t2))
| CBNTLeft : 
  forall t1 t2 C t, 
    CBNContextRel t1 (C, t) ->
    CBNContextRel (HApp t1 t2) (AbsHCon C t2, t)
| CBNAddr : 
  forall n, 
    CBNContextRel (HAddr n) (HCHole, HAddr n).

Lemma cbn_context_sound : 
  forall t C t', 
    CBNContextRel t (C, t') ->
    cbn_context t = Some (C, t').
Proof. 
  induction t; intros.
  - inversion H0; subst; simpl.
  - inversion H0; subst; simpl in *; try reflexivity.
    specialize (IHt1 C0 t' H2).
    destruct t1 eqn:teq; try (rewrite IHt1); try reflexivity.
    inversion H2.
  - inversion H0.
  - inversion H0; subst; simpl. reflexivity.
Qed.           

Lemma cbn_context_sound_bwd : 
  forall t C t', 
    cbn_context t = Some (C, t') ->
    CBNContextRel t (C, t').
Proof. 
  induction t; intros.
  - inversion H0; subst; simpl.
  - simpl in H0. 
    destruct t1 eqn:t1eq.
    + simpl in H0;  discriminate.
    + destruct (cbn_context (HApp h1 h2)) eqn:cbneq; try discriminate. 
      destruct p.
      specialize (IHt1 e h eq_refl).
      inversion H0; subst.
      econstructor. eapply IHt1.
    + inversion H0; subst. econstructor.
    + simpl in H0. inversion H0; subst. econstructor. econstructor.           
  - inversion H0.
  - inversion H0; subst; simpl. econstructor. 
Qed.        

Lemma cbn_no_reduction_no_op :
  forall t C t', 
  cbn_context t = Some (C, t') ->
  t = fill_hole C t'.
Proof.
  induction t; intros.
  - simpl in *. inversion H0; subst. 
  - simpl in *. destruct t1. 
    + simpl in *. inversion H0; subst. 
    + destruct (cbn_context (HApp t1_1 t1_2)) eqn:callerctx; try discriminate. destruct p. 
      inversion H0; subst. simpl. specialize (IHt1 e t' eq_refl).
      rewrite IHt1. reflexivity.
    + inversion H0; subst. simpl. reflexivity.
    + inversion H0; subst. simpl. reflexivity.
  - inversion H0; subst. 
  - inversion H0; subst. simpl. reflexivity.  
Qed.

Definition reduce_term t v_size Hp : option (HTerm * Heap) :=
match t with 
| (HApp (HAbs n t1) t2) => 
  if parameterized_size_hterm t2 v_size <=? Nat.log2_up (card_dom_heap Hp) 
    then 
      Some (subst t2 n t1, Hp)
    else 
      Some (subst (HAddr (nxt Hp)) n t1, insert_heap Hp t2)
| HAddr n => 
  match lookup_heap Hp n with
  | Some t' => Some (t', Hp)
  | None => None
  end
| _ => None
end.

Definition reduce_configuration_cbn C : option configuration :=
  match C with
  | (t, Hp, v_size) =>
    match cbn_context t with
    |Some (ctx, rdx) =>
      match reduce_term rdx v_size Hp with
      | Some (t', Hp') => Some (fill_hole ctx t', Hp', v_size)
      | None => None
      end
    | _ => None
    end
  end.

Fixpoint reduce_configuration_cbn_multistep n C :=
  match n with
  | 0 => Some C
  | S n' => 
    match reduce_configuration_cbn C with
    | Some C' => reduce_configuration_cbn_multistep n' C'
    | None => None
    end
  end. 

Inductive HReduceTerm v_size : (HTerm * Heap) -> (HTerm * Heap) -> Prop :=
  | HFullBeta : 
    forall n t1 t2 Hp, 
      parameterized_size_hterm t2 v_size <=? Nat.log2_up (card_dom_heap Hp) ->
      HReduceTerm v_size ((HApp (HAbs n t1) t2),  Hp) (subst t2 n t1, Hp)
  | HHeapBeta : 
    forall n t1 t2 Hp, 
      not (parameterized_size_hterm t2 v_size <=? Nat.log2_up (card_dom_heap Hp)) ->
      HReduceTerm v_size ((HApp (HAbs n t1) t2),  Hp) (subst (HAddr (nxt Hp)) n t1, insert_heap Hp t2)
  | HLookup : 
    forall n Hp t,
      lookup_heap Hp n = Some t ->
      HReduceTerm v_size (HAddr n, Hp) (t, Hp). 


(* Inductive HConfigurationStep : configuration -> configuration -> Prop :=
  | CBNFullBeta : 
    forall t H, 

    HConfigurationStep  *)

Lemma heap_growth_bounded_aux : 
  forall n t t' Hp Hp' v_size, 
    reduce_configuration_cbn_multistep n (t, Hp, v_size) = Some (t', Hp', v_size) ->
    card_dom_heap Hp' - n <= card_dom_heap Hp.
Proof.
  induction n.
  - intros. unfold reduce_configuration_cbn_multistep in H0. inversion H0; subst.
    lia. 
  - intros. simpl in H0.
    unfold reduce_configuration_cbn in H0.
    destruct (cbn_context t) eqn:ctxt. destruct p. 
    destruct h; simpl in H0; try discriminate.
    + destruct h1; simpl in H0; try discriminate.   
      destruct (parameterized_size_hterm h2 v_size <=? Nat.log2_up (card_dom_heap Hp)) eqn:holder. 
      * specialize (IHn (fill_hole e (subst h2 n0 h1)) t' Hp Hp' v_size H0).
        lia.
      * specialize (IHn (fill_hole e (subst (HAddr (nxt Hp)) n0 h1)) t' (insert_heap Hp h2) Hp' v_size H0).
        unfold insert_heap in *. unfold card_dom_heap in *.
        unfold dom_heap in *. simpl in IHn. 
        destruct Hp; simpl in IHn.
        simpl.
        rewrite dom_insert in *.
        rewrite size_union_alt in IHn.
        rewrite size_difference_alt in IHn.
        assert (size (dom H1 ∩ {[nxt0]}) <= 1).
        {
          transitivity (size ({[nxt0]} : gset nat)).
            - apply subseteq_size. set_solver.
            - rewrite size_singleton. lia.
        }
        rewrite size_singleton in IHn. lia.   
    + destruct (lookup_heap Hp n0); try discriminate.
      specialize (IHn _ _ _ _ _ H0). lia.
    + discriminate.     
Qed.  

Lemma heap_growth_bounded : 
  forall n t t' Hp' v_size, 
    reduce_configuration_cbn_multistep n (t, empty_heap, v_size) = Some (t', Hp', v_size) ->
    card_dom_heap Hp' <= n.
Proof.
  intros. pose proof heap_growth_bounded_aux n t t' empty_heap Hp' v_size H0.
  unfold card_dom_heap in H1.
  unfold dom_heap in H1. unfold empty_heap in H1. simpl in H1. rewrite dom_empty in H1.
  rewrite size_empty in H1.
  unfold card_dom_heap. unfold dom_heap. lia.
Qed.           

Definition heap_dag (Hp : Heap) : Prop :=
  forall n t,
  lookup_heap Hp n = Some t ->
  forall n',
  (elem_of n' (addrs t)) ->
  n' <= n. 

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

Definition valid_config (config : configuration) : Prop :=
  let '(t, Hp, v_size) := config in 
  heap_dag (Hp) /\
  heap_missless (Hp) /\
  term_valid_heap t Hp.

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

Lemma term_valid_heap_reduce : 
  forall t Hp v_size t' Hp'
  (eagle_eye : heap_missless Hp), 
  term_valid_heap t Hp ->
  reduce_term t v_size Hp = Some (t', Hp') ->
  term_valid_heap t' Hp'.
Proof. 
  induction t; intros. 
  - simpl in H1. discriminate. 
  - simpl in H1.  destruct t1; simpl; try discriminate. 
    destruct (parameterized_size_hterm t2 v_size <=? Nat.log2_up (card_dom_heap Hp)). 
    + simpl in *. inversion H1; subst.
      unfold term_valid_heap in *. intros.
      eapply H0. eapply subst_addr_subset. assumption.
    + simpl in *. inversion H1; subst.
      unfold term_valid_heap in *. intros.
      pose proof subst_addr_subset _ _ _ _ H2.
      simpl in H3.
      unfold dom_heap. unfold insert_heap. simpl.
      destruct Hp; simpl in *. clear H1.
      rewrite elem_of_union in H3. 
      (* destruct H3. *)
      rewrite elem_of_dom. unfold is_Some. rewrite lookup_insert.
      destruct (decide (nxt0 = n0)).
      * exists t2; reflexivity.
      * destruct H3;
        [| rewrite elem_of_union in H1; destruct H1; [rewrite elem_of_singleton in H1; congruence|rewrite elem_of_empty in H1; contradiction]].
        specialize (H0 n0 ltac:(eapply elem_of_union; left; eapply H1)).
        unfold dom_heap in H0. simpl in H0. rewrite elem_of_dom in H0.
        eapply H0.                     
  - simpl in H1. discriminate.
  - simpl in H1.
    unfold term_valid_heap.
    unfold lookup_heap in H1.            
    destruct (H Hp !! n) eqn:lkup; try discriminate.
    inversion H1; subst.
    intros.
    unfold heap_missless in eagle_eye.
    unfold lookup_heap in eagle_eye. 
    specialize (eagle_eye n t' lkup n0 H2). 
    unfold dom_heap. destruct Hp'. simpl in *.
    destruct eagle_eye. 
    rewrite elem_of_dom. unfold is_Some. rewrite H4. exists x. reflexivity.
Qed. 


(* Lemma trace_valid_config : 
  forall n t t' Hp Hp' v_size, 
    valid_config (t, Hp, v_size) ->
    reduce_configuration_cbn_multistep n (t, Hp, v_size) = Some (t', Hp', v_size) ->
    valid_config (t', Hp', v_size). 
Proof. 
  induction n; intros. 
  - simpl in H1. inversion H1; subst. assumption.
  - simpl in H1. 
    destruct (cbn_context t) eqn:cbnteq; try discriminate.
    destruct p. 
    destruct (reduce_term h v_size Hp) eqn:redteq; try discriminate. 
    destruct p.
    destruct h; destruct t; simpl in cbnteq; try discriminate. 
    + destruct t1; try discriminate; [|simpl in cbnteq; try congruence]. 
      destruct (cbn_context (HApp t1_1 t1_2)); try discriminate. 
      destruct p.  inversion cbnteq; subst.  
      admit.
    + admit.
    +      
    destruct t; destruct e; simpl in cbnteq; try discriminate. 
    + simpl in cbnteq; discriminate.
    +  *)


(* Lemma trace_heap_dac : 
  forall n t t' H v_size, 
    reduce_configuration_cbn_multistep n (t, empty_heap, v_size) = Some (t', H, v_size) ->
    heap_dag H.
Proof. 
  induction n.
  - intros. simpl in H1. inversion H1; subst.
    unfold heap_dag. intros. rewrite empty_heap_lookup in H0. discriminate.  
  - intros. unfold heap_dag. intros.
    simpl in H1. 
    destruct (cbn_context t) eqn:cbnteq; try discriminate. 
    destruct p.        *)

