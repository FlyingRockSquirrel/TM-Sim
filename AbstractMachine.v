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

Fixpoint HTunfold substin n body :=
match body with
| HVar i => HVar i
| HApp t u => HApp (HTunfold substin n t) (HTunfold substin n u)
| HAbs n' t => HTunfold substin n t
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

Fixpoint cbn_contextless_step t Hp v_size :=
  match t with
  | HApp (HAbs n t1) t2 => 
      if parameterized_size_hterm t2 v_size <=? Nat.log2_up (card_dom_heap Hp) 
    then 
      Some (subst t2 n t1, Hp, v_size)
    else 
      Some (subst (HAddr (nxt Hp)) n t1, insert_heap Hp t2, v_size)
  | HApp t1 t2 => 
    match (cbn_contextless_step t1 Hp v_size) with
    | Some (t1', Hp', v_size) => Some (HApp t1' t2, Hp', v_size)
    | None => None
    end
  | HAddr n => 
    match lookup_heap Hp n with
    | Some t' => Some (t', Hp, v_size)
    | None => None
    end
  | _ => None
  end. 

Lemma contextless_step_red_config_equiv :
  forall t Hp v_size, 
    cbn_contextless_step t Hp v_size = reduce_configuration_cbn (t, Hp, v_size).
Proof. 
  induction t; intros.
  - simpl; reflexivity.
  - destruct (reduce_configuration_cbn (t1, Hp, v_size)) eqn:redc;[simpl|].
    + specialize (IHt1 Hp v_size). 
      rewrite redc in IHt1.
      destruct c.
      destruct p.   
      rewrite IHt1.
      destruct t1; try discriminate; [|simpl; simpl in IHt1; destruct (lookup_heap Hp n0); try discriminate; try congruence].
      simpl in redc.
      simpl.     
      destruct (match t1_1 with
        | HAbs n t1 => Some (HCHole, HApp (HAbs n t1) t1_2)
        | _ =>
        match cbn_context t1_1 with
        | Some (C, t) => Some (AbsHCon C t1_2, t)
        | None => None
        end
        end) eqn:t1mtch; try discriminate.
      destruct p. 
      destruct (reduce_term h1 v_size Hp) eqn:redt; try discriminate.
      destruct p. inversion redc; subst. simpl. reflexivity.
    + unfold reduce_configuration_cbn in redc.
      unfold reduce_configuration_cbn. simpl. 
      destruct (cbn_context t1) eqn:ctxt1.
      * destruct p.  
        destruct (reduce_term h v_size Hp) eqn:redt; try congruence;
        [destruct p; try discriminate|].
        destruct t1; try discriminate;
        rewrite redt;[ |simpl in *; inversion ctxt1; subst; simpl in redt; destruct (lookup_heap Hp n); try congruence; reflexivity].
        rewrite IHt1. simpl.
        simpl in ctxt1.
        rewrite ctxt1. rewrite redt. reflexivity.
      * destruct t1; simpl in ctxt1; try discriminate; try (simpl; reflexivity); [| simpl; destruct (parameterized_size_hterm t2 v_size <=? Nat.log2_up (card_dom_heap Hp)); try reflexivity].
        rewrite IHt1. simpl. rewrite ctxt1. reflexivity.
  - simpl. reflexivity.
  - simpl. destruct (lookup_heap Hp n); reflexivity.
Qed.  

Fixpoint multistep_cbn_configuration_contextless n C : option configuration :=
  match n with
  | 0 => Some C
  | S n' => 
    match C with
    | (t, Hp, v_size) => 
      match cbn_contextless_step t Hp v_size with
      | Some C' => multistep_cbn_configuration_contextless n' C'
      | None => None
      end
    end
  end. 

Lemma multistep_cbn_equiv : 
  forall n C, 
    multistep_cbn_configuration_contextless n C = reduce_configuration_cbn_multistep n C.
Proof.
  induction n; intros; simpl; try reflexivity.
  destruct C. destruct p. rewrite contextless_step_red_config_equiv.
  destruct (reduce_configuration_cbn (h, h0, n0)); try reflexivity.
  eapply IHn.
Qed.   


(* Inductive HReduceTerm v_size : (HTerm * Heap) -> (HTerm * Heap) -> Prop :=
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
      HReduceTerm v_size (HAddr n, Hp) (t, Hp).  *)


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

Fixpoint addrs_context C' :=
  match C' with 
  | HCHole => ∅
  | AbsHCon C t => union (addrs_context C) (addrs t)
  | ArgHCon t C => union (addrs t) (addrs_context C)
  | LamHCon n C => addrs_context C
  end. 


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

Lemma cbn_context_subterm : 
  forall t C t', 
    cbn_context t = Some (C, t') ->
    Subterm t' t. 
Proof. 
  induction t; intros. 
  - simpl in H0. discriminate.
  - simpl in H0. 
    destruct (cbn_context t1) eqn:t1eq.
    * destruct p. destruct t1; try discriminate. 
      -- inversion H0; subst. specialize (IHt1 _ _ eq_refl).
        eapply HAppSTL. eassumption.
      -- simpl in t1eq. inversion t1eq; subst. 
        inversion H0; subst.   
        eapply HAppSTL. econstructor.
    * destruct t1; try discriminate.
      inversion H0; subst.
      eapply HReflST.
  - simpl in *. discriminate.
  - simpl in *. inversion H0; subst.
    apply HReflST.
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

Lemma cbn_con_select_addr_subset : 
  forall t C t', 
  cbn_context t = Some (C, t') ->
  subseteq (addrs_context C) (addrs t). 
Proof. 
  induction t; intros. 
  - simpl in H0.  discriminate. 
  - simpl in H0. simpl. 
    destruct (cbn_context t1) eqn:t1eq; [destruct p|]. 
    + specialize (IHt1 _ _ eq_refl). 
      destruct t1; inversion H0; subst.
      * simpl in *; try discriminate. 
      * simpl. simpl in IHt1. set_solver.
      * simpl. set_solver.
      * simpl. simpl in IHt1. set_solver.
    + destruct t1; try discriminate.
      inversion H0. subst. simpl. set_solver.
  - simpl in H0. discriminate.
  - simpl in *. inversion H0; subst. simpl. set_solver.
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

Lemma config_valid_reduce : 
  forall t Hp v_size t' Hp',
  valid_config (t, Hp, v_size) ->
  reduce_term t v_size Hp = Some (t', Hp') ->
  valid_config (t', Hp', v_size).
Proof.
  destruct t.
  - intros. simpl in H1. discriminate.
  - intros. simpl in H1. destruct t1; try discriminate.
    destruct (parameterized_size_hterm t2 v_size <=? Nat.log2_up(card_dom_heap Hp)) eqn:psize.
    + inversion H1; subst.
      unfold valid_config in *. split; try split.
      * tauto. 
      * tauto.
      * destruct H0 as (dag, (full, vld)). 
        eapply (term_valid_heap_reduce _ _ v_size); [ apply full | apply vld | ].
        simpl. rewrite psize.  reflexivity.
    + destruct H0 as (dag, (full, vld)).  inversion H1; subst.
      unfold valid_config in *. split; try split.
      * unfold heap_dag. unfold term_valid_heap in vld.
        intros. unfold insert_heap in H0. unfold lookup_heap in H0.
        destruct Hp. simpl in H0. simpl in *. unfold insert_heap in H1.
        simpl in H1.
        destruct (PeanoNat.Nat.eq_dec n0 nxt0).
        -- subst. rewrite lookup_insert_eq in H0.
          inversion H0; subst. 
          specialize (vld n' ltac:(set_solver)). 
          pose proof elem_dom_heap_wf _ _ vld.
          simpl in H4. assumption.
        -- rewrite lookup_insert_ne in H0; try congruence.
          eapply dag; try eassumption.
      * unfold heap_missless. intros.
        unfold insert_heap in H0. unfold lookup_heap in H0.
        destruct Hp. simpl in H0.
        destruct (PeanoNat.Nat.eq_dec n0 nxt0).
        -- subst. rewrite lookup_insert_eq in H0.
          inversion H0; subst.
          unfold term_valid_heap in vld. 
          simpl in vld.
          specialize (vld n' ltac:(set_solver)).
          unfold dom_heap in vld. simpl in vld.
          destruct (elem_of_dom H3 n') as (edom, _).
          specialize (edom vld).
          unfold is_Some in edom.
          destruct edom.
          exists x.
          unfold lookup_heap. unfold insert_heap. simpl.
          rewrite lookup_insert_ne; try done.    
          pose proof elem_dom_heap_wf {| H := H3; nxt := nxt0; wf := wf0 |} n'.
          simpl in H5. unfold dom_heap in H5. simpl in H5.
          specialize (H5 vld).
          lia.
        -- rewrite lookup_insert_ne in H0; try congruence.
          unfold heap_missless in full.
          specialize (full n0 t ltac:(unfold lookup_heap; simpl; eapply H0) n' H2).
          destruct full. exists x.
          unfold lookup_heap in *. unfold insert_heap. simpl.  simpl in H4. 
          rewrite lookup_insert_ne; try eassumption.
          pose proof elem_dom_heap_wf {| H := H3; nxt := nxt0; wf := wf0 |} n'.
          simpl in H5. unfold dom_heap in H5. simpl in H5.
          destruct (elem_of_dom H3 n') as (_, edom).
          specialize (edom ltac:(exists x; eapply H4)).
          specialize (H5 edom). lia.
      *  eapply (term_valid_heap_reduce _ _ v_size); [ apply full | apply vld | ].
        simpl. rewrite psize.       reflexivity.
  - intros. simpl in H0. discriminate.
  - intros. simpl in H1.    
    destruct (lookup_heap Hp n) eqn:lkn; try discriminate.
    inversion H1; subst.    
    unfold valid_config in *.
    destruct H0 as (dag, (full, vld)).
    split; try split; try done.
    unfold term_valid_heap. intros.
    unfold heap_missless in full.
    specialize (full n t' lkn n0 H0).
    destruct full.
    unfold dom_heap. destruct Hp'; simpl in *.
    unfold lookup_heap in H2. simpl in H2.
    eapply (elem_of_dom H3 n0). exists x. apply H2.
Qed.            

Lemma insert_heap_mono : 
  forall n Hp t t',
    lookup_heap Hp n = Some t ->
    lookup_heap (insert_heap Hp t') n = Some t.
Proof.
  intros.
  destruct Hp; simpl. unfold lookup_heap in *. simpl in *.
  pose proof unsquash (wf_dec _ _) wf0.
  rewrite lookup_insert_ne; try eassumption.
  unfold not. intros.
  specialize (H2 n ltac:(lia)).
  congruence.
Qed.           

Lemma cbn_contextless_step_heap_expand :
  forall t t' Hp Hp' v_size, 
    cbn_contextless_step t Hp v_size = Some (t', Hp', v_size) ->
    (forall n t, 
      lookup_heap Hp n = Some t ->
      lookup_heap Hp' n = Some t).
Proof.
  induction t; intros.
  - simpl in H0; try discriminate.
  - simpl in H0. destruct t1.
    + simpl in H0. discriminate.
    + destruct (cbn_contextless_step (HApp t1_1 t1_2) Hp v_size) eqn:cstepapp; try discriminate.
      destruct p. destruct p.
      inversion H0; subst. 
      eapply IHt1; try eassumption.
    + destruct (parameterized_size_hterm t2 v_size <=? Nat.log2_up(card_dom_heap Hp));inversion H0; subst; [eassumption|].
      inversion H0; subst. 
      eapply insert_heap_mono. assumption.
    + simpl in H0.   
      destruct (lookup_heap Hp n0); try discriminate.
      inversion H0; subst.
      assumption.
  - simpl in H0. discriminate.
  - simpl in H0. destruct (lookup_heap Hp n); try discriminate.
    inversion H0; subst. assumption.
Qed.   

Lemma trace_valid_config_step : 
forall t t' Hp Hp' v_size, 
  valid_config (t, Hp, v_size) ->
  cbn_contextless_step t Hp v_size = Some (t', Hp', v_size) ->
  valid_config (t', Hp', v_size). 
Proof.
  induction t.
  - intros. simpl in *. try discriminate.
  - intros. simpl in H1. 
    destruct t1; try discriminate.
    + destruct (cbn_contextless_step (HApp t1_1 t1_2) Hp v_size) eqn:cstep; try discriminate.
      destruct p. destruct p.
      inversion H1; subst.    
      destruct H0 as (dag, (full, vld)).
      pose proof (subterm_term_valid_heap (HApp (HApp t1_1 t1_2) t2) (HApp t1_1 t1_2) Hp ltac:(eapply HAppSTL; eapply HReflST) vld) as vldt1.
      specialize (IHt1 _ _ _ _ ltac:(split; try split; try (apply dag); try (apply full); try (apply vldt1)) cstep).
      destruct IHt1 as (dag1, (full1, vld1)).
      split; try split; try assumption. 
      pose proof cbn_contextless_step_heap_expand _ _ _ _ _ cstep.
      unfold term_valid_heap. intros. simpl in H2. 
      specialize (H0 n).
      rewrite elem_of_union in H2.
      destruct H2.
      * eapply (vld1 n H2).
      * specialize (vld n ltac:(simpl; set_solver)).
        destruct Hp. destruct Hp'.
        unfold dom_heap in *. simpl in *; clear cstep.
        eapply elem_of_dom.     
        pose proof elem_of_dom H3 n.
        destruct H5.
        clear H6.
        specialize (H5 vld).
        destruct H5. exists x. unfold lookup_heap in H0. simpl in H0.
        eapply H0; eassumption.
    + destruct (parameterized_size_hterm t2 v_size <=? Nat.log2_up (card_dom_heap Hp)). 
      * inversion H1; subst.
        destruct H0 as (dag, (full, vld)).
        split; try split; try assumption.
        unfold term_valid_heap in *. intros.
        eapply vld. eapply subst_addr_subset. assumption.
      * inversion H1; subst. split; try split.
        {
          destruct H0 as (dag, (full, vld)).
          unfold heap_dag; intros.
          pose proof subterm_term_valid_heap (HApp (HAbs n t1) t2) t2 Hp ltac:(eapply HAppSTR; eapply HReflST) vld.
          destruct Hp. unfold insert_heap in H0. unfold lookup_heap in H0. simpl in H0.
          destruct (PeanoNat.Nat.eq_dec n0 nxt0).
          - subst. rewrite lookup_insert_eq in H0.
            inversion H0; subst.
            specialize (H3 n' H2).
            unfold dom_heap in H3. simpl in H3.
            pose proof unsquash (wf_dec _ _) wf0 n'.
            destruct (Nat.le_dec nxt0 n').
            + specialize (H5 l).
              eapply elem_of_dom in H3.
              destruct H3. congruence.
            + lia.
          - rewrite lookup_insert_ne in H0; try congruence.
            eapply dag; eassumption.   
        }
        {
          destruct H0 as (dag, (full, vld)).
          unfold heap_missless; intros.
          unfold lookup_heap in *; unfold insert_heap in *.
          destruct Hp; simpl in *.
          destruct (PeanoNat.Nat.eq_dec n0 nxt0).
          - subst. rewrite lookup_insert_eq in H0.
            inversion H0; subst. 
            specialize (vld n' ltac:(simpl; set_solver)).
            unfold dom_heap in vld. simpl in vld.
            eapply elem_of_dom in vld. 
            destruct vld.
            destruct (PeanoNat.Nat.eq_dec nxt0 n').
            + exists t. subst. rewrite lookup_insert_eq. reflexivity.
            + exists x. rewrite lookup_insert_ne; try congruence.
          - rewrite lookup_insert_ne in H0; try congruence.
            pose proof full n0 t.
            unfold lookup_heap in H4. simpl in H4.
            specialize (H4 H0 n' H2).
            destruct H4.
            destruct (PeanoNat.Nat.eq_dec nxt0 n').
            + subst. exists t2. rewrite lookup_insert_eq. reflexivity.
            + exists x. rewrite lookup_insert_ne; try congruence.    
        }
        unfold term_valid_heap in *. intros.
        pose proof subst_addr_subset _ _ _ _ H2.
        simpl in H3.
        unfold dom_heap. unfold insert_heap. simpl.
        destruct Hp; simpl in *. clear H1.
        rewrite elem_of_union in H3. 
        (* destruct H3. *)
        rewrite elem_of_dom. unfold is_Some. rewrite lookup_insert.
        destruct (decide (nxt0 = n0)).
        -- exists t2; reflexivity.
        -- destruct H3;
          [| rewrite elem_of_union in H1; destruct H1; [rewrite elem_of_singleton in H1; congruence|rewrite elem_of_empty in H1; contradiction]].
          destruct (H0) as (?, (?, vldt2)). 
          specialize (vldt2 n0 ltac:(eapply elem_of_union; left; eapply H1)).
          unfold dom_heap in vldt2. simpl in vldt2. rewrite elem_of_dom in vldt2.
          eapply vldt2.
    + simpl in H1. destruct (lookup_heap Hp n) eqn:lkupn; try discriminate.
      inversion H1; subst.
      destruct H0 as (dag, (full, vld)).
      split; try split; try eassumption. 
      unfold term_valid_heap; intros. simpl in H0. 
      destruct Hp'. unfold dom_heap. simpl. 
      unfold lookup_heap in lkupn.
      simpl in lkupn.  
      specialize (full n h ltac:(unfold lookup_heap; simpl; apply lkupn) n0).
      rewrite elem_of_union in H0.
      destruct H0.
      * specialize (full H0).
        unfold lookup_heap in full. simpl in full.
        eapply elem_of_dom. eapply full.
      * specialize (vld n0 ltac:(simpl; set_solver)).
        unfold dom_heap in vld. simpl in vld .
        assumption.
  - intros. simpl in *. try discriminate.
  - intros. simpl in *.
    destruct H0 as (dag, (full, vld)).
    destruct (lookup_heap Hp n) eqn:lkupn; inversion H1; subst; split; try split; try assumption; try discriminate.
    unfold term_valid_heap; intros.
    pose proof (full n t' lkupn n0 H0).
    eapply elem_of_dom. eapply H2.
Qed. 

Lemma cbn_contextless_step_same_v_size : 
  forall t t' Hp Hp' vsize vsize', 
    cbn_contextless_step t Hp vsize = Some (t', Hp', vsize') ->
    vsize = vsize'.
Proof.
  induction t; intros.
  - simpl in H0. discriminate.
  - simpl in *. destruct t1. 
    + simpl in H0. discriminate.
    + destruct (cbn_contextless_step (HApp t1_1 t1_2) Hp vsize) eqn:thing; try discriminate.
      destruct p. destruct p. inversion H0; subst.
      eapply IHt1. eapply thing.
    + destruct (parameterized_size_hterm t2 vsize <=? Nat.log2_up (card_dom_heap Hp)); inversion H0; subst; congruence. 
    + simpl in H0. destruct (lookup_heap Hp n); try discriminate; congruence.
  - simpl in H0; discriminate. 
  - simpl in H0. destruct (lookup_heap Hp n); congruence. 
Qed. 

Lemma trace_valid_config : 
  forall n t t' Hp Hp' v_size, 
    valid_config (t, Hp, v_size) ->
    multistep_cbn_configuration_contextless n (t, Hp, v_size) = Some (t', Hp', v_size) ->
    valid_config (t', Hp', v_size). 
Proof. 
  induction n; intros. 
  - simpl in H1. inversion H1; subst. assumption.
  - simpl in H1. 
    destruct (cbn_contextless_step t Hp v_size) eqn:stepeq; try discriminate.
    destruct p. destruct p.
    pose proof (cbn_contextless_step_same_v_size _ _ _ _ _ _ stepeq).
    subst.  
    pose proof trace_valid_config_step _ _ _ _ _ H0 stepeq.
    eapply IHn; [apply H2|apply H1].
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
      eapply elem_of_dom; exists x.
      unfold lookup_heap in H2. simpl in H2. eassumption.
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
      congruence.
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
        congruence.
    Unshelve. 
    all:apply 0.
Qed. 