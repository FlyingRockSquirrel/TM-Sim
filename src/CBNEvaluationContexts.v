From AbsMach Require Import AbstractMachine.

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

Fixpoint addrs_context C' :=
  match C' with 
  | HCHole => ∅
  | AbsHCon C t => union (addrs_context C) (addrs t)
  | ArgHCon t C => union (addrs t) (addrs_context C)
  | LamHCon n C => addrs_context C
  end. 

Lemma cbn_context_subterm : 
  forall t C t', 
    cbn_context t = Some (C, t') ->
    Subterm t' t. 
Proof. 
  induction t; intros C t' H. 
  - simpl in *. discriminate.
  - simpl in *. 
    destruct (cbn_context t1) eqn:t1eq.
    * destruct p. destruct t1; try discriminate. 
      -- inversion H; subst. specialize (IHt1 _ _ eq_refl).
        eapply HAppSTL. eassumption.
      -- simpl in t1eq. inversion t1eq; subst. 
        inversion H; subst.   
        eapply HAppSTL. econstructor.
    * destruct t1; try discriminate.
      inversion H; subst.
      eapply HReflST.
  - simpl in *. discriminate.
  - simpl in *. inversion H; subst.
    apply HReflST.
Qed.

Lemma cbn_con_select_addr_subset : 
  forall t C t', 
  cbn_context t = Some (C, t') ->
  subseteq (addrs_context C) (addrs t). 
Proof. 
  induction t; intros C t' H0. 
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

(* Lemma cbn_context_sound : 
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
Qed.         *)

Lemma cbn_no_reduction_no_op :
  forall t C t', 
  cbn_context t = Some (C, t') ->
  t = fill_hole C t'.
Proof.
  induction t; intros C t' H0.
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
      Some (subst (HAddr (nxt Hp)) n t1, insert_heap Hp t2 (Nat.log2_up (card_dom_heap Hp)))
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



Lemma heap_growth_bounded_aux : 
  forall n t t' Hp Hp' v_size, 
    reduce_configuration_cbn_multistep n (t, Hp, v_size) = Some (t', Hp', v_size) ->
    card_dom_heap Hp' - n <= card_dom_heap Hp.
Proof.
  induction n; intros t t' Hp Hp' v_size H0. 
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
      * specialize (IHn (fill_hole e (subst (HAddr (nxt Hp)) n0 h1)) t' (insert_heap Hp h2 ( Nat.log2_up (card_dom_heap Hp))) Hp' v_size H0).
        unfold insert_heap in *. unfold card_dom_heap in *.
        unfold dom_heap in *. simpl in IHn. 
        destruct Hp; simpl in IHn.
        simpl.
        rewrite dom_insert in *.
        rewrite size_union_alt in IHn.
        rewrite size_difference_alt in IHn.
        assert (size (dom H ∩ {[nxt]}) <= 1).
        {
          transitivity (size ({[nxt]} : gset nat)).
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
  intros n t t' Hp' v_size H0. pose proof heap_growth_bounded_aux n t t' empty_heap Hp' v_size H0 as H1.
  unfold card_dom_heap in H1.
  unfold dom_heap in H1. unfold empty_heap in H1. simpl in H1. rewrite dom_empty in H1.
  rewrite size_empty in H1.
  unfold card_dom_heap. unfold dom_heap. lia.
Qed.         


Lemma term_valid_heap_reduce : 
  forall t Hp v_size t' Hp'
  (eagle_eye : heap_missless Hp), 
  term_valid_heap t Hp ->
  reduce_term t v_size Hp = Some (t', Hp') ->
  term_valid_heap t' Hp'.
Proof. 
  induction t; intros Hp v_size t' Hp' eagle_eye H0 H1. 
  - simpl in H1. discriminate. 
  - simpl in H1.  destruct t1; simpl; try discriminate. 
    destruct (parameterized_size_hterm t2 v_size <=? Nat.log2_up (card_dom_heap Hp)). 
    + simpl in *. inversion H1; subst.
      unfold term_valid_heap in *. intros.
      eapply H0. eapply subst_addr_subset. assumption.
    + simpl in *. inversion H1; subst.
      unfold term_valid_heap in *. intros.
      pose proof subst_addr_subset _ _ _ _ H.
      simpl in H2.
      unfold dom_heap. unfold insert_heap. simpl.
      destruct Hp; simpl in *. clear H1.
      rewrite elem_of_union in H2. 
      (* destruct H3. *)
      rewrite elem_of_dom. unfold is_Some. rewrite lookup_insert.
      destruct (decide (nxt = n0)).
      * eexists; reflexivity.
      * destruct H2;
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
    specialize (eagle_eye n (fst p) ltac:(rewrite lkup; simpl; reflexivity) n0 H). 
    unfold dom_heap. destruct Hp'. simpl in *.
    destruct eagle_eye. 
    rewrite elem_of_dom. unfold is_Some.
    destruct (H2 !! n0); simpl in H3; try discriminate.
    exists p0. reflexivity.   
Qed. 


Lemma config_valid_reduce : 
  forall t Hp v_size t' Hp',
  valid_config (t, Hp, v_size) ->
  reduce_term t v_size Hp = Some (t', Hp') ->
  valid_config (t', Hp', v_size).
Proof.
  destruct t; intros Hp v_size t' Hp' H0 H1; pose proof True as H. 
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
        destruct (PeanoNat.Nat.eq_dec n0 nxt).
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
        destruct (PeanoNat.Nat.eq_dec n0 nxt).
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
          exists x.1.
          unfold lookup_heap. unfold insert_heap. simpl.
          rewrite lookup_insert_ne; try done.
          {
            unfold option_map. rewrite H4. simpl. reflexivity.   
          }    
          pose proof elem_dom_heap_wf {| H := H3; nxt := nxt; wf := wf |} n'.
          simpl in H5. unfold dom_heap in H5. simpl in H5.
          specialize (H5 vld).
          lia.
        -- rewrite lookup_insert_ne in H0; try congruence.
          unfold heap_missless in full.
          specialize (full n0 t ltac:(unfold lookup_heap; simpl; eapply H0) n' H2).
          destruct full. exists x.
          unfold lookup_heap in *. unfold insert_heap. simpl.  simpl in H4. 
          rewrite lookup_insert_ne; try eassumption.
          pose proof elem_dom_heap_wf {| H := H3; nxt := nxt; wf := wf |} n'.
          simpl in H5. unfold dom_heap in H5. simpl in H5.
          destruct (elem_of_dom H3 n') as (_, edom).
          destruct (H3 !! n') eqn:teqqq; simpl in H4; try congruence.
          specialize (edom ltac:(exists p; reflexivity)).
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
    eapply (elem_of_dom H3 n0). 
    destruct (H3 !! n0); simpl in H2; try discriminate.
    exists p. reflexivity. 
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