From AbsMach Require Import AbstractMachine. 

Fixpoint cbn_contextless_step t Hp v_size :=
  match t with
  | HApp (HAbs n t1) t2 => 
      if parameterized_size_hterm t2 v_size <=? Nat.log2_up (card_dom_heap Hp) 
    then 
      Some (subst t2 n t1, Hp, v_size)
    else 
      Some (subst (HAddr (nxt Hp)) n t1, insert_heap Hp t2 (Nat.log2_up (card_dom_heap Hp)), v_size)
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

  Inductive cbn_reduce_rel (v_size : nat) : HTerm -> Heap -> HTerm -> Heap -> Prop :=
(* | CBN_no_step : 
  forall t Hp, 
  cbn_reduce_rel v_size t Hp 0 t Hp *)
| CBN_step_left : 
  forall t1 Hp t1' Hp' t2 , 
  cbn_reduce_rel v_size t1 Hp t1' Hp' ->
  cbn_reduce_rel v_size (HApp t1 t2) Hp (HApp t1' t2) Hp'
| CBN_step_fb : 
  forall n' t1' t2 Hp', 
    (* cbn_reduce_rel v_size t1 Hp (HAbs n' t1') Hp' -> *)
    parameterized_size_hterm t2 v_size <= Nat.log2_up (card_dom_heap Hp') ->
    cbn_reduce_rel v_size (HApp (HAbs n' t1') t2) Hp' (subst t2 n' t1') Hp'
| CBN_step_hb : 
  forall Hp n' t1' t2 Hp', 
    (* cbn_reduce_rel v_size t1 Hp (HAbs n' t1') Hp' -> *)
    ~ (parameterized_size_hterm t2 v_size <= Nat.log2_up (card_dom_heap Hp')) ->
    cbn_reduce_rel v_size (HApp (HAbs n' t1') t2) Hp' (subst (HAddr (nxt Hp)) n' t1') (insert_heap Hp' t2 (Nat.log2_up (card_dom_heap Hp')))
| CBN_step_ls : 
  forall n' Hp' t',
  (* cbn_reduce_rel v_size t Hp (HAddr n') Hp' -> *)
  lookup_heap Hp' n' = Some t' ->
  cbn_reduce_rel v_size (HAddr n') Hp' t' Hp'.

Inductive cbn_reduce_rel_ls (v_size : nat) : HTerm -> Heap -> HTerm -> Heap -> Prop :=
| CBN_step_left_ls : 
  forall t1 Hp t1' Hp' t2 , 
  cbn_reduce_rel_ls v_size t1 Hp t1' Hp' ->
  cbn_reduce_rel_ls v_size (HApp t1 t2) Hp (HApp t1' t2) Hp'
| CBN_step_ls_ls : 
  forall n' Hp' t',
  (* cbn_reduce_rel v_size t Hp (HAddr n') Hp' -> *)
  lookup_heap Hp' n' = Some t' ->
  cbn_reduce_rel_ls v_size (HAddr n') Hp' t' Hp'.

Inductive cbn_reduce_rel_fb (v_size : nat) : HTerm -> Heap -> HTerm -> Heap -> Prop :=
| CBN_step_left_fb : 
  forall t1 Hp t1' Hp' t2 , 
  cbn_reduce_rel_fb v_size t1 Hp t1' Hp' ->
  cbn_reduce_rel_fb v_size (HApp t1 t2) Hp (HApp t1' t2) Hp'
| CBN_step_fb_fb : 
  forall n' t1' t2 Hp', 
    (* cbn_reduce_rel v_size t1 Hp (HAbs n' t1') Hp' -> *)
    parameterized_size_hterm t2 v_size <= Nat.log2_up (card_dom_heap Hp') ->
    cbn_reduce_rel_fb v_size (HApp (HAbs n' t1') t2) Hp' (subst t2 n' t1') Hp'.

Inductive cbn_reduce_rel_sb (v_size : nat) : HTerm -> Heap -> HTerm -> Heap -> Prop :=
| CBN_step_left_sb : 
  forall t1 Hp t1' Hp' t2 , 
  cbn_reduce_rel_sb v_size t1 Hp t1' Hp' ->
  cbn_reduce_rel_sb v_size (HApp t1 t2) Hp (HApp t1' t2) Hp'
| CBN_step_sb_sb : 
  forall n' t1' t2 Hp', 
    (* cbn_reduce_rel v_size t1 Hp (HAbs n' t1') Hp' -> *)
    ~parameterized_size_hterm t2 v_size <= Nat.log2_up (card_dom_heap Hp') ->
    cbn_reduce_rel_sb v_size (HApp (HAbs n' t1') t2) Hp' (subst (HAddr (nxt Hp')) n' t1') (insert_heap Hp' t2 (Nat.log2_up (card_dom_heap Hp'))).

Lemma cbn_reduce_rel_sb_insert : 
  forall v_size t1 Hp t1' Hp', 
    cbn_reduce_rel_sb v_size t1 Hp t1' Hp' ->
    exists t n, 
      Hp' = insert_heap Hp t n.
Proof.
  intros v_size t1 Hp t1' Hp' H; induction H. 
  - eassumption.
  - exists t2. exists (Nat.log2_up (card_dom_heap Hp')). reflexivity.
Qed.   

Lemma cbn_contextless_step_heap_expand :
  forall t t' Hp Hp' v_size, 
    cbn_contextless_step t Hp v_size = Some (t', Hp', v_size) ->
    (forall n t, 
      lookup_heap Hp n = Some t ->
      lookup_heap Hp' n = Some t).
Proof.
  induction t; intros t' Hp Hp' v_size H0 n0. pose proof True as H. 
  - intros t H1. simpl in H0; try discriminate.
  - intros t H1. simpl in H0. destruct t1.
    + simpl in H0. discriminate.
    + destruct (cbn_contextless_step (HApp t1_1 t1_2) Hp v_size) eqn:cstepapp; try discriminate.
      destruct p. destruct p.
      inversion H0; subst. 
      eapply IHt1; try eassumption.
    + destruct (parameterized_size_hterm t2 v_size <=? Nat.log2_up(card_dom_heap Hp));inversion H0; subst; [eassumption|].
      inversion H0; subst. 
      eapply insert_heap_mono. assumption.
    + simpl in H0.   
      destruct (lookup_heap Hp n); try discriminate.
      inversion H0; subst.
      assumption.
  - intros t0 H1. simpl in H0. discriminate.
  - intros t H1. simpl in H0. destruct (lookup_heap Hp n); try discriminate.
    inversion H0; subst. assumption.
Qed.   

Lemma cbn_contextless_step_same_v_size : 
  forall t t' Hp Hp' vsize vsize', 
    cbn_contextless_step t Hp vsize = Some (t', Hp', vsize') ->
    vsize = vsize'.
Proof.
  induction t; intros t' Hp Hp' vsize vsize' H0. pose proof True as H.
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

Lemma cbn_reduce_rel_step_sound : 
  forall t v_size Hp t' Hp', 
    cbn_contextless_step t Hp v_size = Some (t', Hp', v_size) ->
    cbn_reduce_rel v_size t Hp  t' Hp'. 
Proof.
  induction t; intros v_size Hp t' Hp' H0; pose proof True as H.
  - simpl in H0; congruence.
  - simpl in H0. destruct t1. 
    + simpl in H0; discriminate.
    + destruct (cbn_contextless_step (HApp t1_1 t1_2) Hp v_size) eqn:stepeq; try discriminate.
      destruct p. destruct p.
      inversion H0; subst. clear H0.  
      specialize (IHt1 _ _ _ _ stepeq).
      eapply CBN_step_left; assumption.
    + destruct (parameterized_size_hterm t2 v_size <=? Nat.log2_up (card_dom_heap Hp)) eqn:szeq.
      * inversion H0; subst.
        eapply CBN_step_fb.
        eapply Nat.leb_le.
        assumption. 
      * inversion H0; subst. 
        eapply CBN_step_hb.
        unfold not. intros.
        eapply Nat.leb_le in H1. congruence.
    + simpl in H0.  
      destruct (lookup_heap Hp n) eqn:lkupn; try discriminate.
      inversion H0; subst.
      specialize (IHt1 v_size Hp' h Hp').
      simpl in IHt1.
      rewrite lkupn in IHt1.
      specialize (IHt1 eq_refl).
      eapply CBN_step_left. eassumption. 
  - simpl in H0. discriminate.
  - simpl in H0.
    destruct (lookup_heap Hp n) eqn:lkup; try discriminate.
    inversion H0; subst.
    eapply CBN_step_ls.
    apply lkup.
Qed.  

Lemma trace_valid_config_step : 
forall t t' Hp Hp' v_size, 
  valid_config (t, Hp, v_size) ->
  cbn_contextless_step t Hp v_size = Some (t', Hp', v_size) ->
  valid_config (t', Hp', v_size). 
Proof.
  induction t; intros t' Hp Hp' v_size H0 H1; pose proof True as H.
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
        destruct H5. 
        (* exists x.  *)
        unfold lookup_heap in H0. simpl in H0.
        specialize (H0 (x.1) ltac:(rewrite H5; reflexivity)).
        destruct (H4 !! n) eqn:teqq; simpl in *; try congruence. 
        exists p; reflexivity. 
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
          destruct (PeanoNat.Nat.eq_dec n0 nxt).
          - subst. rewrite lookup_insert_eq in H0.
            inversion H0; subst.
            specialize (H3 n' H2).
            unfold dom_heap in H3. simpl in H3.
            pose proof unsquash (wf_dec _ _) wf n'.
            destruct (Nat.le_dec nxt n').
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
          destruct (PeanoNat.Nat.eq_dec n0 nxt).
          - subst. rewrite lookup_insert_eq in H0.
            inversion H0; subst. 
            specialize (vld n' ltac:(simpl; set_solver)).
            unfold dom_heap in vld. simpl in vld.
            eapply elem_of_dom in vld. 
            destruct vld.
            destruct (PeanoNat.Nat.eq_dec nxt n').
            + exists t. subst. rewrite lookup_insert_eq. reflexivity.
            + exists x.1. rewrite lookup_insert_ne; try congruence.
              rewrite H4. reflexivity.  
          - rewrite lookup_insert_ne in H0; try congruence.
            pose proof full n0 t.
            unfold lookup_heap in H4. simpl in H4.
            specialize (H4 H0 n' H2).
            destruct H4.
            destruct (PeanoNat.Nat.eq_dec nxt n').
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
        destruct (decide (nxt = n0)).
        -- eexists; reflexivity.
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
        eapply elem_of_dom.
        destruct full. destruct (H2 !! n0) eqn:teqqq; simpl in H3; try congruence.
        exists p; reflexivity.   
      * specialize (vld n0 ltac:(simpl; set_solver)).
        unfold dom_heap in vld. simpl in vld .
        assumption.
  - intros. simpl in *. try discriminate.
  - intros. simpl in *.
    destruct H0 as (dag, (full, vld)).
    destruct (lookup_heap Hp n) eqn:lkupn; inversion H1; subst; split; try split; try assumption; try discriminate.
    unfold term_valid_heap; intros.
    pose proof (full n t' lkupn n0 H0).
    eapply elem_of_dom. 
    destruct H2. unfold lookup_heap in H2.
    destruct (AbstractMachine.H Hp' !! n0); simpl in H2; try congruence.
    eexists; reflexivity.   
Qed. 

Lemma trace_valid_config : 
  forall n t t' Hp Hp' v_size, 
    valid_config (t, Hp, v_size) ->
    multistep_cbn_configuration_contextless n (t, Hp, v_size) = Some (t', Hp', v_size) ->
    valid_config (t', Hp', v_size). 
Proof. 
  induction n; intros t t' Hp Hp' v_size H0 H1; pose proof True as H.  
  - simpl in H1. inversion H1; subst. assumption.
  - simpl in H1. 
    destruct (cbn_contextless_step t Hp v_size) eqn:stepeq; try discriminate.
    destruct p. destruct p.
    pose proof (cbn_contextless_step_same_v_size _ _ _ _ _ _ stepeq).
    subst.  
    pose proof trace_valid_config_step _ _ _ _ _ H0 stepeq.
    eapply IHn; [apply H2|apply H1].
Qed.    

Lemma cbn_reduce_rel_ls_no_heapmod : 
  forall vs t Hp t' Hp', 
    cbn_reduce_rel_ls vs t Hp t' Hp' ->
    Hp = Hp'.
Proof.
  intros vs t Hp t' Hp' H0. induction H0; congruence.
Qed. 

Lemma cbn_step_ls_sound : 
  forall v_size t Hp t' Hp', 
  valid_config (t, Hp, v_size) ->
  cbn_reduce_rel_ls v_size t Hp t' Hp' ->
  HT_unfold_concrete Hp t = HT_unfold_concrete Hp' t'. 
Proof.
  intros v_size t Hp t' Hp' H0 H1. pose proof True as H. induction H1. 
  - do 2 rewrite HT_unfold_concrete_app. 
    rewrite (cbn_reduce_rel_ls_no_heapmod _ _ _ _ _ H1) in *.
    rewrite IHcbn_reduce_rel_ls; try reflexivity.
    destruct H0 as (dag, (full, vld)).
    split; try split; try tauto.
    unfold term_valid_heap. intros.
    eapply (vld n ltac:(simpl; eapply elem_of_union; left; eapply H0)).     
  - eapply HT_unfold_concrete_addr; try eassumption.
Qed. 

Lemma fb_same_heap : 
  forall v_size t Hp t' Hp', 
    cbn_reduce_rel_fb v_size t Hp t' Hp' ->
    Hp = Hp'.
Proof.
  intros v_size t Hp t' Hp' H. induction H.
  - subst. reflexivity.
  - reflexivity.
Qed.       

Lemma cbn_step_fb_sound : 
  forall v_size t Hp t' Hp',
  valid_config (t, Hp, v_size) ->
  is_closed t ->
  heap_closed Hp ->
  cbn_reduce_rel_fb v_size t Hp t' Hp' ->
  forall lt lt', 
  hterm_to_term (HT_unfold_concrete Hp t) = Some lt ->
  hterm_to_term (HT_unfold_concrete Hp' t') = Some lt' ->
  t_step lt = Some lt'.
Proof.
  intros v_size t Hp t' Hp' vconfig tclos hpclos H. induction H; intros lt lt' H0 H1.
  - rewrite HT_unfold_concrete_app in H0. simpl in H0.
    rewrite HT_unfold_concrete_app in H1. simpl in H1.
    destruct (hterm_to_term (HT_unfold_concrete Hp' t2)) eqn:htt2';
    destruct (hterm_to_term (HT_unfold_concrete Hp' t1')) eqn:htt1';
    destruct (hterm_to_term (HT_unfold_concrete Hp t1)) eqn:htt1; 
    destruct (hterm_to_term (HT_unfold_concrete Hp t2)) eqn:htt2; 
    try discriminate. inversion H1; subst. inversion H0; subst.  
    pose proof fb_same_heap _ _ _ _ _ H.
    subst .
    rewrite htt2 in htt2'.
    inversion htt2'; subst.
    pose proof valid_config_app _ _ _ _ vconfig as H2.
    destruct H2 as (H2, H3).
    unfold is_closed in tclos.
    simpl in tclos.
    destruct tclos as (tclos1, tclos2).   
    specialize (IHcbn_reduce_rel_fb H2 ltac:(unfold is_closed; assumption) ltac:(assumption) t3 t0 eq_refl eq_refl).
    destruct t3; simpl in *; try congruence.
    rewrite IHcbn_reduce_rel_fb. reflexivity.        
  - rewrite HT_unfold_concrete_app in H0. simpl in H0.
    destruct (hterm_to_term (HT_unfold_concrete Hp' t2)) eqn:htt2';
    destruct (hterm_to_term (HT_unfold_concrete Hp' (HAbs n' t1'))) eqn:htt1';
    try discriminate.
    inversion H0; subst. simpl.
    unfold HT_unfold_concrete in htt1'. 
    rewrite HT_unfold_abstract_abs in htt1'.
    simpl in htt1'.  
    destruct (hterm_to_term (HT_unfold_abstract (nxt Hp') Hp' t1')) eqn:t1destruct; try discriminate.
    inversion htt1'; subst. rewrite <- H1.
    rewrite HT_unfold_concrete_subst_comm; try assumption.
    unfold HT_unfold_concrete at 2. 
    rewrite (hterm_to_term_subst_comm _ _ _ _ n' htt2' t1destruct).
    reflexivity.  
Qed. 

Lemma cbn_step_sb_sound : 
  forall v_size t Hp t' Hp',
  valid_config (t, Hp, v_size) ->
  is_closed t ->
  heap_closed Hp ->
  cbn_reduce_rel_sb v_size t Hp t' Hp' ->
  forall lt lt', 
  hterm_to_term (HT_unfold_concrete Hp t) = Some lt ->
  hterm_to_term (HT_unfold_concrete Hp' t') = Some lt' ->
  t_step lt = Some lt'.
Proof.
  intros v_size t Hp t' Hp' vconfig tclos hpclos H. induction H; intros lt lt' H0 H1. 
  - rewrite HT_unfold_concrete_app in H0. simpl in H0.
    rewrite HT_unfold_concrete_app in H1. simpl in H1.
    destruct (hterm_to_term (HT_unfold_concrete Hp' t2)) eqn:htt2';
    destruct (hterm_to_term (HT_unfold_concrete Hp' t1')) eqn:htt1';
    destruct (hterm_to_term (HT_unfold_concrete Hp t1)) eqn:htt1; 
    destruct (hterm_to_term (HT_unfold_concrete Hp t2)) eqn:htt2; 
    try discriminate. inversion H1; subst. inversion H0; subst.
    assert ((HT_unfold_concrete Hp t2) = (HT_unfold_concrete Hp' t2)) as uneq.
    {
      pose proof cbn_reduce_rel_sb_insert _ _ _ _ _ H.
      destruct H2 as (t5, (n0, H3)).
      subst.
      unfold HT_unfold_concrete. unfold insert_heap. simpl. unfold lookup_heap.
      simpl. rewrite lookup_insert_ne; try lia.
      pose proof unsquash (wf_dec _ _) (wf Hp) (S (nxt Hp)) ltac:(lia).
      rewrite H2. simpl.
      destruct Hp; simpl.
      destruct nxt.
      - simpl in *. unfold lookup_heap; simpl. rewrite lookup_insert_eq; try lia.
        pose proof unsquash (wf_dec _ _) (wf) 0 ltac:(lia).
        rewrite H4. simpl.
        unfold HT_unfold_concrete in htt2.
        simpl in htt2.
        unfold lookup_heap in htt2. simpl in htt2.
        rewrite H4 in htt2. simpl in htt2.
        symmetry. eapply hterm_to_term_entails_unfold_noop. eassumption.
      - simpl. unfold lookup_heap; simpl. simpl in H2.        
        pose proof unsquash (wf_dec _ _) (wf) (S nxt) ltac:(lia) as H4.
        rewrite H4.
        rewrite lookup_insert_eq; try lia. simpl.
        unfold HT_unfold_concrete in htt2.
        simpl in htt2. unfold lookup_heap in htt2. simpl in htt2. rewrite H4 in htt2.
        simpl in htt2.      
        rewrite (HT_unfold_abstract_domain_gen t2 nxt _ _ htt2 (S nxt) t5 ltac:(lia)).
        eapply HT_unfold_abstract_domain; simpl; intros.
        unfold lookup_heap. simpl.
        rewrite lookup_insert_ne; try lia. reflexivity.       
    }
    rewrite <- uneq in *. 
    rewrite htt2' in htt2. inversion htt2; subst.
    pose proof valid_config_app _ _ _ _ vconfig as H3.
    destruct H3 as (H3, H4).
    unfold is_closed in tclos.
    simpl in tclos.
    destruct tclos as (tclos1, tclos2).
    specialize (IHcbn_reduce_rel_sb H3 ltac:(unfold is_closed; eapply tclos1) hpclos t3 t0 eq_refl eq_refl).
    destruct t3; simpl in *; try congruence.
    rewrite IHcbn_reduce_rel_sb. reflexivity.  
  - rewrite HT_unfold_concrete_app in H0. simpl in H0.
    destruct (hterm_to_term (HT_unfold_concrete Hp' t2)) eqn:htt2';
    destruct (hterm_to_term (HT_unfold_concrete Hp' (HAbs n' t1'))) eqn:htt1';
    try discriminate.
    inversion H0; subst. simpl.
    unfold HT_unfold_concrete in htt1'. 
    rewrite HT_unfold_abstract_abs in htt1'.
    simpl in htt1'.  
    destruct (hterm_to_term (HT_unfold_abstract (nxt Hp') Hp' t1')) eqn:t1destruct; try discriminate.
    inversion htt1'; subst. rewrite <- H1.
    rewrite HT_unfold_concrete_subst_comm; try assumption.
    2:{ unfold heap_closed.
      intros n t0 H2. unfold insert_heap, lookup_heap in H2. simpl in H2. destruct (PeanoNat.Nat.eq_dec (nxt Hp') n); subst.
      - rewrite lookup_insert_eq in H2. simpl in H2. inversion H2; subst.
        unfold is_closed in tclos. simpl in tclos. destruct tclos as (tclos1, tclos2).
        eapply tclos2.
      - rewrite lookup_insert_ne in H2; try congruence.
        eapply (hpclos n t0 H2). }
    unfold HT_unfold_concrete at 1.
    simpl.
    unfold lookup_heap. simpl.
    rewrite lookup_insert_ne; try lia.     
    destruct Hp'. simpl.
    pose proof unsquash (wf_dec _ _) wf (S nxt) ltac:(lia) as H3.
    rewrite H3. simpl.
    unfold HT_unfold_concrete.
    simpl.     
    unfold lookup_heap. simpl.
    rewrite lookup_insert_ne; try lia.
    rewrite H3. simpl.      
    set (abr := (Nat.log2_up (card_dom_heap {| H := H2; nxt := nxt; wf := wf |})) ).
    destruct nxt.
    + simpl. unfold insert_heap. unfold lookup_heap. simpl. 
      rewrite lookup_insert_eq. simpl.
      simpl in t1destruct. unfold lookup_heap in t1destruct.
      simpl in t1destruct.   
      pose proof unsquash (wf_dec _ _) wf 0 ltac:(lia) as H4.
      rewrite H4 in t1destruct.
      simpl in t1destruct.
      rewrite (hterm_to_term_entails_unfold_noop t1' t1 t1destruct).
      unfold HT_unfold_concrete in htt2'.
      simpl in htt2'. unfold lookup_heap in htt2'.
      simpl in htt2'. rewrite H4 in htt2'.
      simpl in htt2'.
      symmetry. 
      eapply hterm_to_term_subst_comm; try eassumption.
    + simpl in t1destruct. unfold insert_heap. simpl. unfold lookup_heap.
      simpl. 
      rewrite lookup_insert_eq. simpl.
      unfold lookup_heap in t1destruct; simpl in t1destruct.
      pose proof unsquash (wf_dec _ _) wf (S nxt) ltac:(lia) as H4.
      rewrite H4 in t1destruct. simpl in t1destruct.  
      destruct (nxt =? nxt) eqn:nxteq; [|rewrite Nat.eqb_neq in nxteq; try congruence].
      assert ((HT_unfold_concrete {| H := H2; nxt := S nxt; wf := wf |} t2) = (HT_unfold_abstract nxt 
        {|
        H := <[S nxt:=(t2, abr)]> H2;
        nxt := S (S nxt);
        wf := insert_inc_next {| H := H2; nxt := S nxt; wf := wf |} t2 abr
        |} t2)) as H5.
      {
        unfold HT_unfold_concrete. simpl. 
        unfold lookup_heap. simpl. rewrite H4. simpl.       
        Search HT_unfold_abstract.
        eapply HT_unfold_abstract_domain.
        intros.
        destruct (PeanoNat.Nat.eq_dec n'0 (S nxt)); try lia.
        unfold lookup_heap. simpl. rewrite lookup_insert_ne; try congruence.    
      }
      rewrite <- H5.
      assert ((HT_unfold_abstract nxt
        {|
        H := <[S nxt:=(t2, abr)]> H2;
        nxt := S (S nxt);
        wf := insert_inc_next {| H := H2; nxt := S nxt; wf := wf |} t2 abr
        |} (HTunfold t2 (S nxt) t1')) = (HT_unfold_abstract nxt {| H := H2; nxt := S nxt; wf := wf |} t1')) as H6.
      {
        assert ((HTunfold t2 (S nxt) t1') = t1') as auxeq.
        {
          eapply HT_unfold_abstract_domain_gen; try eassumption. lia.   
        } 
          rewrite auxeq.
          eapply HT_unfold_abstract_domain;
          intros.
          unfold lookup_heap. simpl. rewrite lookup_insert_ne; try lia. reflexivity.    
      }
      rewrite H6 in *.
      unfold HT_unfold_concrete.
      symmetry. eapply hterm_to_term_subst_comm; try eassumption.  
Qed. 
