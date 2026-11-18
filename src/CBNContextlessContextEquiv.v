From AbsMach Require Import AbstractMachine CBNEvaluationContexts CBNEvaluationContextless. 


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

Lemma multistep_cbn_equiv : 
  forall n C, 
    multistep_cbn_configuration_contextless n C = reduce_configuration_cbn_multistep n C.
Proof.
  induction n; intros; simpl; try reflexivity.
  destruct C. destruct p. rewrite contextless_step_red_config_equiv.
  destruct (reduce_configuration_cbn (h, h0, n0)); try reflexivity.
  eapply IHn.
Qed.   