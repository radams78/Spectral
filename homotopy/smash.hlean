-- Authors: Floris van Doorn

import homotopy.smash

open bool pointed eq equiv is_equiv sum bool prod unit circle cofiber prod.ops wedge

  /- smash A (susp B) = susp (smash A B) <- this follows from associativity and smash with S¹-/

  /- To prove: Σ(X × Y) ≃ ΣX ∨ ΣY ∨ Σ(X ∧ Y) (notation means suspension, wedge, smash),
     and both are equivalent to the reduced join -/

  /- To prove: commutative, associative -/

  /- smash A B ≃ pcofiber (pprod_of_pwedge A B) -/

namespace smash

  variables {A B : Type*}

  definition prod_of_wedge [unfold 3] (v : pwedge A B) : A × B :=
  begin
    induction v with a b ,
    { exact (a, pt) },
    { exact (pt, b) },
    { reflexivity }
  end

  variables (A B)
  definition pprod_of_pwedge [constructor] : pwedge A B →* A ×* B :=
  begin
    fconstructor,
    { exact prod_of_wedge },
    { reflexivity }
  end

  variables {A B}
  attribute pcofiber [constructor]
  definition pcofiber_of_smash [unfold 3] (x : smash A B) : pcofiber (@pprod_of_pwedge A B) :=
  begin
    induction x,
    { exact pushout.inr (a, b) },
    { exact pushout.inl ⋆ },
    { exact pushout.inl ⋆ },
    { symmetry, exact pushout.glue (pushout.inl a) },
    { symmetry, exact pushout.glue (pushout.inr b) }
  end

  -- move
  definition ap_eq_ap011 {A B C X : Type} (f : A → B → C) (g : X → A) (h : X → B) {x x' : X}
    (p : x = x') : ap (λx, f (g x) (h x)) p = ap011 f (ap g p) (ap h p) :=
  by induction p; reflexivity

  definition smash_of_pcofiber_glue [unfold 3] (x : pwedge A B) :
    Point (smash A B) = smash.mk (prod_of_wedge x).1 (prod_of_wedge x).2  :=
  begin
    induction x with a b: esimp,
    { apply gluel' },
    { apply gluer' },
    { apply eq_pathover_constant_left, refine _ ⬝hp (ap_eq_ap011 smash.mk _ _ _)⁻¹,
      rewrite [ap_compose' prod.pr1, ap_compose' prod.pr2],
      -- TODO: define elim_glue for wedges and remove k in krewrite
      krewrite [pushout.elim_glue], esimp, apply vdeg_square,
      exact !con.right_inv ⬝ !con.right_inv⁻¹ }
  end

  definition smash_of_pcofiber [unfold 3] (x : pcofiber (pprod_of_pwedge A B)) : smash A B :=
  begin
    induction x with x x,
    { exact smash.mk pt pt },
    { exact smash.mk x.1 x.2 },
    { exact smash_of_pcofiber_glue x }
  end

  definition pcofiber_of_smash_of_pcofiber (x : pcofiber (pprod_of_pwedge A B)) :
    pcofiber_of_smash (smash_of_pcofiber x) = x :=
  begin
    induction x with x x,
    { refine (pushout.glue pt)⁻¹ },
    { exact sorry },
    { exact sorry }
  end

  definition smash_of_pcofiber_of_smash (x : smash A B) :
    smash_of_pcofiber (pcofiber_of_smash x) = x :=
  begin
    induction x,
    { reflexivity },
    { apply gluel },
    { apply gluer },
    { apply eq_pathover_id_right, refine ap_compose smash_of_pcofiber _ _ ⬝ph _,
      refine ap02 _ !elim_gluel ⬝ph _, refine !ap_inv ⬝ph _, refine !pushout.elim_glue⁻² ⬝ph _,
      esimp, apply square_of_eq, refine !idp_con ⬝ _ ⬝ whisker_right _ !inv_con_inv_right⁻¹,
      exact !inv_con_cancel_right⁻¹ },
    { apply eq_pathover_id_right, refine ap_compose smash_of_pcofiber _ _ ⬝ph _,
      refine ap02 _ !elim_gluer ⬝ph _, refine !ap_inv ⬝ph _, refine !pushout.elim_glue⁻² ⬝ph _,
      esimp, apply square_of_eq, refine !idp_con ⬝ _ ⬝ whisker_right _ !inv_con_inv_right⁻¹,
      exact !inv_con_cancel_right⁻¹ },
  end

  variables (A B)
  definition smash_pequiv_pcofiber : smash A B ≃* pcofiber (pprod_of_pwedge A B) :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { apply pcofiber_of_smash },
      { apply smash_of_pcofiber },
      { exact pcofiber_of_smash_of_pcofiber },
      { exact smash_of_pcofiber_of_smash }},
    { esimp, symmetry, apply pushout.glue pt }
  end

  variables {A B}

  /- smash A S¹ = susp A -/
  open susp

  definition psusp_of_smash_pcircle [unfold 2] (x : smash A S¹*) : psusp A :=
  begin
    induction x,
    { induction b, exact pt, exact merid a ⬝ (merid pt)⁻¹ },
    { exact pt },
    { exact pt },
    { reflexivity },
    { induction b, reflexivity, apply eq_pathover_constant_right, apply hdeg_square,
      exact !elim_loop ⬝ !con.right_inv }
  end

  definition smash_pcircle_of_psusp [unfold 2] (x : psusp A) : smash A S¹* :=
  begin
    induction x,
    { exact pt },
    { exact pt },
    { exact gluel' pt a ⬝ ap (smash.mk a) loop ⬝ gluel' a pt },
  end

exit -- the definitions below compile, but take a long time to do so and have sorry's in them
  definition smash_pcircle_of_psusp_of_smash_pcircle_pt [unfold 3] (a : A) (x : S¹*) :
    smash_pcircle_of_psusp (psusp_of_smash_pcircle (smash.mk a x)) = smash.mk a x :=
  begin
    induction x,
    { exact gluel' pt a },
    { exact abstract begin apply eq_pathover,
      refine ap_compose smash_pcircle_of_psusp _ _ ⬝ph _,
      refine ap02 _ (elim_loop north (merid a ⬝ (merid pt)⁻¹)) ⬝ph _,
      refine !ap_con ⬝ (!elim_merid ◾ (!ap_inv ⬝ !elim_merid⁻²)) ⬝ph _,
      -- make everything below this a lemma defined by path induction?
      apply square_of_eq, rewrite [+con.assoc], apply whisker_left, apply whisker_left,
      symmetry, apply con_eq_of_eq_inv_con, esimp, apply con_eq_of_eq_con_inv,
      refine _⁻² ⬝ !con_inv, refine _ ⬝ !con.assoc,
      refine _ ⬝ whisker_right _ !inv_con_cancel_right⁻¹, refine _ ⬝ !con.right_inv⁻¹,
      refine !con.right_inv ◾ _, refine _ ◾ !con.right_inv,
      refine !ap_mk_right ⬝ !con.right_inv end end }
  end

  definition smash_pcircle_of_psusp_of_smash_pcircle_gluer_base (b : S¹*)
    : square (smash_pcircle_of_psusp_of_smash_pcircle_pt (Point A) b)
             (gluer pt)
             (ap smash_pcircle_of_psusp (ap (λ a, psusp_of_smash_pcircle a) (gluer b)))
             (gluer b) :=
  begin
    refine ap02 _ !elim_gluer ⬝ph _,
    induction b,
    { apply square_of_eq, exact whisker_right _ !con.right_inv },
    { apply square_pathover', exact sorry }
  end

  definition smash_pcircle_pequiv [constructor] (A : Type*) : smash A S¹* ≃* psusp A :=
  begin
    fapply pequiv_of_equiv,
    { fapply equiv.MK,
      { exact psusp_of_smash_pcircle },
      { exact smash_pcircle_of_psusp },
      { exact abstract begin intro x, induction x,
        { reflexivity },
        { exact merid pt },
        { apply eq_pathover_id_right,
          refine ap_compose psusp_of_smash_pcircle _ _ ⬝ph _,
          refine ap02 _ !elim_merid ⬝ph _,
          rewrite [↑gluel', +ap_con, +ap_inv, -ap_compose'],
          refine (_ ◾ _⁻² ◾ _ ◾ (_ ◾ _⁻²)) ⬝ph _,
          rotate 5, do 2 apply elim_gluel, esimp, apply elim_loop, do 2 apply elim_gluel,
          refine idp_con (merid a ⬝ (merid (Point A))⁻¹) ⬝ph _,
          apply square_of_eq, refine !idp_con ⬝ _⁻¹, apply inv_con_cancel_right } end end },
      { intro x, induction x using smash.rec,
        { exact smash_pcircle_of_psusp_of_smash_pcircle_pt a b },
        { exact gluel pt },
        { exact gluer pt },
        { apply eq_pathover_id_right,
          refine ap_compose smash_pcircle_of_psusp _ _ ⬝ph _,
          refine ap02 _ !elim_gluel ⬝ph _,
          esimp, apply whisker_rt, exact vrfl },
        { apply eq_pathover_id_right,
          refine ap_compose smash_pcircle_of_psusp _ _ ⬝ph _,
          refine ap02 _ !elim_gluer ⬝ph _,
          induction b,
          { apply square_of_eq, exact whisker_right _ !con.right_inv },
          { exact sorry}
          }}},
    { reflexivity }
  end

end smash
-- (X × A) → Y ≃ X → A → Y
