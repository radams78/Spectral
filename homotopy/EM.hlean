-- Authors: Floris van Doorn

import homotopy.EM ..move_to_lib algebra.category.functor.equivalence

open eq equiv is_equiv algebra group nat pointed EM.ops is_trunc trunc susp function

namespace EM

  definition EMadd1_functor_succ [unfold_full] {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    EMadd1_functor φ (succ n) ~* ptrunc_functor (n+2) (psusp_functor (EMadd1_functor φ n)) :=
  by reflexivity

  definition EM1_functor_gid (G : Group) : EM1_functor (gid G) ~* !pid :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x,
      { reflexivity },
      { apply eq_pathover_id_right, apply hdeg_square, apply elim_pth, },
      { apply @is_prop.elim, apply is_trunc_pathover }},
    { reflexivity },
  end

  definition EMadd1_functor_gid (G : AbGroup) (n : ℕ) : EMadd1_functor (gid G) n ~* !pid :=
  begin
    induction n with n p,
    { apply EM1_functor_gid },
    { refine !EMadd1_functor_succ ⬝* _,
      refine ptrunc_functor_phomotopy _ (psusp_functor_phomotopy p ⬝* !psusp_functor_pid) ⬝* _,
      apply ptrunc_functor_pid }
  end

  definition EM_functor_gid (G : AbGroup) (n : ℕ) : EM_functor (gid G) n ~* !pid :=
  begin
    cases n with n,
    { apply pmap_of_homomorphism_gid },
    { apply EMadd1_functor_gid }
  end

  definition EM1_functor_gcompose {G H K : Group} (ψ : H →g K) (φ : G →g H) :
    EM1_functor (ψ ∘g φ) ~* EM1_functor ψ ∘* EM1_functor φ :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x,
      { reflexivity },
      { apply eq_pathover, apply hdeg_square, esimp,
        refine !elim_pth ⬝ _ ⬝ (ap_compose (EM1_functor ψ) _ _)⁻¹,
        refine _ ⬝ ap02 _ !elim_pth⁻¹, exact !elim_pth⁻¹ },
      { apply @is_prop.elim, apply is_trunc_pathover }},
    { reflexivity },
  end

  definition EMadd1_functor_gcompose {G H K : AbGroup} (ψ : H →g K) (φ : G →g H) (n : ℕ) :
    EMadd1_functor (ψ ∘g φ) n ~* EMadd1_functor ψ n ∘* EMadd1_functor φ n :=
  begin
    induction n with n p,
    { apply EM1_functor_gcompose },
    { refine !EMadd1_functor_succ ⬝* _,
      refine ptrunc_functor_phomotopy _ (psusp_functor_phomotopy p ⬝* !psusp_functor_pcompose) ⬝* _,
      apply ptrunc_functor_pcompose }
  end

  definition EM_functor_gcompose {G H K : AbGroup} (ψ : H →g K) (φ : G →g H) (n : ℕ) :
    EM_functor (ψ ∘g φ) n ~* EM_functor ψ n ∘* EM_functor φ n :=
  begin
    cases n with n,
    { apply pmap_of_homomorphism_gcompose },
    { apply EMadd1_functor_gcompose }
  end

  definition EM1_functor_phomotopy {G H : Group} {φ ψ : G →g H} (p : φ ~ ψ) :
    EM1_functor φ ~* EM1_functor ψ :=
  begin
    fapply phomotopy.mk,
    { intro x, induction x,
      { reflexivity },
      { apply eq_pathover, apply hdeg_square, esimp,
        refine !elim_pth ⬝ _ ⬝ !elim_pth⁻¹, exact ap pth (p g) },
      { apply @is_prop.elim, apply is_trunc_pathover }},
    { reflexivity },
  end

  definition EMadd1_functor_phomotopy {G H : AbGroup} {φ ψ : G →g H} (p : φ ~ ψ) (n : ℕ) :
    EMadd1_functor φ n ~* EMadd1_functor ψ n :=
  begin
    induction n with n q,
    { exact EM1_functor_phomotopy p },
    { exact ptrunc_functor_phomotopy _ (psusp_functor_phomotopy q) }
  end

  definition EM_functor_phomotopy {G H : AbGroup} {φ ψ : G →g H} (p : φ ~ ψ) (n : ℕ) :
    EM_functor φ n ~* EM_functor ψ n :=
  begin
    cases n with n,
    { exact pmap_of_homomorphism_phomotopy p },
    { exact EMadd1_functor_phomotopy p n }
  end

  definition EM_equiv_EM {G H : AbGroup} (φ : G ≃g H) (n : ℕ) : K G n ≃* K H n :=
  begin
    fapply pequiv.MK,
    { exact EM_functor φ n },
    { exact EM_functor φ⁻¹ᵍ n },
    { intro x, refine (EM_functor_gcompose φ⁻¹ᵍ φ n)⁻¹* x ⬝ _,
      refine _ ⬝ EM_functor_gid G n x,
      refine EM_functor_phomotopy _ n x,
      rexact left_inv φ },
    { intro x, refine (EM_functor_gcompose φ φ⁻¹ᵍ n)⁻¹* x ⬝ _,
      refine _ ⬝ EM_functor_gid H n x,
      refine EM_functor_phomotopy _ n x,
      rexact right_inv φ }
  end

  definition is_equiv_EM_functor {G H : AbGroup} (φ : G →g H) [H2 : is_equiv φ] (n : ℕ) :
    is_equiv (EM_functor φ n) :=
  to_is_equiv (EM_equiv_EM (isomorphism.mk φ H2) n)


  definition fundamental_group_EM1' (G : Group) : G ≃g π₁ (EM1 G) :=
  (fundamental_group_EM1 G)⁻¹ᵍ

  definition ghomotopy_group_EMadd1' (G : AbGroup) (n : ℕ) : G ≃g πg[n+1] (EMadd1 G n) :=
  begin
    change G ≃g π₁ (Ω[n] (EMadd1 G n)),
    refine _ ⬝g homotopy_group_isomorphism_of_pequiv 0 (loopn_EMadd1_pequiv_EM1 G n),
    apply fundamental_group_EM1'
  end

  definition homotopy_group_functor_EM1_functor {G H : Group} (φ : G →g H) :
    π→g[1] (EM1_functor φ) ∘ fundamental_group_EM1' G ~ fundamental_group_EM1' H ∘ φ :=
  begin
    intro g, apply ap tr, exact !idp_con ⬝ !elim_pth,
  end

  section
  infix ` ⬝hty `:75 := homotopy.trans
  postfix `⁻¹ʰᵗʸ`:(max+1) := homotopy.symm

  definition ghomotopy_group_EMadd1'_0 (G : AbGroup) :
    ghomotopy_group_EMadd1' G 0 ~ fundamental_group_EM1' G :=
  begin
    refine _ ⬝hty id_compose _,
    unfold [ghomotopy_group_EMadd1'],
    apply hwhisker_right (fundamental_group_EM1' G),
    refine _ ⬝hty trunc_functor_id _ _,
    exact trunc_functor_homotopy _ ap1_pid,
  end

  definition loopn_EMadd1_pequiv_EM1_succ (G : AbGroup) (n : ℕ) :
    loopn_EMadd1_pequiv_EM1 G (succ n) ~* (loopn_succ_in (EMadd1 G (succ n)) n)⁻¹ᵉ* ∘*
      Ω→[n] (loop_EMadd1 G n) ∘* loopn_EMadd1_pequiv_EM1 G n :=
  by reflexivity

  -- definition is_trunc_EMadd1' [instance] (G : AbGroup) (n : ℕ) : is_trunc (succ n) (EMadd1 G n) :=
  -- is_trunc_EMadd1 G n

  definition loop_EMadd1_succ (G : AbGroup) (n : ℕ) :
    loop_EMadd1 G (n+1) ~* (loop_ptrunc_pequiv (n+1+1) (psusp (EMadd1 G (n+1))))⁻¹ᵉ* ∘*
    freudenthal_pequiv (EMadd1 G (n+1)) (add_mul_le_mul_add n 1 1) ∘*
    (ptrunc_pequiv (n+1+1) (EMadd1 G (n+1)))⁻¹ᵉ* :=
  by reflexivity

  definition ap1_EMadd1_natural {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    Ω→ (EMadd1_functor φ (succ n)) ∘* loop_EMadd1 G n ~* loop_EMadd1 H n ∘* EMadd1_functor φ n :=
  begin
    refine pwhisker_right _ (ap1_phomotopy !EMadd1_functor_succ) ⬝* _,
    induction n with n IH,
    { refine pwhisker_left _ !hopf.to_pmap_delooping_pinv ⬝* _ ⬝*
             pwhisker_right _ !hopf.to_pmap_delooping_pinv⁻¹*,
      refine !loop_psusp_unit_natural⁻¹* ⬝h* _,
      apply ap1_psquare,
      apply ptr_natural },
    { refine pwhisker_left _ !loop_EMadd1_succ ⬝* _ ⬝* pwhisker_right _ !loop_EMadd1_succ⁻¹*,
      refine _ ⬝h* !ap1_ptrunc_functor,
      refine (@(ptrunc_pequiv_natural (n+1+1) _) _ _)⁻¹ʰ* ⬝h* _,
      refine pwhisker_left _ !to_pmap_freudenthal_pequiv ⬝* _ ⬝*
             pwhisker_right _ !to_pmap_freudenthal_pequiv⁻¹*,
      apply ptrunc_functor_psquare,
      exact !loop_psusp_unit_natural⁻¹* }
  end

  definition apn_EMadd1_pequiv_EM1_natural {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    Ω→[n] (EMadd1_functor φ n) ∘* loopn_EMadd1_pequiv_EM1 G n ~*
    loopn_EMadd1_pequiv_EM1 H n ∘* EM1_functor φ :=
  begin
    induction n with n IH,
    { reflexivity },
    { refine pwhisker_left _ !loopn_EMadd1_pequiv_EM1_succ ⬝* _,
      refine _ ⬝* pwhisker_right _ !loopn_EMadd1_pequiv_EM1_succ⁻¹*,
      refine _ ⬝h* !loopn_succ_in_inv_natural,
      exact IH ⬝h* (apn_psquare n !ap1_EMadd1_natural) }
  end

  definition homotopy_group_functor_EMadd1_functor {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    π→g[n+1] (EMadd1_functor φ n) ∘ ghomotopy_group_EMadd1' G n ~
    ghomotopy_group_EMadd1' H n ∘ φ :=
  begin
    refine hwhisker_left _ (to_fun_isomorphism_trans _ _) ⬝hty _ ⬝hty
           hwhisker_right _ (to_fun_isomorphism_trans _ _)⁻¹ʰᵗʸ,
    refine htyhcompose _ (homotopy_group_homomorphism_psquare 1 (apn_EMadd1_pequiv_EM1_natural φ n)),
    apply homotopy_group_functor_EM1_functor
  end

  definition homotopy_group_functor_EMadd1_functor' {G H : AbGroup} (φ : G →g H) (n : ℕ) :
    φ ∘ (ghomotopy_group_EMadd1' G n)⁻¹ᵍ ~
      (ghomotopy_group_EMadd1' H n)⁻¹ᵍ ∘ π→g[n+1] (EMadd1_functor φ n) :=
  htyhinverse (homotopy_group_functor_EMadd1_functor φ n)

  -- definition EM_functor_equiv (n : ℕ) (G H : AbGroup) : (G →g H) ≃ (EMadd1 G (n+1) →* EMadd1 H (n+1)) :=
  -- begin
  --   fapply equiv.MK,
  --   { intro φ, exact EMadd1_functor φ (n+1) },
  --   { intro f, },
  --   { },
  --   { }
  -- end

  definition EMadd1_functor_homotopy_group_functor {X Y : Type*} (f : X →* Y) (n : ℕ)
    [is_conn (n+1) X] [is_trunc (n+1+1) X] [is_conn (n+1) Y] [is_trunc (n+1+1) Y] :
    f ∘* EMadd1_pequiv_type X n ~* EMadd1_pequiv_type Y n ∘* EMadd1_functor (π→g[n+2] f) (succ n) :=
  begin

  end

  -- definition EMadd1_pmap {G : AbGroup} {X : Type*} (n : ℕ)
  --   (e : Ω[succ n] X ≃* G)
  --   (r : Πp q, e (p ⬝ q) = e p * e q)
  --   [H1 : is_conn n X] [H2 : is_trunc (n.+1) X] : EMadd1 G n →* X :=
  -- begin
  --   revert X e r H1 H2, induction n with n f: intro X e r H1 H2,
  --   { exact EM1_pmap e⁻¹ᵉ* (equiv.inv_preserve_binary e concat mul r) },
  --   rewrite [EMadd1_succ],
  --   exact ptrunc.elim ((succ n).+1)
  --           (psusp.elim (f _ (EM_up e) (is_homomorphism_EM_up e r) _ _)),
  -- end

  -- definition is_set_pmap_ptruncconntype {n : ℕ₋₂} (X Y : (n.+1)-Type*[n]) : is_set (X →* Y) :=
  -- begin
  --   apply is_trunc_succ_intro,
  --   intro f g,
  --   apply @(is_trunc_equiv_closed_rev -1 (pmap_eq_equiv f g)),
  --   apply is_prop.mk,
  --   exact sorry
  -- end


  end

  /- category -/
  structure ptruncconntype' (n : ℕ₋₂) : Type :=
   (A : Type*)
   (H1 : is_trunc (n+1) A)
   (H2 : is_conn n A)

  attribute ptruncconntype'.A [coercion]
  attribute ptruncconntype'.H1 ptruncconntype'.H2 [instance]

  definition EMadd1_pequiv_ptruncconntype' {n : ℕ} (X : ptruncconntype' (n+1)) :
    EMadd1 (πag[n+2] X) (succ n) ≃* X :=
  @(EMadd1_pequiv_type X n) _ (ptruncconntype'.H1 X)

  definition is_set_pmap_ptruncconntype' {n : ℕ₋₂} (X Y : ptruncconntype' n) : is_set (X →* Y) :=
  begin
  --   apply is_trunc_succ_intro,
  --   intro f g,
  --   apply @(is_trunc_equiv_closed_rev -1 (pmap_eq_equiv f g)),
  --   apply is_prop.mk,
    exact sorry
  end

  open category
  definition precategory_ptruncconntype'.{u} [constructor] (n : ℕ₋₂) :
    precategory.{u+1 u} (ptruncconntype' n) :=
  begin
    fapply precategory.mk,
    { exact λX Y, X →* Y },
    { exact is_set_pmap_ptruncconntype' },
    { exact λX Y Z g f, g ∘* f },
    { exact λX, pid X },
    { intros, apply eq_of_phomotopy, exact !passoc⁻¹* },
    { intros, apply eq_of_phomotopy, apply pid_pcompose },
    { intros, apply eq_of_phomotopy, apply pcompose_pid }
  end

  definition cptruncconntype' [constructor] (n : ℕ₋₂) : Precategory :=
  precategory.Mk (precategory_ptruncconntype' n)

  definition tEM [constructor] (G : AbGroup) (n : ℕ) : ptruncconntype' (n.-1) :=
  ptruncconntype'.mk (EM G n) !is_trunc_EM _

  notation `cType*[`:95 n `]`:0 := cptruncconntype' n
  open functor

  definition EM_cfunctor (n : ℕ) : AbGrp ⇒ cType*[n.-1] :=
  functor.mk
    (λG, tEM G n)
    (λG H φ, EM_functor φ n)
    begin intro, fapply eq_of_phomotopy, apply EM_functor_gid end
    begin intros, fapply eq_of_phomotopy, apply EM_functor_gcompose end

  definition homotopy_group_cfunctor (n : ℕ) : cType*[n+2.-1] ⇒ AbGrp :=
  functor.mk
    (λX, πag[n+2] X)
    (λX Y f, π→g[n+2] f)
    begin intro, apply homomorphism_eq, exact to_homotopy !homotopy_group_functor_pid end
    begin intros, apply homomorphism_eq, exact to_homotopy !homotopy_group_functor_compose end

  open nat_trans category

  definition is_isomorphism_EM_cfunctor (n : ℕ) : is_equivalence (EM_cfunctor (n+2)) :=
  begin
    fapply is_equivalence.mk,
    { exact homotopy_group_cfunctor n },
    { fapply natural_iso.mk,
      { fapply nat_trans.mk,
        { intro G, exact (ghomotopy_group_EMadd1' G (n+1))⁻¹ᵍ },
        { intro G H φ, apply homomorphism_eq, exact homotopy_group_functor_EMadd1_functor' φ (n+1) }},
      { intro G, fapply iso.is_iso.mk,
        { exact ghomotopy_group_EMadd1' G (n+1) },
        { apply homomorphism_eq,
          exact to_right_inv (equiv_of_isomorphism (ghomotopy_group_EMadd1' G (n+1))), },
        { apply homomorphism_eq,
          exact to_left_inv (equiv_of_isomorphism (ghomotopy_group_EMadd1' G (n+1))), }}},
    { fapply natural_iso.mk,
      { fapply nat_trans.mk,
        { intro X, exact EMadd1_pequiv_ptruncconntype' X },
        { intro X Y f, apply eq_of_phomotopy, apply EMadd1_functor_homotopy_group_functor }},
      { intro X, fapply iso.is_iso.mk,
        { exact (EMadd1_pequiv_ptruncconntype' X)⁻¹ᵉ* },
        { apply eq_of_phomotopy, apply pleft_inv },
        { apply eq_of_phomotopy, apply pright_inv }}}
  end


end EM
