/-
Copyright (c) 2015 Egbert Rijke. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke

Basic concepts of group theory
-/

import algebra.group_theory

open eq algebra is_trunc sigma sigma.ops prod trunc

namespace group

  /- #Subgroups -/
  /-- Recall that a subtype of a type A is the same thing as a family of mere propositions over A. Thus, we define a subgroup of a group G to be a family of mere propositions over (the underlying type of) G, closed under the constants and operations --/

  /-- Question: Why is this called subgroup_rel. Because it is a unary relation? --/
  structure subgroup_rel (G : Group) : Type :=
    (R : G → Prop)
    (Rone : R one)
    (Rmul : Π{g h}, R g → R h → R (g * h))
    (Rinv : Π{g}, R g → R (g⁻¹))

  attribute subgroup_rel.R [coercion]

  /-- Every group G has at least two subgroups, the trivial subgroup containing only one, and the full subgroup. --/
  definition trivial_subgroup.{u} (G : Group.{u}) : subgroup_rel.{u u} G :=
  begin
    fapply subgroup_rel.mk,
    { intro g, fapply trunctype.mk, exact (g = one), exact _ },
    { esimp },
    { intros g h p q, esimp at *, rewrite p, rewrite q, exact mul_one one},
    { intros g p, esimp at *, rewrite p, exact one_inv }
  end

  definition is_trivial_subgroup (G : Group) (R : subgroup_rel G) : Type :=
  (Π g : G, R g → g = 1)

  definition full_subgroup.{u} (G : Group.{u}) : subgroup_rel.{u 0} G :=
  begin
    fapply subgroup_rel.mk,
    { intro g, fapply trunctype.mk, exact unit, exact _ },
    { esimp, constructor },
    { intros g h p q, esimp, constructor },
    { intros g p, esimp, constructor }
  end

  definition is_full_subgroup (G : Group) (R : subgroup_rel G) : Prop :=
  trunctype.mk' -1 (Π g : G, R g)

  /-- Every group homomorphism f : G -> H determines a subgroup of H, the image of f, and a subgroup of G, the kernel of f. In the following definition we define the image of f. Since a subgroup is required to be closed under the group operations, showing that the image of f is closed under the group operations is part of the definition of the image of f. --/

  /-- TODO. We need to find some reasonable way of dealing with universe levels. The reason why it currently is what it is, is because lean is inflexible with universe leves once tactic mode is started --/
  definition image_subgroup.{u1 u2} {G : Group.{u1}} {H : Group.{u2}} (f : G →g H) : subgroup_rel.{u2 (max u1 u2)} H :=
    begin
      fapply subgroup_rel.mk,
        -- definition of the subset
      { intro h, apply ttrunc, exact fiber f h},
        -- subset contains 1
      { apply trunc.tr, fapply fiber.mk, exact 1, apply respect_one},
        -- subset is closed under multiplication
      { intro h h', intro u v,
        induction u with p, induction v with q,
        induction p with x p, induction q with y q,
        induction p, induction q,
        apply tr, apply fiber.mk (x * y), apply respect_mul},
        -- subset is closed under inverses
      { intro g, intro t, induction t, induction a with x p, induction p,
        apply tr, apply fiber.mk x⁻¹, apply respect_inv }
    end

  section kernels

  variables {G₁ G₂ : Group}

  -- TODO: maybe define this in more generality for pointed sets?
  definition kernel_pred [constructor] (φ : G₁ →g G₂) (g : G₁) : Prop := trunctype.mk (φ g = 1) _

  theorem kernel_mul (φ : G₁ →g G₂) (g h : G₁) (H₁ : kernel_pred φ g) (H₂ : kernel_pred φ h) : kernel_pred φ (g *[G₁] h) :=
  begin
    esimp at *,
    exact calc
      φ (g * h) = (φ g) * (φ h) : to_respect_mul
            ... = 1 * (φ h)     : H₁
            ... = 1 * 1         : H₂
            ... = 1             : one_mul
  end

  theorem kernel_inv (φ : G₁ →g G₂) (g : G₁) (H : kernel_pred φ g) : kernel_pred φ (g⁻¹) :=
  begin
    esimp at *,
    exact calc
      φ g⁻¹ = (φ g)⁻¹ : to_respect_inv
        ... = 1⁻¹     : H
        ... = 1       : one_inv
  end

  definition kernel_subgroup [constructor] (φ : G₁ →g G₂) : subgroup_rel G₁ :=
  ⦃ subgroup_rel,
    R := kernel_pred φ,
    Rone := respect_one φ,
    Rmul := kernel_mul φ,
    Rinv := kernel_inv φ
  ⦄

  end kernels

  /-- Now we should be able to show that if f is a homomorphism for which the kernel is trivial and the image is full, then f is an isomorphism, except that no one defined the proposition that f is an isomorphism :/ --/
  -- definition is_iso_from_kertriv_imfull {G H : Group} (f : G →g H) : is_trivial_subgroup G (kernel f) → is_full_subgroup H (image_subgroup f) → unit /- replace unit by is_isomorphism f -/ := sorry

  /- #Normal subgroups -/

  /-- Next, we formalize some aspects of normal subgroups. Recall that a normal subgroup H of a group G is a subgroup which is invariant under all inner automorophisms on G. --/

  definition is_normal [constructor] {G : Group} (R : G → Prop) : Prop :=
  trunctype.mk (Π{g} h, R g → R (h * g * h⁻¹)) _

  structure normal_subgroup_rel (G : Group) extends subgroup_rel G :=
    (is_normal_subgroup : is_normal R)

  attribute subgroup_rel.R [coercion]
  abbreviation subgroup_to_rel      [unfold 2] := @subgroup_rel.R
  abbreviation subgroup_has_one     [unfold 2] := @subgroup_rel.Rone
  abbreviation subgroup_respect_mul [unfold 2] := @subgroup_rel.Rmul
  abbreviation subgroup_respect_inv [unfold 2] := @subgroup_rel.Rinv
  abbreviation is_normal_subgroup   [unfold 2] := @normal_subgroup_rel.is_normal_subgroup

  variables {G G' : Group} (H : subgroup_rel G) (N : normal_subgroup_rel G) {g g' h h' k : G}
            {A B : AbGroup}

  theorem is_normal_subgroup' (h : G) (r : N g) : N (h⁻¹ * g * h) :=
  inv_inv h ▸ is_normal_subgroup N h⁻¹ r

  definition normal_subgroup_rel_ab.{u} [constructor] (R : subgroup_rel.{_ u} A)
    : normal_subgroup_rel.{_ u} A :=
  ⦃normal_subgroup_rel, R,
    is_normal_subgroup := abstract begin
      intros g h r, xrewrite [mul.comm h g, mul_inv_cancel_right], exact r
      end end⦄

  theorem is_normal_subgroup_rev (h : G) (r : N (h * g * h⁻¹)) : N g :=
  have H : h⁻¹ * (h * g * h⁻¹) * h = g, from calc
    h⁻¹ * (h * g * h⁻¹) * h = h⁻¹ * (h * g) * h⁻¹ * h : by rewrite [-mul.assoc h⁻¹]
                        ... = h⁻¹ * (h * g)           : by rewrite [inv_mul_cancel_right]
                        ... = g                       : inv_mul_cancel_left,
  H ▸ is_normal_subgroup' N h r

  theorem is_normal_subgroup_rev' (h : G) (r : N (h⁻¹ * g * h)) : N g :=
  is_normal_subgroup_rev N h⁻¹ ((inv_inv h)⁻¹ ▸ r)

  theorem normal_subgroup_insert (r : N k) (r' : N (g * h)) : N (g * (k * h)) :=
  have H1 : N ((g * h) * (h⁻¹ * k * h)), from
    subgroup_respect_mul N r' (is_normal_subgroup' N h r),
  have H2 : (g * h) * (h⁻¹ * k * h) = g * (k * h), from calc
    (g * h) * (h⁻¹ * k * h) = g * (h * (h⁻¹ * k * h))   : mul.assoc
                        ... = g * (h * (h⁻¹ * (k * h))) : by rewrite [mul.assoc h⁻¹]
                        ... = g * (k * h)               : by rewrite [mul_inv_cancel_left],
  show N (g * (k * h)), from H2 ▸ H1
  /-- In the following, we show that the kernel of any group homomorphism f : G₁ →g G₂ is a normal subgroup of G₁ --/
  theorem is_normal_subgroup_kernel {G₁ G₂ : Group} (φ : G₁ →g G₂) (g : G₁) (h : G₁)
    : kernel_pred φ g → kernel_pred φ (h * g * h⁻¹) :=
  begin
    esimp at *,
    intro p,
    exact calc
      φ (h * g * h⁻¹) = (φ (h * g)) * φ (h⁻¹)   : to_respect_mul
                  ... = (φ h) * (φ g) * (φ h⁻¹) : to_respect_mul
                  ... = (φ h) * 1 * (φ h⁻¹)     : p
                  ... = (φ h) * (φ h⁻¹)         : mul_one
                  ... = (φ h) * (φ h)⁻¹         : to_respect_inv
                  ... = 1                       : mul.right_inv
  end

  /-- Thus, we extend the kernel subgroup to a normal subgroup --/
  definition normal_subgroup_kernel [constructor] {G₁ G₂ : Group} (φ : G₁ →g G₂) : normal_subgroup_rel G₁ :=
  ⦃ normal_subgroup_rel,
    kernel_subgroup φ,
    is_normal_subgroup := is_normal_subgroup_kernel φ
  ⦄

  -- this is just (Σ(g : G), H g), but only defined if (H g) is a prop
  definition sg : Type := {g : G | H g}
  local attribute sg [reducible]
  variable {H}
  definition subgroup_one [constructor] : sg H := ⟨one, !subgroup_has_one⟩
  definition subgroup_inv [unfold 3] : sg H → sg H :=
  λv, ⟨v.1⁻¹, subgroup_respect_inv H v.2⟩
  definition subgroup_mul [unfold 3 4] : sg H → sg H → sg H :=
  λv w, ⟨v.1 * w.1, subgroup_respect_mul H v.2 w.2⟩

  section
  local notation 1 := subgroup_one
  local postfix ⁻¹ := subgroup_inv
  local infix * := subgroup_mul

  theorem subgroup_mul_assoc (g₁ g₂ g₃ : sg H) : g₁ * g₂ * g₃ = g₁ * (g₂ * g₃) :=
  subtype_eq !mul.assoc

  theorem subgroup_one_mul (g : sg H) : 1 * g = g :=
  subtype_eq !one_mul

  theorem subgroup_mul_one (g : sg H) : g * 1 = g :=
  subtype_eq !mul_one

  theorem subgroup_mul_left_inv (g : sg H) : g⁻¹ * g = 1 :=
  subtype_eq !mul.left_inv

  theorem subgroup_mul_comm {G : AbGroup} {H : subgroup_rel G} (g h : sg H)
    : g * h = h * g :=
  subtype_eq !mul.comm

  end

  variable (H)
  definition group_sg [constructor] : group (sg H) :=
  group.mk subgroup_mul _ subgroup_mul_assoc subgroup_one subgroup_one_mul subgroup_mul_one
           subgroup_inv subgroup_mul_left_inv

  definition subgroup [constructor] : Group :=
  Group.mk _ (group_sg H)

  definition ab_group_sg [constructor] {G : AbGroup} (H : subgroup_rel G)
    : ab_group (sg H) :=
  ⦃ab_group, group_sg H, mul_comm := subgroup_mul_comm⦄

  definition ab_subgroup [constructor] {G : AbGroup} (H : subgroup_rel G)
    : AbGroup :=
  AbGroup.mk _ (ab_group_sg H)

  definition kernel {G H : Group} (f : G →g H) : Group := subgroup (kernel_subgroup f)

  definition ab_kernel {G H : AbGroup} (f : G →g H) : AbGroup := ab_subgroup (kernel_subgroup f)

  definition incl_of_subgroup [constructor] {G : Group} (H : subgroup_rel G) : subgroup H →g G :=
  begin
    fapply homomorphism.mk,
      -- the underlying function
    { intro h, induction h with g, exact g},
      -- is a homomorphism
    intro g h, reflexivity
  end

  definition subgroup_rel_of_subgroup {G : Group} (H1 H2 : subgroup_rel G) (hyp : Π (g : G), subgroup_rel.R H1 g → subgroup_rel.R H2 g) : subgroup_rel (subgroup H2) :=
  subgroup_rel.mk
      -- definition of the subset
    (λ h, H1 (incl_of_subgroup H2 h))
      -- contains 1
    (subgroup_has_one H1)
      -- closed under multiplication
    (λ g h p q, subgroup_respect_mul H1 p q)
      -- closed under inverses
    (λ h p, subgroup_respect_inv H1 p)

  definition image {G H : Group} (f : G →g H) : Group :=
    subgroup (image_subgroup f)

  definition AbGroup_of_Group.{u} (G : Group.{u}) (H : Π (g h : G), mul g h = mul h g) : AbGroup.{u} :=
  begin
    induction G,
    induction struct,
    fapply AbGroup.mk,
    exact carrier,
    fapply ab_group.mk,
    repeat assumption,
    exact H
  end

  definition ab_image {G : AbGroup} {H : Group} (f : G →g H) : AbGroup :=
  AbGroup_of_Group (image f)
  begin
    intro g h,
    induction g with x t, induction h with y s,
    fapply subtype_eq,
    induction t with p, induction s with q, induction p with g p, induction q with h q, induction p, induction q,
    refine (((respect_mul f g h)⁻¹ ⬝ _) ⬝ (respect_mul f h g)),
    apply (ap f),
    induction G, induction struct, apply mul_comm
  end

  definition image_incl {G H : Group} (f : G →g H) : image f →g H :=
    incl_of_subgroup (image_subgroup f)

  definition comm_image_incl {A B : AbGroup} (f : A →g B) : ab_image f →g B := incl_of_subgroup (image_subgroup f)

  definition hom_lift {G H : Group} (f : G →g H) (K : subgroup_rel H) (Hyp : Π (g : G), K (f g)) : G →g subgroup K :=
  begin
    fapply homomorphism.mk,
    intro g,
    fapply sigma.mk,
    exact f g,
    fapply Hyp,
    intro g h, apply subtype_eq, esimp, apply respect_mul
  end

  definition image_lift {G H : Group} (f : G →g H) : G →g image f :=
  begin
    fapply hom_lift f,
    intro g,
    apply tr,
    fapply fiber.mk,
    exact g, reflexivity
  end

  definition is_surjective_image_lift {G H : Group} (f : G →g H) : is_surjective (image_lift f) :=
  begin
    intro h,
    induction h with h p, induction p with x, induction x with g p,
    fapply image.mk,
    exact g, induction p, reflexivity
  end

  definition image_factor {G H : Group} (f : G →g H) : f = (image_incl f) ∘g (image_lift f) :=
  begin
    fapply homomorphism_eq,
    reflexivity
  end

  definition image_incl_injective {G H : Group} (f : G →g H) : Π (x y : image f), (image_incl f x = image_incl f y) → (x = y) :=
  begin
    intro x y,
    intro p,
    fapply subtype_eq,
    exact p
  end

  definition image_incl_eq_one {G H : Group} (f : G →g H) : Π (x : image f), (image_incl f x = 1) → x = 1 :=
  begin
    intro x,
    fapply image_incl_injective f x 1,
  end

end group
