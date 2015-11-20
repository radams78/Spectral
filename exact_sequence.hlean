/-
Authors: Floris van Doorn

Definition of exact sequences
-/

import types.int types.pointed hit.trunc

open eq pointed nat int function trunc is_trunc

namespace algebra

  definition Pointed_of_Group (G : Group) : Type* := @Pointed.mk G one
  definition Group_of_CommGroup (G : CommGroup) : Group := Group.mk G _


  structure group_homomorphism (G₁ G₂ : Group) : Type :=
    (φ : G₁ → G₂)
    (p : Π(g h : G₁), φ (g * h) = φ g * φ h)

  attribute group_homomorphism.φ [coercion]
  abbreviation group_fun [unfold 1] := @group_homomorphism.φ
  abbreviation respect_mul [unfold 1] := @group_homomorphism.p

  variables {G₁ G₂ : Group} (g h : G₁)

  theorem respect_one (φ : group_homomorphism G₁ G₂) : φ 1 = 1 :=
  mul.right_cancel
    (calc
      φ 1 * φ 1 = φ (1 * 1) : respect_mul
            ... = φ 1 : ap φ !one_mul
            ... = 1 * φ 1 : one_mul)

  local attribute Pointed_of_Group [coercion]
  definition pmap_of_group_homomorphism [constructor] (φ : group_homomorphism G₁ G₂) : G₁ →* G₂ :=
  pmap.mk φ !respect_one

end algebra

open algebra

namespace LES

  -- pointed types with additional structure
  structure PointedStructure :=
    (Z : Type)
    (carrier : Z → Type*)

  attribute PointedStructure.carrier [coercion]
  abbreviation elt_of [unfold 1] := @PointedStructure.Z
  abbreviation PS_carrier [unfold 1] := @PointedStructure.carrier

  -- pointed maps with additional structure
  structure PointedMapStructure (Z₁ Z₂ : PointedStructure) :=
    (F : elt_of Z₁ → elt_of Z₂ → Type)
    (function : Π(X₁ : elt_of Z₁) (X₂ : elt_of Z₂), F X₁ X₂ → X₁ →* X₂)

  attribute PointedMapStructure.function [coercion]
  abbreviation fun_of [unfold 1] := @PointedMapStructure.F
  abbreviation PMS_function [unfold 1] := @PointedMapStructure.function

  definition PS_Pointed [constructor] : PointedStructure :=
  PointedStructure.mk Type* id

  definition PS_Unit [constructor] : PointedStructure :=
  PointedStructure.mk (-2-Type) (λx, @Pointed.mk x !center)

  definition PS_CommGroup [constructor] : PointedStructure :=
  PointedStructure.mk CommGroup (λG, @Pointed.mk G one)

  definition PS_Group [constructor] : PointedStructure :=
  PointedStructure.mk Group (λG, @Pointed.mk G one)

  definition PMS_general [constructor] (Z₁ Z₂ : PointedStructure)
    : PointedMapStructure Z₁ Z₂ :=
  PointedMapStructure.mk (λX Y, X →* Y) (λX Y, id)

  definition PMS_Group [constructor]
    : PointedMapStructure PS_Group PS_Group :=
  PointedMapStructure.mk group_homomorphism (λX Y, pmap_of_group_homomorphism)

  section
    local attribute Group_of_CommGroup [coercion]
    definition PMS_CommGroup [constructor]
      : PointedMapStructure PS_CommGroup PS_CommGroup :=
    PointedMapStructure.mk (λX Y, group_homomorphism X Y) (λX Y, pmap_of_group_homomorphism)

    definition PMS_CommGroup_Group [constructor]
      : PointedMapStructure PS_CommGroup PS_CommGroup :=
    PointedMapStructure.mk (λX Y, group_homomorphism X Y) (λX Y, pmap_of_group_homomorphism)
  end

  structure general_long_exact_sequence
    (Z : ℤ → PointedStructure) (F : Πn, PointedMapStructure (Z (succ n)) (Z n)) :=
    (A : Πn, elt_of (Z n))
    (f : Πn, fun_of (F n) (A (succ n)) (A n))
    (p : Πn x, f n (f (succ n) x) = pt)
    (q : Πn y, f n y = pt → ∃x, f (succ n) x = y)

  structure long_exact_sequence := -- a long exact sequence
    (A : ℤ → Type*)                -- consists of a sequence of pointed types
    (f : Πn, A (succ n) →* A n)       -- together with basepoint-preserving maps
    (p : Πn x, f n (f (succ n) x) = pt) -- such that the kernel of f n is in the image of f (succ n)
    (q : Πn y, f n y = pt → ∃x, f (succ n) x = y) -- and vice versa


  definition foo (X : long_exact_sequence)
    : general_long_exact_sequence (λn, PS_Pointed) (λn, !PMS_general) :=
  general_long_exact_sequence.mk
    (long_exact_sequence.A X)
    (long_exact_sequence.f X)
    (long_exact_sequence.p X)
    (long_exact_sequence.q X)


  definition usual_long_exact_sequence : Type :=
  general_long_exact_sequence
    (int.rec (λ(n : ℕ),
      match n with
      | 0 := PS_Pointed
      | 1 := PS_Pointed
      | 2 := PS_Pointed
      | 3 := PS_Group
      | 4 := PS_Group
      | 5 := PS_Group
      | k + 6 := PS_CommGroup end) (λn, PS_Unit))
    (int.rec (λ(n : ℕ),
      match n with
      | 0 := !PMS_general
      | 1 := !PMS_general
      | 2 := !PMS_general
      | 3 := PMS_Group
      | 4 := PMS_Group
      | 5 := begin esimp [int.succ], end
      | k + 6 := begin end end) (λn, !PMS_general))


end LES
