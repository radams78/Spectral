/-
Copyright (c) 2015 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn, Egbert Rijke

Constructions with groups
-/

import .quotient_group .free_commutative_group

open eq algebra is_trunc set_quotient relation sigma prod sum list trunc function equiv sigma.ops

namespace group

  variables {G G' : Group} (H : subgroup_rel G) (N : normal_subgroup_rel G) {g g' h h' k : G}
            {A B : AbGroup}

  variables (X : Set) {l l' : list (X ⊎ X)}

  section

    parameters {I : Set} (Y : I → AbGroup)
    variables {A' : AbGroup}

    definition dirsum_carrier : AbGroup := free_ab_group (trunctype.mk (Σi, Y i) _)
    local abbreviation ι [constructor] := @free_ab_group_inclusion
    inductive dirsum_rel : dirsum_carrier → Type :=
    | rmk : Πi y₁ y₂, dirsum_rel (ι ⟨i, y₁⟩ * ι ⟨i, y₂⟩ * (ι ⟨i, y₁ * y₂⟩)⁻¹)

    definition dirsum : AbGroup := quotient_ab_group_gen dirsum_carrier (λg, ∥dirsum_rel g∥)

    -- definition dirsum_carrier_incl [constructor] (i : I) : Y i →g dirsum_carrier :=

    definition dirsum_incl [constructor] (i : I) : Y i →g dirsum :=
    homomorphism.mk (λy, class_of (ι ⟨i, y⟩))
      begin intro g h, symmetry, apply gqg_eq_of_rel, apply tr, apply dirsum_rel.rmk end

    definition dirsum_elim_resp_quotient (f : Πi, Y i →g A') (g : dirsum_carrier)
      (r : ∥dirsum_rel g∥) : free_ab_group_elim (λv, f v.1 v.2) g = 1 :=
    begin
      induction r with r, induction r,
      rewrite [to_respect_mul, to_respect_inv], apply mul_inv_eq_of_eq_mul,
      rewrite [one_mul, to_respect_mul, ▸*, ↑foldl, +one_mul, to_respect_mul]
    end

    definition dirsum_elim [constructor] (f : Πi, Y i →g A') : dirsum →g A' :=
    gqg_elim _ (free_ab_group_elim (λv, f v.1 v.2)) (dirsum_elim_resp_quotient f)

    definition dirsum_elim_compute (f : Πi, Y i →g A') (i : I) :
      dirsum_elim f ∘g dirsum_incl i ~ f i :=
    begin
      intro g, apply one_mul
    end

    definition dirsum_elim_unique (f : Πi, Y i →g A') (k : dirsum →g A')
      (H : Πi, k ∘g dirsum_incl i ~ f i) : k ~ dirsum_elim f :=
    begin
      apply gqg_elim_unique,
      apply free_ab_group_elim_unique,
      intro x, induction x with i y, exact H i y
    end


  end

end group
