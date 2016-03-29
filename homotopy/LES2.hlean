/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

We define the fiber sequence of a pointed map f : X →* Y. We follow the proof in section 8.4 of
the book. First we define a sequence fiber_sequence as in Definition 8.4.3.
It has types X(n) : Type*
X(0)   := Y,
X(1)   := X,
X(n+1) := pfiber (f(n))
with functions f(n) : X(n+1) →* X(n)
f(0)   := f
f(n+1) := ppoint f(n)
We prove that this is an exact sequence.
Then we prove Lemma 8.4.3, by showing that X(n+3) ≃* Ω(X(n)) and that this equivalence sends
the map f(n+3) to -Ω(f(n)), i.e. the composition of Ω(f(n)) with path inversion.
This is the hardest part of this formalization, because we need to show that they are the same
as pointed maps (we define a pointed homotopy between them).

Using this equivalence we get a boundary_map : Ω(Y) → pfiber f and we can define a new
fiber sequence X'(n) : Type*
X'(0)   := Y,
X'(1)   := X,
X'(2)   := pfiber f
X'(n+3) := Ω(X'(n))
and maps f'(n) : X'(n+1) →* X'(n)
f'(0) := f
f'(1) := ppoint f
f'(2) := boundary_map f
f'(3) := -Ω(f)
f'(4) := -Ω(ppoint f)
f'(5) := -Ω(boundary_map f)
f'(n+6) := Ω²(f'(n))

We can show that these sequences are equivalent, hence the sequence (X',f') is an exact
sequence. Now we get the fiber sequence by taking the set-truncation of this sequence.
-/

import .chain_complex algebra.homotopy_group

open eq pointed sigma fiber equiv is_equiv sigma.ops is_trunc nat trunc algebra function

/--------------
    PART 1
 --------------/

namespace chain_complex

  definition fiber_sequence_helper [constructor] (v : Σ(X Y : Type*), X →* Y)
    : Σ(Z X : Type*), Z →* X :=
  ⟨pfiber v.2.2, v.1, ppoint v.2.2⟩

  definition fiber_sequence_helpern (v : Σ(X Y : Type*), X →* Y) (n : ℕ)
    : Σ(Z X : Type*), Z →* X :=
  iterate fiber_sequence_helper n v

  section
  universe variable u
  parameters {X Y : pType.{u}} (f : X →* Y)
  variable (n : ℕ)
  include f

  definition fiber_sequence_carrier : Type* :=
  (fiber_sequence_helpern ⟨X, Y, f⟩ n).2.1

  definition fiber_sequence_fun
    : fiber_sequence_carrier (n + 1) →* fiber_sequence_carrier n :=
  (fiber_sequence_helpern ⟨X, Y, f⟩ n).2.2

  /- Definition 8.4.3 -/
  definition fiber_sequence : type_chain_complex.{0 u} +ℕ :=
  begin
    fconstructor,
    { exact fiber_sequence_carrier},
    { exact fiber_sequence_fun},
    { intro n x, cases n with n,
      { exact point_eq x},
      { exact point_eq x}}
  end

  definition is_exact_fiber_sequence : is_exact_t fiber_sequence :=
  λn x p, fiber.mk (fiber.mk x p) rfl

  /- (generalization of) Lemma 8.4.4(i)(ii) -/
  definition fiber_sequence_carrier_equiv
    : fiber_sequence_carrier (n+3) ≃ Ω(fiber_sequence_carrier n) :=
  calc
    fiber_sequence_carrier (n+3) ≃ fiber (fiber_sequence_fun (n+1)) pt : erfl
    ... ≃ Σ(x : fiber_sequence_carrier _), fiber_sequence_fun (n+1) x = pt
      : fiber.sigma_char
    ... ≃ Σ(x : fiber (fiber_sequence_fun n) pt), fiber_sequence_fun _ x = pt
      : erfl
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier _), fiber_sequence_fun _ x = pt),
            fiber_sequence_fun _ (fiber.mk v.1 v.2) = pt
      : by exact sigma_equiv_sigma !fiber.sigma_char (λa, erfl)
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier _), fiber_sequence_fun _ x = pt),
            v.1 = pt
      : erfl
    ... ≃ Σ(v : Σ(x : fiber_sequence_carrier _), x = pt),
            fiber_sequence_fun _ v.1 = pt
      : sigma_assoc_comm_equiv
    ... ≃ fiber_sequence_fun _ !center.1 = pt
      : @(sigma_equiv_of_is_contr_left _) !is_contr_sigma_eq'
    ... ≃ fiber_sequence_fun _ pt = pt
      : erfl
    ... ≃ pt = pt
      : by exact !equiv_eq_closed_left !respect_pt
    ... ≃ Ω(fiber_sequence_carrier n) : erfl

  /- computation rule -/
  definition fiber_sequence_carrier_equiv_eq
    (x : fiber_sequence_carrier (n+1)) (p : fiber_sequence_fun n x = pt)
    (q : fiber_sequence_fun (n+1) (fiber.mk x p) = pt)
    : fiber_sequence_carrier_equiv n (fiber.mk (fiber.mk x p) q)
      = !respect_pt⁻¹ ⬝ ap (fiber_sequence_fun n) q⁻¹ ⬝ p :=
  begin
    refine _ ⬝ !con.assoc⁻¹,
    apply whisker_left,
    refine transport_eq_Fl _ _ ⬝ _,
    apply whisker_right,
    refine inverse2 !ap_inv ⬝ !inv_inv ⬝ _,
    refine ap_compose (fiber_sequence_fun n) pr₁ _ ⬝
           ap02 (fiber_sequence_fun n) !ap_pr1_center_eq_sigma_eq',
  end

  definition fiber_sequence_carrier_equiv_inv_eq
    (p : Ω(fiber_sequence_carrier n)) : (fiber_sequence_carrier_equiv n)⁻¹ᵉ p =
      fiber.mk (fiber.mk pt (respect_pt (fiber_sequence_fun n) ⬝ p)) idp :=
  begin
    apply inv_eq_of_eq,
    refine _ ⬝ !fiber_sequence_carrier_equiv_eq⁻¹, esimp,
    exact !inv_con_cancel_left⁻¹
  end

  definition fiber_sequence_carrier_pequiv
    : fiber_sequence_carrier (n+3) ≃* Ω(fiber_sequence_carrier n) :=
  pequiv_of_equiv (fiber_sequence_carrier_equiv n)
    begin
      esimp,
      apply con.left_inv
    end

  definition fiber_sequence_carrier_pequiv_eq
    (x : fiber_sequence_carrier (n+1)) (p : fiber_sequence_fun n x = pt)
    (q : fiber_sequence_fun (n+1) (fiber.mk x p) = pt)
    : fiber_sequence_carrier_pequiv n (fiber.mk (fiber.mk x p) q)
      = !respect_pt⁻¹ ⬝ ap (fiber_sequence_fun n) q⁻¹ ⬝ p :=
  fiber_sequence_carrier_equiv_eq n x p q

  definition fiber_sequence_carrier_pequiv_inv_eq
    (p : Ω(fiber_sequence_carrier n)) : (fiber_sequence_carrier_pequiv n)⁻¹ᵉ* p =
      fiber.mk (fiber.mk pt (respect_pt (fiber_sequence_fun n) ⬝ p)) idp :=
  by rexact fiber_sequence_carrier_equiv_inv_eq n p

  /- Lemma 8.4.4(iii) -/
  definition fiber_sequence_fun_eq_helper
    (p : Ω(fiber_sequence_carrier (n + 1))) :
    fiber_sequence_carrier_pequiv n
      (fiber_sequence_fun (n + 3)
        ((fiber_sequence_carrier_pequiv (n + 1))⁻¹ᵉ* p)) =
          ap1 (fiber_sequence_fun n) p⁻¹ :=
  begin
    refine ap (λx, fiber_sequence_carrier_pequiv n (fiber_sequence_fun (n + 3) x))
              (fiber_sequence_carrier_pequiv_inv_eq (n+1) p) ⬝ _,
    /- the following three lines are rewriting some reflexivities: -/
    -- replace (n + 3) with (n + 2 + 1),
    -- refine ap (fiber_sequence_carrier_pequiv n)
    --           (fiber_sequence_fun_eq1 (n+2) _ idp) ⬝ _,
    refine fiber_sequence_carrier_pequiv_eq n pt (respect_pt (fiber_sequence_fun n)) _ ⬝ _,
    esimp,
    apply whisker_right,
    apply whisker_left,
    apply ap02, apply inverse2, apply idp_con,
  end

  theorem fiber_sequence_carrier_pequiv_eq_point_eq_idp :
    fiber_sequence_carrier_pequiv_eq n
      (Point (fiber_sequence_carrier (n+1)))
      (respect_pt (fiber_sequence_fun n))
      (respect_pt (fiber_sequence_fun (n + 1))) = idp :=
  begin
    apply con_inv_eq_idp,
    refine ap (λx, whisker_left _ (_ ⬝ x)) _ ⬝ _,
    { reflexivity},
    { reflexivity},
    esimp,
    refine ap (whisker_left _)
              (transport_eq_Fl_idp_left (fiber_sequence_fun n)
                                        (respect_pt (fiber_sequence_fun n))) ⬝ _,
    apply whisker_left_idp_con_eq_assoc
  end

  theorem fiber_sequence_fun_phomotopy_helper :
    (fiber_sequence_carrier_pequiv n ∘*
      fiber_sequence_fun (n + 3)) ∘*
        (fiber_sequence_carrier_pequiv (n + 1))⁻¹ᵉ* ~*
          ap1 (fiber_sequence_fun n) ∘* pinverse :=
  begin
    fapply phomotopy.mk,
    { exact fiber_sequence_fun_eq_helper n},
    { esimp, rewrite [idp_con], refine _ ⬝ whisker_left _ !idp_con⁻¹,
      apply whisker_right,
      apply whisker_left,
      exact fiber_sequence_carrier_pequiv_eq_point_eq_idp n}
  end

  theorem fiber_sequence_fun_eq : Π(x : fiber_sequence_carrier (n + 4)),
    fiber_sequence_carrier_pequiv n (fiber_sequence_fun (n + 3) x) =
      ap1 (fiber_sequence_fun n) (fiber_sequence_carrier_pequiv (n + 1) x)⁻¹ :=
  begin
    apply homotopy_of_inv_homotopy_pre (fiber_sequence_carrier_pequiv (n + 1)),
    apply fiber_sequence_fun_eq_helper n
  end

  theorem fiber_sequence_fun_phomotopy :
    fiber_sequence_carrier_pequiv n ∘*
      fiber_sequence_fun (n + 3) ~*
          (ap1 (fiber_sequence_fun n) ∘* pinverse) ∘* fiber_sequence_carrier_pequiv (n + 1) :=
  begin
    apply phomotopy_of_pinv_right_phomotopy,
    apply fiber_sequence_fun_phomotopy_helper
  end

  definition boundary_map : Ω Y →* pfiber f :=
  fiber_sequence_fun 2 ∘* (fiber_sequence_carrier_pequiv 0)⁻¹ᵉ*

/--------------
    PART 2
 --------------/

  /- Now we are ready to define the long exact sequence of homotopy groups.
     First we define its carrier -/
  definition loop_spaces : ℕ → Type*
  | 0     := Y
  | 1     := X
  | 2     := pfiber f
  | (k+3) := Ω (loop_spaces k)

  definition loop_spaces_add3 [unfold_full] :
    loop_spaces (n+3) = Ω (loop_spaces n) :=
  by reflexivity
exit
  -- definition loop_spaces_mul3
  --   : Πn, loop_spaces (3 * n) = Ω[n] Y :> Type*
  -- | 0     := proof rfl qed
  -- | (k+1) := proof ap (λX, Ω X) (loop_spaces_mul3 k) qed

  -- definition loop_spaces_mul3add1
  --   : Πn, loop_spaces (3 * n + 1) = Ω[n] X :> Type*
  -- | 0     := by reflexivity
  -- | (k+1) := proof ap (λX, Ω X) (loop_spaces_mul3add1 k) qed

  -- definition loop_spaces_mul3add2
  --   : Πn, loop_spaces (3 * n + 2) = Ω[n] (pfiber f) :> Type*
  -- | 0     := by reflexivity
  -- | (k+1) := proof ap (λX, Ω X) (loop_spaces_mul3add2 k) qed

  /- The maps between the homotopy groups -/
  definition loop_spaces_fun
    : Π(n : ℕ), loop_spaces (n+1) →* loop_spaces n
  | 0     := proof f qed
  | 1     := proof ppoint f qed
  | 2     := proof boundary_map f qed
  | (k+3) := proof ap1 (loop_spaces_fun k) qed

  definition loop_spaces_fun_add3 [unfold_full] :
    loop_spaces_fun (n + 3) = ap1 (loop_spaces_fun n) :=
  proof idp qed

  definition fiber_sequence_pequiv_loop_spaces :
    Πn, fiber_sequence_carrier n ≃* loop_spaces n
  | 0     := by reflexivity
  | 1     := by reflexivity
  | 2     := by reflexivity
  | (k+3) :=
    begin
      refine fiber_sequence_carrier_pequiv k ⬝e* _,
      apply loop_pequiv_loop,
      exact fiber_sequence_pequiv_loop_spaces k
    end

  definition fiber_sequence_pequiv_loop_spaces_add3
    : fiber_sequence_pequiv_loop_spaces (n + 3) =
      ap1 (fiber_sequence_pequiv_loop_spaces n) ∘* fiber_sequence_carrier_pequiv n :=
  by reflexivity

  definition fiber_sequence_pequiv_loop_spaces_3_phomotopy
    : fiber_sequence_pequiv_loop_spaces 3 ~* proof fiber_sequence_carrier_pequiv nat.zero qed :=
  begin
    refine pwhisker_right _ ap1_id ⬝* _,
    apply pid_comp
  end

  theorem fiber_sequence_phomotopy_loop_spaces' :
    Π(n : ℕ),
    fiber_sequence_pequiv_loop_spaces n ∘* fiber_sequence_fun n ~*
      loop_spaces_fun n ∘* fiber_sequence_pequiv_loop_spaces (n + 1)
  | 0     := by reflexivity
  | 1     := by reflexivity
  | 2     :=
    begin
      refine !pid_comp ⬝* _,
      replace loop_spaces_fun' 2 with boundary_map f,
      refine _ ⬝* pwhisker_left _ (fiber_sequence_pequiv_loop_spaces_3_phomotopy f)⁻¹*,
      apply phomotopy_of_pinv_right_phomotopy,
      reflexivity
    end
  | (k+3) :=
    begin
      replace (k + 3 + 1) with (k + 1 + 3),
      rewrite [fiber_sequence_pequiv_loop_spaces_add3 k,
               fiber_sequence_pequiv_loop_spaces_add3 (k+1)],
      refine !passoc ⬝* _,
      refine pwhisker_left _ (fiber_sequence_fun_phomotopy k) ⬝* _,
      refine !passoc⁻¹* ⬝* _ ⬝* !passoc,
      apply pwhisker_right,
      rewrite [loop_spaces_fun'_add3],
      refine _ ⬝* !passoc⁻¹*,
      refine _ ⬝* pwhisker_left _ !ap1_compose_pinverse,
      refine !passoc⁻¹* ⬝* _ ⬝* !passoc,
      apply pwhisker_right,
      refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose,
      apply ap1_phomotopy,
      exact fiber_sequence_phomotopy_loop_spaces' k
    end

  theorem fiber_sequence_phomotopy_loop_spaces (n : ℕ)
    (x : fiber_sequence_carrier (n + 1)) :
    fiber_sequence_pequiv_loop_spaces n (fiber_sequence_fun n x) =
      loop_spaces_fun n (fiber_sequence_pequiv_loop_spaces (n + 1) x) :=
  begin
    refine fiber_sequence_phomotopy_loop_spaces' n x ⬝ _,
    exact (loop_spaces_fun_eq n _)⁻¹
  end

  definition type_LES_of_loop_spaces [constructor] : type_chain_complex +ℕ :=
  transfer_type_chain_complex
    (fiber_sequence f)
    (loop_spaces_fun)
    (fiber_sequence_pequiv_loop_spaces)
    (fiber_sequence_phomotopy_loop_spaces)

  definition is_exact_type_LES_of_loop_spaces : is_exact_t (type_LES_of_loop_spaces) :=
  begin
    intro n,
    apply is_exact_at_t_transfer,
    apply is_exact_fiber_sequence
  end

  /- the long exact sequence of homotopy groups -/
  definition LES_of_loop_spaces [constructor] : chain_complex +ℕ :=
  trunc_chain_complex
    (transfer_type_chain_complex
      (fiber_sequence f)
      (loop_spaces_fun)
      (fiber_sequence_pequiv_loop_spaces)
      (fiber_sequence_phomotopy_loop_spaces))

  /- the fiber sequence is exact -/
  definition is_exact_LES_of_loop_spaces : is_exact (LES_of_loop_spaces) :=
  begin
    intro n,
    apply is_exact_at_trunc,
    apply is_exact_type_LES_of_loop_spaces
  end
exit
  /- for a numeral, the carrier of the fiber sequence is definitionally what we want
     (as pointed sets) -/
  example : LES_of_loop_spaces 6 = π*[2] Y          :> Set* := by reflexivity
  example : LES_of_loop_spaces 7 = π*[2] X          :> Set* := by reflexivity
  example : LES_of_loop_spaces 8 = π*[2] (pfiber f) :> Set* := by reflexivity

  /- for a numeral, the functions of the fiber sequence is definitionally what we want
     (as pointed function). All these functions have at most one "pinverse" in them, and these
     inverses are inside the π→*[2*k].
  -/
  example : cc_to_fn (LES_of_loop_spaces)  6 = π→*[2] f
    :> (_ →* _) := by reflexivity
  example : cc_to_fn (LES_of_loop_spaces)  7 = π→*[2] (ppoint f)
    :> (_ →* _) := by reflexivity
  example : cc_to_fn (LES_of_loop_spaces)  8 = π→*[2] (boundary_map f)
    :> (_ →* _) := by reflexivity
  example : cc_to_fn (LES_of_loop_spaces)  9 = π→*[2] (ap1 f ∘* pinverse)
    :> (_ →* _) := by reflexivity
  example : cc_to_fn (LES_of_loop_spaces) 10 = π→*[2] (ap1 (ppoint f) ∘* pinverse)
    :> (_ →* _) := by reflexivity
  example : cc_to_fn (LES_of_loop_spaces) 11 = π→*[2] (ap1 (boundary_map f) ∘* pinverse)
    :> (_ →* _) := by reflexivity
  example : cc_to_fn (LES_of_loop_spaces) 12 = π→*[4] f
    :> (_ →* _) := by reflexivity

  /- the carrier of the fiber sequence is what we want for natural numbers of the form
     3n, 3n+1 and 3n+2 -/
  definition LES_of_loop_spaces_mul3 (n : ℕ)
    : LES_of_loop_spaces (3 * n) = π*[n] Y :> Set* :=
  begin
   apply ptrunctype_eq_of_pType_eq,
   exact ap (ptrunc 0) (loop_spaces_mul3 n)
  end

  definition LES_of_loop_spaces_mul3add1 (n : ℕ)
    : LES_of_loop_spaces (3 * n + 1) = π*[n] X :> Set* :=
  begin
   apply ptrunctype_eq_of_pType_eq,
   exact ap (ptrunc 0) (loop_spaces_mul3add1 n)
  end

  definition LES_of_loop_spaces_mul3add2 (n : ℕ)
    : LES_of_loop_spaces (3 * n + 2) = π*[n] (pfiber f) :> Set* :=
  begin
   apply ptrunctype_eq_of_pType_eq,
   exact ap (ptrunc 0) (loop_spaces_mul3add2 n)
  end

  definition LES_of_loop_spaces_mul3' (n : ℕ)
    : LES_of_loop_spaces (3 * n) = π*[n] Y :> Type :=
  begin
   exact ap (ptrunc 0) (loop_spaces_mul3 n)
  end

  definition LES_of_loop_spaces_mul3add1' (n : ℕ)
    : LES_of_loop_spaces (3 * n + 1) = π*[n] X :> Type :=
  begin
   exact ap (ptrunc 0) (loop_spaces_mul3add1 n)
  end

  definition LES_of_loop_spaces_mul3add2' (n : ℕ)
    : LES_of_loop_spaces (3 * n + 2) = π*[n] (pfiber f) :> Type :=
  begin
   exact ap (ptrunc 0) (loop_spaces_mul3add2 n)
  end

  definition group_LES_of_loop_spaces (n : ℕ) : group (LES_of_loop_spaces (n + 3)) :=
  group_homotopy_group 0 (loop_spaces n)

  definition comm_group_LES_of_loop_spaces (n : ℕ) : comm_group (LES_of_loop_spaces (n + 6)) :=
  comm_group_homotopy_group 0 (loop_spaces n)

end chain_complex

open group prod succ_str fin

/--------------
    PART 3
 --------------/

namespace chain_complex

  --TODO: move
  definition tr_mul_tr {A : Type*} (n : ℕ) (p q : Ω[n + 1] A) :
    tr p *[πg[n+1] A] tr q = tr (p ⬝ q) :=
  by reflexivity

  definition is_homomorphism_cast_loop_space_succ_eq_in {A : Type*} (n : ℕ) :
    is_homomorphism
      (cast (ap (trunc 0 ∘ pointed.carrier) (loop_space_succ_eq_in A (succ n)))
        : πg[n+1+1] A → πg[n+1] Ω A) :=
  begin
    intro g h, induction g with g, induction h with h,
    xrewrite [tr_mul_tr, - + fn_cast_eq_cast_fn _ (λn, tr), tr_mul_tr, ↑cast, -tr_compose,
              loop_space_succ_eq_in_concat, - + tr_compose],
  end

  definition is_homomorphism_inverse (A : Type*) (n : ℕ)
    : is_homomorphism (λp, p⁻¹ : πag[n+2] A → πag[n+2] A) :=
  begin
    intro g h, rewrite mul.comm,
    induction g with g, induction h with h,
    exact ap tr !con_inv
  end

  section
  universe variable u
  parameters {X Y : pType.{u}} (f : X →* Y)

  definition loop_spaces2 [reducible] : +6ℕ → Type*
  | (n, fin.mk 0 H) := Ω[2*n] Y
  | (n, fin.mk 1 H) := Ω[2*n] X
  | (n, fin.mk 2 H) := Ω[2*n] (pfiber f)
  | (n, fin.mk 3 H) := Ω[2*n + 1] Y
  | (n, fin.mk 4 H) := Ω[2*n + 1] X
  | (n, fin.mk k H) := Ω[2*n + 1] (pfiber f)

  definition loop_spaces2_add1 (n : ℕ) : Π(x : fin (succ 5)),
    loop_spaces2 (n+1, x) = Ω Ω(loop_spaces2 (n, x))
  | (fin.mk 0 H) := by reflexivity
  | (fin.mk 1 H) := by reflexivity
  | (fin.mk 2 H) := by reflexivity
  | (fin.mk 3 H) := by reflexivity
  | (fin.mk 4 H) := by reflexivity
  | (fin.mk 5 H) := by reflexivity
  | (fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition loop_spaces_fun2 : Π(n : +6ℕ), loop_spaces2 (S n) →* loop_spaces2 n
  | (n, fin.mk 0 H) := proof Ω→[2*n] f qed
  | (n, fin.mk 1 H) := proof Ω→[2*n] (ppoint f) qed
  | (n, fin.mk 2 H) :=
    proof Ω→[2*n] (boundary_map f) ∘* pcast (loop_space_succ_eq_in Y (2*n)) qed
  | (n, fin.mk 3 H) := proof Ω→[2*n + 1] f ∘* pinverse qed
  | (n, fin.mk 4 H) := proof Ω→[2*n + 1] (ppoint f) ∘* pinverse qed
  | (n, fin.mk 5 H) :=
    proof (Ω→[2*n + 1] (boundary_map f) ∘* pinverse) ∘* pcast (loop_space_succ_eq_in Y (2*n+1)) qed
  | (n, fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition loop_spaces_fun2_add1_0 (n : ℕ) (H : 0 < succ 5)
    : loop_spaces_fun2 (n+1, fin.mk 0 H) ~*
      cast proof idp qed ap1 (ap1 (loop_spaces_fun2 (n, fin.mk 0 H))) :=
  by reflexivity

  definition loop_spaces_fun2_add1_1 (n : ℕ) (H : 1 < succ 5)
    : loop_spaces_fun2 (n+1, fin.mk 1 H) ~*
      cast proof idp qed ap1 (ap1 (loop_spaces_fun2 (n, fin.mk 1 H))) :=
  by reflexivity

  definition loop_spaces_fun2_add1_2 (n : ℕ) (H : 2 < succ 5)
    : loop_spaces_fun2 (n+1, fin.mk 2 H) ~*
      cast proof idp qed ap1 (ap1 (loop_spaces_fun2 (n, fin.mk 2 H))) :=
  begin
    esimp, refine _ ⬝* (ap1_phomotopy !ap1_compose)⁻¹*, refine _ ⬝* !ap1_compose⁻¹*,
    apply pwhisker_left,
    refine !pcast_ap_loop_space ⬝* ap1_phomotopy !pcast_ap_loop_space,
  end

  definition loop_spaces_fun2_add1_3 (n : ℕ) (H : 3 < succ 5)
    : loop_spaces_fun2 (n+1, fin.mk 3 H) ~*
      cast proof idp qed ap1 (ap1 (loop_spaces_fun2 (n, fin.mk 3 H))) :=
  begin
    esimp, refine _ ⬝* (ap1_phomotopy !ap1_compose)⁻¹*, refine _ ⬝* !ap1_compose⁻¹*,
    apply pwhisker_left,
    exact ap1_pinverse⁻¹* ⬝* ap1_phomotopy !ap1_pinverse⁻¹*
  end

  definition loop_spaces_fun2_add1_4 (n : ℕ) (H : 4 < succ 5)
    : loop_spaces_fun2 (n+1, fin.mk 4 H) ~*
      cast proof idp qed ap1 (ap1 (loop_spaces_fun2 (n, fin.mk 4 H))) :=
  begin
    esimp, refine _ ⬝* (ap1_phomotopy !ap1_compose)⁻¹*, refine _ ⬝* !ap1_compose⁻¹*,
    apply pwhisker_left,
    exact ap1_pinverse⁻¹* ⬝* ap1_phomotopy !ap1_pinverse⁻¹*
  end

  definition loop_spaces_fun2_add1_5 (n : ℕ) (H : 5 < succ 5)
    : loop_spaces_fun2 (n+1, fin.mk 5 H) ~*
      cast proof idp qed ap1 (ap1 (loop_spaces_fun2 (n, fin.mk 5 H))) :=
  begin
    esimp, refine _ ⬝* (ap1_phomotopy !ap1_compose)⁻¹*, refine _ ⬝* !ap1_compose⁻¹*,
    apply pconcat2,
    { esimp, refine _ ⬝* (ap1_phomotopy !ap1_compose)⁻¹*, refine _ ⬝* !ap1_compose⁻¹*,
      apply pwhisker_left,
      exact ap1_pinverse⁻¹* ⬝* ap1_phomotopy !ap1_pinverse⁻¹*},
    { refine !pcast_ap_loop_space ⬝* ap1_phomotopy !pcast_ap_loop_space}
  end

  definition nat_of_str [unfold 2] [reducible] {n : ℕ} : ℕ × fin (succ n) → ℕ :=
  λx, succ n * pr1 x + val (pr2 x)

  definition str_of_nat {n : ℕ} : ℕ → ℕ × fin (succ n) :=
  λm, (m / (succ n), mk_mod n m)

  definition nat_of_str_6S [unfold 2] [reducible]
    : Π(x : stratified +ℕ 5), nat_of_str x + 1 = nat_of_str (@S (stratified +ℕ 5) x)
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) := by reflexivity
  | (n, fin.mk 3 H) := by reflexivity
  | (n, fin.mk 4 H) := by reflexivity
  | (n, fin.mk 5 H) := by reflexivity
  | (n, fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition fin_prod_nat_equiv_nat [constructor] (n : ℕ) : ℕ × fin (succ n) ≃ ℕ :=
  equiv.MK nat_of_str str_of_nat
    abstract begin
      intro m, unfold [nat_of_str, str_of_nat, mk_mod],
      refine _ ⬝ (eq_div_mul_add_mod m (succ n))⁻¹,
      rewrite [mul.comm]
    end end
    abstract begin
      intro x, cases x with m k,
      cases k with k H,
      apply prod_eq: esimp [str_of_nat],
      { rewrite [add.comm, add_mul_div_self_left _ _ (!zero_lt_succ),
                 div_eq_zero_of_lt H, zero_add]},
      { apply eq_of_veq, esimp [mk_mod],
        rewrite [add.comm, add_mul_mod_self_left, mod_eq_of_lt H]}
    end end

  /-
    note: in the following theorem the (n+1) case is 6 times the same,
    so maybe this can be simplified
  -/
  definition loop_spaces2_pequiv' : Π(n : ℕ) (x : fin (nat.succ 5)),
    loop_spaces (nat_of_str (n, x)) ≃* loop_spaces2 (n, x)
  |  0    (fin.mk 0 H)     := by reflexivity
  |  0    (fin.mk 1 H)     := by reflexivity
  |  0    (fin.mk 2 H)     := by reflexivity
  |  0    (fin.mk 3 H)     := by reflexivity
  |  0    (fin.mk 4 H)     := by reflexivity
  |  0    (fin.mk 5 H)     := by reflexivity
  | (n+1) (fin.mk 0 H)     :=
    begin
      -- uncomment the next two lines to have prettier subgoals
      -- esimp, replace (succ 5 * (n + 1) + 0) with (6*n+3+3),
      -- rewrite [+loop_spaces_add3, loop_spaces2_add1],
      apply loop_pequiv_loop, apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 0 H)
    end
  | (n+1) (fin.mk 1 H)     :=
    begin
      apply loop_pequiv_loop, apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 1 H)
    end
  | (n+1) (fin.mk 2 H)     :=
    begin
      apply loop_pequiv_loop, apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 2 H)
    end
  | (n+1) (fin.mk 3 H)     :=
    begin
      apply loop_pequiv_loop, apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 3 H)
    end
  | (n+1) (fin.mk 4 H)     :=
    begin
      apply loop_pequiv_loop, apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 4 H)
    end
  | (n+1) (fin.mk 5 H)     :=
    begin
      apply loop_pequiv_loop, apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 5 H)
    end
  | n     (fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition loop_spaces2_pequiv : Π(x : +6ℕ),
    loop_spaces (nat_of_str x) ≃* loop_spaces2 x
  | (n, x) := loop_spaces2_pequiv' n x

  local attribute loop_pequiv_loop [reducible]
  /- all cases where n>0 are basically the same -/
  definition loop_spaces_fun2_phomotopy (x : +6ℕ) :
    loop_spaces2_pequiv x ∘* loop_spaces_fun (nat_of_str x) ~*
      (loop_spaces_fun2 x ∘* loop_spaces2_pequiv (S x))
    ∘* pcast (ap (loop_spaces) (nat_of_str_6S x)) :=
  begin
    cases x with n x, cases x with k H,
    cases k with k, rotate 1, cases k with k, rotate 1, cases k with k, rotate 1,
    cases k with k, rotate 1, cases k with k, rotate 1, cases k with k, rotate 2,
    { /-k=0-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹* ⬝* !comp_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ (!loop_spaces_fun2_add1_0)⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=1-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹* ⬝* !comp_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ (!loop_spaces_fun2_add1_1)⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=2-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹* ⬝* !comp_pid⁻¹*,
        refine _ ⬝* !comp_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ (!loop_spaces_fun2_add1_2)⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=3-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹* ⬝* !comp_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ (!loop_spaces_fun2_add1_3)⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=4-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹* ⬝* !comp_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ (!loop_spaces_fun2_add1_4)⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=5-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹*,
        refine !comp_pid⁻¹* ⬝* pconcat2 _ _,
        { exact (comp_pid (ap1 (boundary_map f) ∘* pinverse))⁻¹*},
        { refine cast (ap (λx, _ ~* loop_pequiv_loop x) !loop_pequiv_loop_rfl)⁻¹ _,
          refine cast (ap (λx, _ ~* x) !loop_pequiv_loop_rfl)⁻¹ _, reflexivity}},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ (!loop_spaces_fun2_add1_5)⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=k'+6-/ exfalso, apply lt_le_antisymm H, apply le_add_left}
  end

  definition type_LES_of_loop_spaces2 [constructor] : type_chain_complex +6ℕ :=
  transfer_type_chain_complex2
    (type_LES_of_loop_spaces)
    !fin_prod_nat_equiv_nat
    nat_of_str_6S
    @loop_spaces_fun2
    @loop_spaces2_pequiv
    begin
      intro m x,
      refine loop_spaces_fun2_phomotopy m x ⬝ _,
      apply ap (loop_spaces_fun2 m), apply ap (loop_spaces2_pequiv (S m)),
      esimp, exact ap010 cast !ap_compose⁻¹ x
    end

  definition is_exact_type_LES_of_loop_spaces2 : is_exact_t (type_LES_of_loop_spaces2) :=
  begin
    intro n,
    apply is_exact_at_transfer2,
    apply is_exact_type_LES_of_loop_spaces
  end

  definition LES_of_loop_spaces2 [constructor] : chain_complex +6ℕ :=
  trunc_chain_complex type_LES_of_loop_spaces2

/--------------
    PART 4
 --------------/

  definition loop_spaces3 [reducible] : +6ℕ → Set*
  | (n, fin.mk 0 H) := π*[2*n] Y
  | (n, fin.mk 1 H) := π*[2*n] X
  | (n, fin.mk 2 H) := π*[2*n] (pfiber f)
  | (n, fin.mk 3 H) := π*[2*n + 1] Y
  | (n, fin.mk 4 H) := π*[2*n + 1] X
  | (n, fin.mk k H) := π*[2*n + 1] (pfiber f)

  definition loop_spaces3eq2 [reducible]
    : Π(n : +6ℕ), ptrunc 0 (loop_spaces2 n) ≃* loop_spaces3 n
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) := by reflexivity
  | (n, fin.mk 3 H) := by reflexivity
  | (n, fin.mk 4 H) := by reflexivity
  | (n, fin.mk 5 H) := by reflexivity
  | (n, fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition loop_spaces_fun3 : Π(n : +6ℕ), loop_spaces3 (S n) →* loop_spaces3 n
  | (n, fin.mk 0 H) := proof π→*[2*n] f qed
  | (n, fin.mk 1 H) := proof π→*[2*n] (ppoint f) qed
  | (n, fin.mk 2 H) :=
    proof π→*[2*n] (boundary_map f) ∘* pcast (ap (ptrunc 0) (loop_space_succ_eq_in Y (2*n))) qed
  | (n, fin.mk 3 H) := proof π→*[2*n + 1] f ∘* tinverse qed
  | (n, fin.mk 4 H) := proof π→*[2*n + 1] (ppoint f) ∘* tinverse qed
  | (n, fin.mk 5 H) :=
    proof (π→*[2*n + 1] (boundary_map f) ∘* tinverse)
          ∘* pcast (ap (ptrunc 0) (loop_space_succ_eq_in Y (2*n+1))) qed
  | (n, fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition loop_spaces_fun3eq2 [reducible]
    : Π(n : +6ℕ), loop_spaces3eq2 n ∘* ptrunc_functor 0 (loop_spaces_fun2 n) ~*
      loop_spaces_fun3 n ∘* loop_spaces3eq2 (S n)
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) :=
    begin
      refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹*,
      refine !ptrunc_functor_pcompose ⬝* _,
      apply pwhisker_left, apply ptrunc_functor_pcast,
    end
  | (n, fin.mk 3 H) :=
    begin
      refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹*,
      refine !ptrunc_functor_pcompose ⬝* _,
      apply pwhisker_left, apply ptrunc_functor_pinverse
    end
  | (n, fin.mk 4 H) :=
    begin
      refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹*,
      refine !ptrunc_functor_pcompose ⬝* _,
      apply pwhisker_left, apply ptrunc_functor_pinverse
    end
  | (n, fin.mk 5 H) :=
    begin
      refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹*,
      refine !ptrunc_functor_pcompose ⬝* _,
      apply pconcat2,
      { refine !ptrunc_functor_pcompose ⬝* _,
        apply pwhisker_left, apply ptrunc_functor_pinverse},
      { apply ptrunc_functor_pcast}
    end
  | (n, fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition LES_of_loop_spaces3 [constructor] : chain_complex +6ℕ :=
  transfer_chain_complex
    LES_of_loop_spaces2
    loop_spaces_fun3
    loop_spaces3eq2
    loop_spaces_fun3eq2

  definition is_exact_LES_of_loop_spaces3 : is_exact (LES_of_loop_spaces3) :=
  begin
    intro n,
    apply is_exact_at_transfer,
    apply is_exact_at_trunc,
    apply is_exact_type_LES_of_loop_spaces2
  end

  end

  open is_trunc
  universe variable u
  variables {X Y : pType.{u}} (f : X →* Y) (n : ℕ)
  include f

  /- the carrier of the fiber sequence is definitionally what we want (as pointed sets) -/
  example : LES_of_loop_spaces3 f (str_of_nat 6)  = π*[2] Y          :> Set* := by reflexivity
  example : LES_of_loop_spaces3 f (str_of_nat 7)  = π*[2] X          :> Set* := by reflexivity
  example : LES_of_loop_spaces3 f (str_of_nat 8)  = π*[2] (pfiber f) :> Set* := by reflexivity
  example : LES_of_loop_spaces3 f (str_of_nat 9)  = π*[3] Y          :> Set* := by reflexivity
  example : LES_of_loop_spaces3 f (str_of_nat 10) = π*[3] X          :> Set* := by reflexivity
  example : LES_of_loop_spaces3 f (str_of_nat 11) = π*[3] (pfiber f) :> Set* := by reflexivity

  definition LES_of_loop_spaces3_0 : LES_of_loop_spaces3 f (n, 0) = π*[2*n] Y :=
  by reflexivity
  definition LES_of_loop_spaces3_1 : LES_of_loop_spaces3 f (n, 1) = π*[2*n] X :=
  by reflexivity
  definition LES_of_loop_spaces3_2 : LES_of_loop_spaces3 f (n, 2) = π*[2*n] (pfiber f) :=
  by reflexivity
  definition LES_of_loop_spaces3_3 : LES_of_loop_spaces3 f (n, 3) = π*[2*n + 1] Y :=
  by reflexivity
  definition LES_of_loop_spaces3_4 : LES_of_loop_spaces3 f (n, 4) = π*[2*n + 1] X :=
  by reflexivity
  definition LES_of_loop_spaces3_5 : LES_of_loop_spaces3 f (n, 5) = π*[2*n + 1] (pfiber f):=
  by reflexivity

  /- the functions of the fiber sequence is definitionally what we want (as pointed function).
      -/

  definition LES_of_loop_spaces_fun3_0 :
    cc_to_fn (LES_of_loop_spaces3 f) (n, 0) = π→*[2*n] f :=
  by reflexivity
  definition LES_of_loop_spaces_fun3_1 :
    cc_to_fn (LES_of_loop_spaces3 f) (n, 1) = π→*[2*n] (ppoint f) :=
  by reflexivity
  definition LES_of_loop_spaces_fun3_2 : cc_to_fn (LES_of_loop_spaces3 f) (n, 2) =
    π→*[2*n] (boundary_map f) ∘* pcast (ap (ptrunc 0) (loop_space_succ_eq_in Y (2*n))) :=
  by reflexivity
  definition LES_of_loop_spaces_fun3_3 :
    cc_to_fn (LES_of_loop_spaces3 f) (n, 3) = π→*[2*n + 1] f ∘* tinverse :=
  by reflexivity
  definition LES_of_loop_spaces_fun3_4 :
    cc_to_fn (LES_of_loop_spaces3 f) (n, 4) = π→*[2*n + 1] (ppoint f) ∘* tinverse :=
  by reflexivity
  definition LES_of_loop_spaces_fun3_5 : cc_to_fn (LES_of_loop_spaces3 f) (n, 5) =
    (π→*[2*n + 1] (boundary_map f) ∘* tinverse) ∘*
    pcast (ap (ptrunc 0) (loop_space_succ_eq_in Y (2*n+1))) :=
  by reflexivity

  definition group_LES_of_loop_spaces3_0 :
    Π(k : ℕ) (H : k + 3 < succ 5), group (LES_of_loop_spaces3 f (0, fin.mk (k+3) H))
  | 0     H := begin rexact group_homotopy_group 0 Y end
  | 1     H := begin rexact group_homotopy_group 0 X end
  | 2     H := begin rexact group_homotopy_group 0 (pfiber f) end
  | (k+3) H := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition comm_group_LES_of_loop_spaces3 (n : ℕ) : Π(x : fin (succ 5)),
    comm_group (LES_of_loop_spaces3 f (n + 1, x))
  | (fin.mk 0 H) := proof comm_group_homotopy_group (2*n) Y qed
  | (fin.mk 1 H) := proof comm_group_homotopy_group (2*n) X qed
  | (fin.mk 2 H) := proof comm_group_homotopy_group (2*n) (pfiber f) qed
  | (fin.mk 3 H) := proof comm_group_homotopy_group (2*n+1) Y qed
  | (fin.mk 4 H) := proof comm_group_homotopy_group (2*n+1) X qed
  | (fin.mk 5 H) := proof comm_group_homotopy_group (2*n+1) (pfiber f) qed
  | (fin.mk (k+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition CommGroup_LES_of_loop_spaces3 (n : +6ℕ) : CommGroup.{u} :=
  CommGroup.mk (LES_of_loop_spaces3 f (pr1 n + 1, pr2 n))
               (comm_group_LES_of_loop_spaces3 f (pr1 n) (pr2 n))

  definition homomorphism_LES_of_loop_spaces_fun3 : Π(k : +6ℕ),
    CommGroup_LES_of_loop_spaces3 f (S k) →g CommGroup_LES_of_loop_spaces3 f k
  | (k, fin.mk 0 H) :=
    proof homomorphism.mk (cc_to_fn (LES_of_loop_spaces3 f) (k + 1, 0))
                          (phomotopy_group_functor_mul _ _) qed
  | (k, fin.mk 1 H) :=
    proof homomorphism.mk (cc_to_fn (LES_of_loop_spaces3 f) (k + 1, 1))
                          (phomotopy_group_functor_mul _ _) qed
  | (k, fin.mk 2 H) :=
    begin
      apply homomorphism.mk (cc_to_fn (LES_of_loop_spaces3 f) (k + 1, 2)),
      exact abstract begin rewrite [LES_of_loop_spaces_fun3_2],
      refine @is_homomorphism_compose _ _ _ _ _ _ (π→*[2 * (k + 1)] boundary_map f) _ _ _,
      { apply group_homotopy_group ((2 * k) + 1)},
      { apply phomotopy_group_functor_mul},
      { rewrite [▸*, -ap_compose', ▸*],
        apply is_homomorphism_cast_loop_space_succ_eq_in} end end
    end
  | (k, fin.mk 3 H) :=
    begin
      apply homomorphism.mk (cc_to_fn (LES_of_loop_spaces3 f) (k + 1, 3)),
      exact abstract begin rewrite [LES_of_loop_spaces_fun3_3],
      refine @is_homomorphism_compose _ _ _ _ _ _ (π→*[2 * (k + 1) + 1] f) tinverse _ _,
      { apply group_homotopy_group (2 * (k+1))},
      { apply phomotopy_group_functor_mul},
      { apply is_homomorphism_inverse} end end
    end
  | (k, fin.mk 4 H) :=
    begin
      apply homomorphism.mk (cc_to_fn (LES_of_loop_spaces3 f) (k + 1, 4)),
      exact abstract begin rewrite [LES_of_loop_spaces_fun3_4],
      refine @is_homomorphism_compose _ _ _ _ _ _ (π→*[2 * (k + 1) + 1] (ppoint f)) tinverse _ _,
      { apply group_homotopy_group (2 * (k+1))},
      { apply phomotopy_group_functor_mul},
      { apply is_homomorphism_inverse} end end
    end
  | (k, fin.mk 5 H) :=
    begin
      apply homomorphism.mk (cc_to_fn (LES_of_loop_spaces3 f) (k + 1, 5)),
      exact abstract begin rewrite [LES_of_loop_spaces_fun3_5],
      refine @is_homomorphism_compose _ _ _ _ _ _
               (π→*[2 * (k + 1) + 1] (boundary_map f) ∘ tinverse) _ _ _,
      { refine @is_homomorphism_compose _ _ _ _ _ _
                 (π→*[2 * (k + 1) + 1] (boundary_map f)) tinverse _ _,
        { apply group_homotopy_group (2 * (k+1))},
        { apply phomotopy_group_functor_mul},
        { apply is_homomorphism_inverse}},
      { rewrite [▸*, -ap_compose', ▸*],
        apply is_homomorphism_cast_loop_space_succ_eq_in} end end
    end
  | (k, fin.mk (l+6) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  --TODO: the maps 3, 4 and 5 are anti-homomorphisms.

  end
end chain_complex'
