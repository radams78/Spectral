/-
Copyright (c) 2016 Floris van Doorn. All rights reserved.
Released under Apache 2.0 license as described in the file LICENSE.
Authors: Floris van Doorn

We define the fiber sequence of a pointed map f : X →* Y. We mostly follow the proof in section 8.4
of the book. First we define a sequence fiber_sequence as in Definition 8.4.3.
It has types X(n) : Type*
X(0)   := Y,
X(1)   := X,
X(n+1) := pfiber (f(n))
with functions f(n) : X(n+1) →* X(n)
f(0)   := f
f(n+1) := ppoint f(n)
We prove that this is an exact sequence.
Then we prove Lemma 8.4.3, by showing that X(n+3) ≃* Ω(X(n)) and that this equivalence sends
the pointed map f(n+3) to -Ω(f(n)), i.e. the composition of Ω(f(n)) with path inversion.

Using this equivalence we get a boundary_map : Ω(Y) → pfiber f. Now we can define a new
fiber sequence X'(n) : Type*, and here we slightly diverge from the book. We define it as
X'(0)   := Y,
X'(1)   := X,
X'(2)   := pfiber f
X'(n+3) := Ω(X'(n))
with maps f'(n) : X'(n+1) →* X'(n)
f'(0) := f
f'(1) := ppoint f
f'(2) := boundary_map f
f'(n+3) := Ω(f'(n))

We can show that these sequences are equivalent, up to sign, hence the sequence (X',f') is an exact
sequence. Now we get the fiber sequence by taking the set-truncation of this sequence.

In the book the odd levels

PART 3:

Part 4:

-/

import .chain_complex algebra.homotopy_group

open eq pointed sigma fiber equiv is_equiv sigma.ops is_trunc nat trunc algebra function sum

section MOVE
  -- TODO: MOVE
  open group chain_complex
  definition pinverse_pinverse (A : Type*) : pinverse ∘* pinverse ~* pid (Ω A) :=
  begin
    fapply phomotopy.mk,
    { apply inv_inv},
    { reflexivity}
  end

  definition pequiv_pinverse (A : Type*) : Ω A ≃* Ω A :=
  pequiv_of_pmap pinverse !is_equiv_eq_inverse

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

end MOVE

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
  include f

  definition fiber_sequence_carrier (n : ℕ) : Type* :=
  (fiber_sequence_helpern ⟨X, Y, f⟩ n).2.1

  definition fiber_sequence_fun (n : ℕ)
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
  definition fiber_sequence_carrier_equiv (n : ℕ)
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
  definition fiber_sequence_carrier_equiv_eq (n : ℕ)
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

  definition fiber_sequence_carrier_equiv_inv_eq (n : ℕ)
    (p : Ω(fiber_sequence_carrier n)) : (fiber_sequence_carrier_equiv n)⁻¹ᵉ p =
      fiber.mk (fiber.mk pt (respect_pt (fiber_sequence_fun n) ⬝ p)) idp :=
  begin
    apply inv_eq_of_eq,
    refine _ ⬝ !fiber_sequence_carrier_equiv_eq⁻¹, esimp,
    exact !inv_con_cancel_left⁻¹
  end

  definition fiber_sequence_carrier_pequiv (n : ℕ)
    : fiber_sequence_carrier (n+3) ≃* Ω(fiber_sequence_carrier n) :=
  pequiv_of_equiv (fiber_sequence_carrier_equiv n)
    begin
      esimp,
      apply con.left_inv
    end

  definition fiber_sequence_carrier_pequiv_eq (n : ℕ)
    (x : fiber_sequence_carrier (n+1)) (p : fiber_sequence_fun n x = pt)
    (q : fiber_sequence_fun (n+1) (fiber.mk x p) = pt)
    : fiber_sequence_carrier_pequiv n (fiber.mk (fiber.mk x p) q)
      = !respect_pt⁻¹ ⬝ ap (fiber_sequence_fun n) q⁻¹ ⬝ p :=
  fiber_sequence_carrier_equiv_eq n x p q

  definition fiber_sequence_carrier_pequiv_inv_eq (n : ℕ)
    (p : Ω(fiber_sequence_carrier n)) : (fiber_sequence_carrier_pequiv n)⁻¹ᵉ* p =
      fiber.mk (fiber.mk pt (respect_pt (fiber_sequence_fun n) ⬝ p)) idp :=
  by rexact fiber_sequence_carrier_equiv_inv_eq n p

  /- Lemma 8.4.4(iii) -/
  definition fiber_sequence_fun_eq_helper (n : ℕ)
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

  theorem fiber_sequence_carrier_pequiv_eq_point_eq_idp (n : ℕ) :
    fiber_sequence_carrier_pequiv_eq n
      (Point (fiber_sequence_carrier (n+1)))
      (respect_pt (fiber_sequence_fun n))
      (respect_pt (fiber_sequence_fun (n + 1))) = idp :=
  begin
    apply con_inv_eq_idp,
    refine ap (λx, whisker_left _ (_ ⬝ x)) _ ⬝ _,
    { reflexivity},
    { reflexivity},
    refine ap (whisker_left _)
              (transport_eq_Fl_idp_left (fiber_sequence_fun n)
                                        (respect_pt (fiber_sequence_fun n))) ⬝ _,
    apply whisker_left_idp_con_eq_assoc
  end

  theorem fiber_sequence_fun_phomotopy_helper (n : ℕ) :
    (fiber_sequence_carrier_pequiv n ∘*
      fiber_sequence_fun (n + 3)) ∘*
        (fiber_sequence_carrier_pequiv (n + 1))⁻¹ᵉ* ~*
          ap1 (fiber_sequence_fun n) ∘* pinverse :=
  begin
    fapply phomotopy.mk,
    { exact chain_complex.fiber_sequence_fun_eq_helper f n},
    { esimp, rewrite [idp_con], refine _ ⬝ whisker_left _ !idp_con⁻¹,
      apply whisker_right,
      apply whisker_left,
      exact chain_complex.fiber_sequence_carrier_pequiv_eq_point_eq_idp f n}
  end

  theorem fiber_sequence_fun_eq (n : ℕ) : Π(x : fiber_sequence_carrier (n + 4)),
    fiber_sequence_carrier_pequiv n (fiber_sequence_fun (n + 3) x) =
      ap1 (fiber_sequence_fun n) (fiber_sequence_carrier_pequiv (n + 1) x)⁻¹ :=
  begin
    apply homotopy_of_inv_homotopy_pre (fiber_sequence_carrier_pequiv (n + 1)),
    apply fiber_sequence_fun_eq_helper n
  end

  theorem fiber_sequence_fun_phomotopy (n : ℕ) :
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

  /- The maps between the homotopy groups -/
  definition loop_spaces_fun
    : Π(n : ℕ), loop_spaces (n+1) →* loop_spaces n
  | 0     := proof f qed
  | 1     := proof ppoint f qed
  | 2     := proof boundary_map qed
  | (k+3) := proof ap1 (loop_spaces_fun k) qed

  definition loop_spaces_fun_add3 [unfold_full] (n : ℕ) :
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

  definition fiber_sequence_pequiv_loop_spaces_add3 (n : ℕ)
    : fiber_sequence_pequiv_loop_spaces (n + 3) =
      ap1 (fiber_sequence_pequiv_loop_spaces n) ∘* fiber_sequence_carrier_pequiv n :=
  by reflexivity

  definition fiber_sequence_pequiv_loop_spaces_3_phomotopy
    : fiber_sequence_pequiv_loop_spaces 3 ~* proof fiber_sequence_carrier_pequiv nat.zero qed :=
  begin
    refine pwhisker_right _ ap1_id ⬝* _,
    apply pid_comp
  end

  theorem fiber_sequence_phomotopy_loop_spaces_helper1 (n : ℕ) :
    fiber_sequence_pequiv_loop_spaces n ∘* fiber_sequence_fun n ~*
      loop_spaces_fun n ∘* fiber_sequence_pequiv_loop_spaces (n + 1) →
    fiber_sequence_pequiv_loop_spaces (n + 3) ∘* fiber_sequence_fun (n + 3) ~*
      (loop_spaces_fun (n + 3) ∘* pinverse) ∘* fiber_sequence_pequiv_loop_spaces (n + 4) :=
  begin
    intro IH,
    replace (n + 4) with (n + 1 + 3),
    rewrite [fiber_sequence_pequiv_loop_spaces_add3 n,
             fiber_sequence_pequiv_loop_spaces_add3 (n+1)],
    refine !passoc ⬝* _,
    refine pwhisker_left _ (fiber_sequence_fun_phomotopy n) ⬝* _,
    refine !passoc⁻¹* ⬝* _ ⬝* !passoc,
    apply pwhisker_right,
    rewrite [loop_spaces_fun_add3],
    refine _ ⬝* !passoc⁻¹*,
    refine _ ⬝* pwhisker_left _ !ap1_compose_pinverse,
    refine !passoc⁻¹* ⬝* _ ⬝* !passoc,
    apply pwhisker_right,
    refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose,
    apply ap1_phomotopy,
    exact IH
  end

  -- theorem fiber_sequence_phomotopy_loop_spaces_helper2 (n : ℕ) :
  --   fiber_sequence_pequiv_loop_spaces (n + 2) ∘* fiber_sequence_fun (n + 2) ~*
  --     (loop_spaces_fun (n + 2) ∘* pinverse) ∘* fiber_sequence_pequiv_loop_spaces (n + 3) →
  --   fiber_sequence_pequiv_loop_spaces (n + 5) ∘* fiber_sequence_fun (n + 5) ~*
  --     loop_spaces_fun (n + 5) ∘* fiber_sequence_pequiv_loop_spaces (n + 6) :=
  -- begin
  --   intro IH,
  --   replace (n + 5) with (n + 2 + 3),
  --   replace (n + 6) with (n + 3 + 3),
  --   rewrite [fiber_sequence_pequiv_loop_spaces_add3 (n+2),
  --            fiber_sequence_pequiv_loop_spaces_add3 (n+3)],
  --   refine !passoc ⬝* _,
  --   refine pwhisker_left _ (fiber_sequence_fun_phomotopy (n+2)) ⬝* _,
  --   refine !passoc⁻¹* ⬝* _ ⬝* !passoc,
  --   apply pwhisker_right,
  --   rewrite [loop_spaces_fun_add3],
  --   refine !passoc⁻¹* ⬝* _,
  --   refine pwhisker_right _ !ap1_compose⁻¹* ⬝* _,
  --   refine pwhisker_right _ (ap1_phomotopy IH) ⬝* _,
  --   refine pwhisker_right _ !ap1_compose ⬝* _,
  --   refine pwhisker_right _ (pwhisker_right _ !ap1_compose) ⬝* _,
  --   refine !passoc ⬝* !passoc ⬝* _,
  --   apply pwhisker_left,
  --   refine pwhisker_left _ !ap1_compose_pinverse ⬝* _,
  --   refine !passoc⁻¹* ⬝* _ ⬝* !pid_comp,
  --   apply pwhisker_right,
  --   refine pwhisker_right _ !ap1_pinverse ⬝* _,
  --   apply pinverse_pinverse
  -- end

  definition pid_or_pinverse : Π(n : ℕ), loop_spaces n ≃* loop_spaces n
  | 0     := pequiv.rfl
  | 1     := pequiv.rfl
  | 2     := pequiv.rfl
  | (k+3) := loop_pequiv_loop (pid_or_pinverse k) ⬝e* !pequiv_pinverse

  theorem fiber_sequence_phomotopy_loop_spaces : Π(n : ℕ),
    fiber_sequence_pequiv_loop_spaces n ∘* fiber_sequence_fun n ~*
      loop_spaces_fun n ∘* fiber_sequence_pequiv_loop_spaces (n + 1) ⊎
    fiber_sequence_pequiv_loop_spaces n ∘* fiber_sequence_fun n ~*
      (loop_spaces_fun n ∘* pid_or_pinverse (n + 1)) ∘* fiber_sequence_pequiv_loop_spaces (n + 1)
  | 0     := by apply inl; reflexivity
  | 1     := by apply inl; reflexivity
  | 2     :=
    begin
      apply inl,
      refine !pid_comp ⬝* _,
      replace loop_spaces_fun 2 with boundary_map,
      refine _ ⬝* pwhisker_left _ fiber_sequence_pequiv_loop_spaces_3_phomotopy⁻¹*,
      apply phomotopy_of_pinv_right_phomotopy,
      reflexivity
    end
  | (k+3) :=
    begin
      cases (fiber_sequence_phomotopy_loop_spaces k) with H H,
      { apply inr, apply chain_complex.fiber_sequence_phomotopy_loop_spaces_helper1 f k, exact H},
      { revert H, match k with
        | 0 :=
          begin
            intro H, apply inr, apply chain_complex.fiber_sequence_phomotopy_loop_spaces_helper1 f,
            refine H ⬝* _, apply pwhisker_right, apply comp_pid
          end
        | 1 :=
          begin
            intro H, apply inr, apply chain_complex.fiber_sequence_phomotopy_loop_spaces_helper1 f,
            refine H ⬝* _, apply pwhisker_right, apply comp_pid
          end
        | (l+2) :=
          begin
            intro H, apply inl, apply chain_complex.fiber_sequence_phomotopy_loop_spaces_helper2 f,
            exact H
          end
        end }
    end

  definition LES_of_loop_spaces [constructor] : type_chain_complex +ℕ :=
  transfer_type_chain_complex
    fiber_sequence
    loop_spaces_fun
    fiber_sequence_pequiv_loop_spaces
    sorry --(fiber_sequence_phomotopy_loop_spaces)

  definition is_exact_LES_of_loop_spaces : is_exact_t LES_of_loop_spaces :=
  begin
    intro n,
    apply is_exact_at_t_transfer,
    apply is_exact_fiber_sequence
  end

  open prod succ_str fin
exit
  /--------------
      PART 3
   --------------/

  definition loop_spaces2 [reducible] : +3ℕ → Type*
  | (n, fin.mk 0 H) := Ω[n] Y
  | (n, fin.mk 1 H) := Ω[n] X
  | (n, fin.mk k H) := Ω[n] (pfiber f)

  definition loop_spaces2_add1 (n : ℕ) : Π(x : fin (nat.succ 2)),
    loop_spaces2 (n+1, x) = Ω (loop_spaces2 (n, x))
  | (fin.mk 0 H) := by reflexivity
  | (fin.mk 1 H) := by reflexivity
  | (fin.mk 2 H) := by reflexivity
  | (fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition loop_spaces_fun2 : Π(n : +3ℕ), loop_spaces2 (S n) →* loop_spaces2 n
  | (n, fin.mk 0 H) := proof Ω→[n] f qed
  | (n, fin.mk 1 H) := proof Ω→[n] (ppoint f) qed
  | (n, fin.mk 2 H) := proof Ω→[n] boundary_map ∘* pcast (loop_space_succ_eq_in Y n) qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition loop_spaces_fun2_add1_0 (n : ℕ) (H : 0 < succ 2)
    : loop_spaces_fun2 (n+1, fin.mk 0 H) ~*
      cast proof idp qed ap1 (loop_spaces_fun2 (n, fin.mk 0 H)) :=
  by reflexivity

  definition loop_spaces_fun2_add1_1 (n : ℕ) (H : 1 < succ 2)
    : loop_spaces_fun2 (n+1, fin.mk 1 H) ~*
      cast proof idp qed ap1 (loop_spaces_fun2 (n, fin.mk 1 H)) :=
  by reflexivity

  definition loop_spaces_fun2_add1_2 (n : ℕ) (H : 2 < succ 2)
    : loop_spaces_fun2 (n+1, fin.mk 2 H) ~*
      cast proof idp qed ap1 (loop_spaces_fun2 (n, fin.mk 2 H)) :=
  begin
    esimp,
    refine _ ⬝* !ap1_compose⁻¹*,
    apply pwhisker_left,
    apply pcast_ap_loop_space
  end

  definition nat_of_str [unfold 2] [reducible] {n : ℕ} : ℕ × fin (succ n) → ℕ :=
  λx, succ n * pr1 x + val (pr2 x)

  definition str_of_nat {n : ℕ} : ℕ → ℕ × fin (succ n) :=
  λm, (m / (succ n), mk_mod n m)

  definition nat_of_str_3S [unfold 2] [reducible]
    : Π(x : stratified +ℕ 2), nat_of_str x + 1 = nat_of_str (@S (stratified +ℕ 2) x)
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) := by reflexivity
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

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
      { rewrite [add.comm, add_mul_div_self_left _ _ (!zero_lt_succ), ▸*,
                 div_eq_zero_of_lt H, zero_add]},
      { apply eq_of_veq, esimp [mk_mod],
        rewrite [add.comm, add_mul_mod_self_left, ▸*, mod_eq_of_lt H]}
    end end

  /-
    note: in the following theorem the (n+1) case is 3 times the same,
    so maybe this can be simplified
  -/
  definition loop_spaces2_pequiv' : Π(n : ℕ) (x : fin (nat.succ 2)),
    loop_spaces (nat_of_str (n, x)) ≃* loop_spaces2 (n, x)
  |  0    (fin.mk 0 H)     := by reflexivity
  |  0    (fin.mk 1 H)     := by reflexivity
  |  0    (fin.mk 2 H)     := by reflexivity
  | (n+1) (fin.mk 0 H)     :=
    begin
      apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 0 H)
    end
  | (n+1) (fin.mk 1 H)     :=
    begin
      apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 1 H)
    end
  | (n+1) (fin.mk 2 H)     :=
    begin
      apply loop_pequiv_loop,
      rexact loop_spaces2_pequiv' n (fin.mk 2 H)
    end
  | n     (fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition loop_spaces2_pequiv : Π(x : +3ℕ),
    loop_spaces (nat_of_str x) ≃* loop_spaces2 x
  | (n, x) := loop_spaces2_pequiv' n x

  local attribute loop_pequiv_loop [reducible]
  /- all cases where n>0 are basically the same -/
  definition loop_spaces_fun2_phomotopy (x : +3ℕ) :
    loop_spaces2_pequiv x ∘* loop_spaces_fun (nat_of_str x) ~*
      (loop_spaces_fun2 x ∘* loop_spaces2_pequiv (S x))
    ∘* pcast (ap (loop_spaces) (nat_of_str_3S x)) :=
  begin
    cases x with n x, cases x with k H,
    cases k with k, rotate 1, cases k with k, rotate 1, cases k with k, rotate 2,
    { /-k=0-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹* ⬝* !comp_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ !loop_spaces_fun2_add1_0⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=1-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹* ⬝* !comp_pid⁻¹*,
        reflexivity},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ !loop_spaces_fun2_add1_1⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=2-/
      induction n with n IH,
      { refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹*,
        refine !comp_pid⁻¹* ⬝* pconcat2 _ _,
        { exact (comp_pid (chain_complex.boundary_map f))⁻¹*},
        { refine cast (ap (λx, _ ~* x) !loop_pequiv_loop_rfl)⁻¹ _, reflexivity}},
      { refine _ ⬝* !comp_pid⁻¹*,
        refine _ ⬝* pwhisker_right _ !loop_spaces_fun2_add1_2⁻¹*,
        refine !ap1_compose⁻¹* ⬝* _ ⬝* !ap1_compose, apply ap1_phomotopy,
        exact IH ⬝* !comp_pid}},
    { /-k=k'+3-/ exfalso, apply lt_le_antisymm H, apply le_add_left}
  end

  definition LES_of_loop_spaces2 [constructor] : type_chain_complex +3ℕ :=
  transfer_type_chain_complex2
    LES_of_loop_spaces
    !fin_prod_nat_equiv_nat
    nat_of_str_3S
    @loop_spaces_fun2
    @loop_spaces2_pequiv
    begin
      intro m x,
      refine loop_spaces_fun2_phomotopy m x ⬝ _,
      apply ap (loop_spaces_fun2 m), apply ap (loop_spaces2_pequiv (S m)),
      esimp, exact ap010 cast !ap_compose⁻¹ x
    end

  definition is_exact_LES_of_loop_spaces2 : is_exact_t LES_of_loop_spaces2 :=
  begin
    intro n,
    apply is_exact_at_transfer2,
    apply is_exact_LES_of_loop_spaces
  end

  definition LES_of_homotopy_groups' [constructor] : chain_complex +3ℕ :=
  trunc_chain_complex LES_of_loop_spaces2

/--------------
    PART 4
 --------------/

  definition homotopy_groups [reducible] : +3ℕ → Set*
  | (n, fin.mk 0 H) := π*[n] Y
  | (n, fin.mk 1 H) := π*[n] X
  | (n, fin.mk k H) := π*[n] (pfiber f)

  definition homotopy_groups_pequiv_loop_spaces2 [reducible]
    : Π(n : +3ℕ), ptrunc 0 (loop_spaces2 n) ≃* homotopy_groups n
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) := by reflexivity
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition homotopy_groups_fun : Π(n : +3ℕ), homotopy_groups (S n) →* homotopy_groups n
  | (n, fin.mk 0 H) := proof π→*[n] f qed
  | (n, fin.mk 1 H) := proof π→*[n] (ppoint f) qed
  | (n, fin.mk 2 H) :=
    proof π→*[n] boundary_map ∘* pcast (ap (ptrunc 0) (loop_space_succ_eq_in Y n)) qed
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition homotopy_groups_fun_phomotopy_loop_spaces_fun2 [reducible]
    : Π(n : +3ℕ), homotopy_groups_pequiv_loop_spaces2 n ∘* ptrunc_functor 0 (loop_spaces_fun2 n) ~*
      homotopy_groups_fun n ∘* homotopy_groups_pequiv_loop_spaces2 (S n)
  | (n, fin.mk 0 H) := by reflexivity
  | (n, fin.mk 1 H) := by reflexivity
  | (n, fin.mk 2 H) :=
    begin
      refine !pid_comp ⬝* _ ⬝* !comp_pid⁻¹*,
      refine !ptrunc_functor_pcompose ⬝* _,
      apply pwhisker_left, apply ptrunc_functor_pcast,
    end
  | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition LES_of_homotopy_groups [constructor] : chain_complex +3ℕ :=
  transfer_chain_complex
    LES_of_homotopy_groups'
    homotopy_groups_fun
    homotopy_groups_pequiv_loop_spaces2
    homotopy_groups_fun_phomotopy_loop_spaces_fun2

  definition is_exact_LES_of_homotopy_groups : is_exact LES_of_homotopy_groups :=
  begin
    intro n,
    apply is_exact_at_transfer,
    apply is_exact_at_trunc,
    apply is_exact_LES_of_loop_spaces2
  end

  variable (n : ℕ)

  /- the carrier of the fiber sequence is definitionally what we want (as pointed sets) -/
  example : LES_of_homotopy_groups (str_of_nat 6)  = π*[2] Y          :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 7)  = π*[2] X          :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 8)  = π*[2] (pfiber f) :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 9)  = π*[3] Y          :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 10) = π*[3] X          :> Set* := by reflexivity
  example : LES_of_homotopy_groups (str_of_nat 11) = π*[3] (pfiber f) :> Set* := by reflexivity

  definition LES_of_homotopy_groups_0 : LES_of_homotopy_groups (n, 0) = π*[n] Y :=
  by reflexivity
  definition LES_of_homotopy_groups_1 : LES_of_homotopy_groups (n, 1) = π*[n] X :=
  by reflexivity
  definition LES_of_homotopy_groups_2 : LES_of_homotopy_groups (n, 2) = π*[n] (pfiber f) :=
  by reflexivity

  /- the functions of the fiber sequence is definitionally what we want (as pointed function).
      -/

  definition LES_of_homotopy_groups_fun_0 :
    cc_to_fn LES_of_homotopy_groups (n, 0) = π→*[n] f :=
  by reflexivity
  definition LES_of_homotopy_groups_fun_1 :
    cc_to_fn LES_of_homotopy_groups (n, 1) = π→*[n] (ppoint f) :=
  by reflexivity
  definition LES_of_homotopy_groups_fun_2 : cc_to_fn LES_of_homotopy_groups (n, 2) =
    π→*[n] boundary_map ∘* pcast (ap (ptrunc 0) (loop_space_succ_eq_in Y n)) :=
  by reflexivity

  open group

  definition group_LES_of_homotopy_groups_0
    : Π(x : fin (succ 2)), group (LES_of_homotopy_groups (1, x))
  | (fin.mk 0     H) := begin rexact group_homotopy_group 0 Y end
  | (fin.mk 1     H) := begin rexact group_homotopy_group 0 X end
  | (fin.mk 2     H) := begin rexact group_homotopy_group 0 (pfiber f) end
  | (fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition comm_group_LES_of_homotopy_groups (n : ℕ) : Π(x : fin (succ 2)),
    comm_group (LES_of_homotopy_groups (n + 2, x))
  | (fin.mk 0 H) := proof comm_group_homotopy_group n Y qed
  | (fin.mk 1 H) := proof comm_group_homotopy_group n X qed
  | (fin.mk 2 H) := proof comm_group_homotopy_group n (pfiber f) qed
  | (fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition CommGroup_LES_of_homotopy_groups (n : +3ℕ) : CommGroup.{u} :=
  CommGroup.mk (LES_of_homotopy_groups (pr1 n + 2, pr2 n))
               (comm_group_LES_of_homotopy_groups (pr1 n) (pr2 n))

  definition homomorphism_LES_of_homotopy_groups_fun : Π(k : +3ℕ),
    CommGroup_LES_of_homotopy_groups (S k) →g CommGroup_LES_of_homotopy_groups k
  | (k, fin.mk 0 H) :=
    proof homomorphism.mk (cc_to_fn LES_of_homotopy_groups (k + 2, 0))
                          (phomotopy_group_functor_mul _ _) qed
  | (k, fin.mk 1 H) :=
    proof homomorphism.mk (cc_to_fn LES_of_homotopy_groups (k + 2, 1))
                          (phomotopy_group_functor_mul _ _) qed
  | (k, fin.mk 2 H) :=
    begin
      apply homomorphism.mk (cc_to_fn LES_of_homotopy_groups (k + 2, 2)),
      exact abstract begin rewrite [LES_of_homotopy_groups_fun_2],
      refine @is_homomorphism_compose _ _ _ _ _ _ (π→*[k + 2] boundary_map) _ _ _,
      { apply group_homotopy_group (k + 1)},
      { apply phomotopy_group_functor_mul},
      { rewrite [▸*, -ap_compose', ▸*],
        apply is_homomorphism_cast_loop_space_succ_eq_in} end end
    end
  | (k, fin.mk (l+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  end
end chain_complex
