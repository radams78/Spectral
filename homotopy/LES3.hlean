import .LES_of_homotopy_groups

open eq algebra equiv is_equiv function trunc is_trunc pointed prod fin nat fiber succ_str


/--------------
    PART 3
 --------------/

namespace chain_complex

  section
  universe variable u
  parameters {X Y : pType.{u}} (f : X →* Y)

  definition loop_spaces2 [reducible] : +3ℕ → Type*
  | (n, fin.mk 0 H) := Ω[n] Y
  | (n, fin.mk 1 H) := Ω[n] X
  | (n, fin.mk k H) := Ω[n] (pfiber f)

  definition loop_spaces2_add1 (n : ℕ) : Π(x : fin (succ 2)),
    loop_spaces2 (n+1, x) = Ω(loop_spaces2 (n, x))
  | (fin.mk 0 H) := by reflexivity
  | (fin.mk 1 H) := by reflexivity
  | (fin.mk 2 H) := by reflexivity
  | (fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition loop_spaces_fun2 : Π(n : +3ℕ), loop_spaces2 (S n) →* loop_spaces2 n
  | (n, fin.mk 0 H) := proof Ω→[n] f qed
  | (n, fin.mk 1 H) := proof Ω→[n] (ppoint f) qed
  | (n, fin.mk 2 H) :=
    proof Ω→[n] (boundary_map f) ∘* pcast (loop_space_succ_eq_in Y n) qed
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
    esimp, refine _ ⬝* !ap1_compose⁻¹*,
    apply pwhisker_left,
    apply pcast_ap_loop_space
  end

  definition str_mul_of_str {n m : ℕ} : ℕ × fin (succ n) → ℕ × fin (succ n * succ m) :=
  λx, (pr1 x / succ m, fin.mk (succ n * (pr1 x % succ m) + val (pr2 x))
  abstract begin
    rewrite [mul_succ], apply add_lt_add_of_le_of_lt,
    { apply mul_le_mul_left,
      apply le_of_lt_succ, apply mod_lt, apply succ_pos},
    { apply is_lt}
  end end)

  definition str_of_str_mul {n m : ℕ}
    : ℕ × fin (succ n * succ m) → ℕ × fin (succ n) :=
  λx, (succ m * pr1 x + val (pr2 x) / (succ n), mk_mod n (val (pr2 x)))

  -- definition nat_of_str_6S [unfold 2] [reducible]
  --   : Π(x : stratified +ℕ 5), nat_of_str x + 1 = nat_of_str (@S (stratified +ℕ 5) x)
  -- | (n, fin.mk 0 H) := by reflexivity
  -- | (n, fin.mk 1 H) := by reflexivity
  -- | (n, fin.mk 2 H) := by reflexivity
  -- | (n, fin.mk 3 H) := by reflexivity
  -- | (n, fin.mk 4 H) := by reflexivity
  -- | (n, fin.mk 5 H) := by reflexivity
  -- | (n, fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition nat_prod_fin_equiv_nat_prod_fin_mul [constructor] (n m : ℕ)
    : ℕ × fin (succ n) ≃ ℕ × fin (succ n * succ m) :=
  equiv.MK str_mul_of_str str_of_str_mul
    abstract begin
      intro m, exact sorry
-- unfold [nat_of_str, str_of_nat, mk_mod],
--       refine _ ⬝ (eq_div_mul_add_mod m (succ n))⁻¹,
--       rewrite [mul.comm]
    end end
    abstract begin
      intro x, exact sorry
-- cases x with m k,
--       cases k with k H,
--       apply prod_eq: esimp [str_of_nat],
--       { rewrite [add.comm, add_mul_div_self_left _ _ (!zero_lt_succ),
--                  div_eq_zero_of_lt H, zero_add]},
--       { apply eq_of_veq, esimp [mk_mod],
--         rewrite [add.comm, add_mul_mod_self_left, mod_eq_of_lt H]}
    end end
  /-
    note: in the following theorem the (n+1) case is 6 times the same,
    so maybe this can be simplified
  -/
  definition loop_spaces2_pequiv' : Π(n : ℕ) (x : fin (nat.succ 2)),
    loop_spaces f (nat_of_str (n, x)) ≃* loop_spaces2 (n, x)
  |  0    (fin.mk 0 H)     := by reflexivity
  |  0    (fin.mk 1 H)     := by reflexivity
  |  0    (fin.mk 2 H)     := by reflexivity
  |  0    (fin.mk 3 H)     := by reflexivity
  |  0    (fin.mk 4 H)     := by reflexivity
  |  0    (fin.mk 5 H)     := by reflexivity
  | (n+1) (fin.mk 0 H)     :=
    begin
      -- uncomment the next two lines to have prettier subgoals
      -- esimp, replace (succ 2 * (n + 1) + 0) with (6*n+3+3),
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
  | n     (fin.mk (k+3) H) := begin exfalso, apply lt_le_antisymm H, apply le_add_left end

  definition loop_spaces2_pequiv : Π(x : +3ℕ),
    loop_spaces f (nat_of_str x) ≃* loop_spaces2 x
  | (n, x) := loop_spaces2_pequiv' n x

  /- all cases where n>0 are basically the same -/
  definition loop_spaces_fun2_phomotopy (x : +3ℕ) :
    loop_spaces2_pequiv x ∘* loop_spaces_fun f (nat_of_str x) ~*
      (loop_spaces_fun2 x ∘* loop_spaces2_pequiv (S x))
    ∘* pcast (ap (loop_spaces f) (nat_of_str_6S x)) :=
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

  definition type_LES_of_loop_spaces2 [constructor] : type_chain_complex +3ℕ :=
  transfer_type_chain_complex2
    (type_LES_of_loop_spaces f)
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

  definition LES_of_loop_spaces2 [constructor] : chain_complex +3ℕ :=
  trunc_chain_complex type_LES_of_loop_spaces2

end chain_complex
