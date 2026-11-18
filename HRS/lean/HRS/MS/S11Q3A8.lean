import HRS.MS.S11Q3A7

/-!
# S11.3 / S11.4 (worker S11Q3), A8: the integrand `W_t(X)` of the normalizer, its time derivative, and the majorant `N ∏ h(X_a)`
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S11Q3

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.S113BD

variable {d : ℕ} {s : ℝ}

/-- One-particle majorant. -/
def s11q3_h (a0 a1 B c k0 k1 : ℝ) (x : Euc d) : ℝ :=
  Real.exp (a0 + a1 * ‖x‖) * (B * Real.exp (-c * ‖x‖ ^ 2)) * (1 + (k0 + k1 * ‖x‖))

theorem s11q3_h_integrable (hd : 1 ≤ d) {c : ℝ} (hc : 0 < c) {a0 a1 B k0 k1 : ℝ} (hB : 0 ≤ B) (hk0 : 0 ≤ k0)
    (hk1 : 0 ≤ k1) : Integrable (s11q3_h (d := d) a0 a1 B c k0 k1) := by
  set K : ℝ := B * Real.exp (a0 + a1 ^ 2 / (2 * c)) with hK
  have hK0 : 0 ≤ K := by positivity
  refine Integrable.mono' (s113x_poly_gauss_integrable hd (c := c / 2) (by positivity) (K * (1 + k0)) (K * k1))
    (by unfold s11q3_h; fun_prop) (Filter.Eventually.of_forall fun x => ?_)
  have hr : 0 ≤ ‖x‖ := norm_nonneg x
  have hpt : Real.exp (a0 + a1 * ‖x‖) * Real.exp (-c * ‖x‖ ^ 2) ≤
      Real.exp (a0 + a1 ^ 2 / (2 * c)) * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by
    rw [← Real.exp_add, ← Real.exp_add]
    apply Real.exp_le_exp.2
    have h2c : 0 < 2 * c := by positivity
    have : a1 * ‖x‖ ≤ a1 ^ 2 / (2 * c) + (c / 2) * ‖x‖ ^ 2 := by
      rw [← sub_nonneg]
      have : a1 ^ 2 / (2 * c) + (c / 2) * ‖x‖ ^ 2 - a1 * ‖x‖ = (c * ‖x‖ - a1) ^ 2 / (2 * c) := by
        field_simp; ring
      rw [this]; positivity
    nlinarith
  unfold s11q3_h
  rw [Real.norm_of_nonneg (by positivity)]
  have hu : 0 ≤ 1 + (k0 + k1 * ‖x‖) := by positivity
  calc Real.exp (a0 + a1 * ‖x‖) * (B * Real.exp (-c * ‖x‖ ^ 2)) * (1 + (k0 + k1 * ‖x‖))
      = B * (Real.exp (a0 + a1 * ‖x‖) * Real.exp (-c * ‖x‖ ^ 2)) * (1 + (k0 + k1 * ‖x‖)) := by ring
    _ ≤ B * (Real.exp (a0 + a1 ^ 2 / (2 * c)) * Real.exp (-(c / 2) * ‖x‖ ^ 2)) * (1 + (k0 + k1 * ‖x‖)) := by
        (gcongr)
    _ = (K * (1 + k0) + K * k1 * ‖x‖) * Real.exp (-(c / 2) * ‖x‖ ^ 2) := by rw [hK]; ring

theorem s11q3_one_add_sum_le_prod {ι : Type*} (S : Finset ι) (u : ι → ℝ) (hu : ∀ i, 0 ≤ u i) :
    1 + ∑ i ∈ S, u i ≤ ∏ i ∈ S, (1 + u i) := by
  classical
  induction S using Finset.induction_on with
  | empty => simp
  | insert j S hj ih =>
    rw [Finset.sum_insert hj, Finset.prod_insert hj]
    have hS : 0 ≤ ∑ i ∈ S, u i := Finset.sum_nonneg fun i _ => hu i
    have := hu j
    nlinarith

section W

variable {ρ D : ℝ → Euc d → ℝ} {c B : ℝ}

def s11q3_E (d : ℕ) (s β : ℝ) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (t : ℝ) (X : EucConfig d N) : ℝ :=
  Real.exp (-β * N * s11q3_F0 d s N X + β * ∑ a, s11q3_Gam d s (ρ t) (X a))

def s11q3_P {N : ℕ} (ρ : ℝ → Euc d → ℝ) (t : ℝ) (X : EucConfig d N) : ℝ := ∏ a, ρ t (X a)

def s11q3_W (d : ℕ) (s β : ℝ) (N : ℕ) (ρ : ℝ → Euc d → ℝ) (t : ℝ) (X : EucConfig d N) : ℝ :=
  s11q3_E d s β N ρ t X * s11q3_P ρ t X

def s11q3_W' (d : ℕ) (s β : ℝ) (N : ℕ) (ρ D : ℝ → Euc d → ℝ) (t : ℝ) (X : EucConfig d N) : ℝ :=
  s11q3_E d s β N ρ t X * (β * ∑ a, s11q3_Gam d s (D t) (X a)) * s11q3_P ρ t X +
    s11q3_E d s β N ρ t X * ∑ a, (∏ j ∈ Finset.univ.erase a, ρ t (X j)) * D t (X a)

theorem s11q3_W_bound (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : s11q3_Reg d ρ D c B) {β : ℝ} (hβ : 0 < β)
    {N : ℕ} (hN : 1 ≤ N) :
    ∃ a0 a1 k0 k1 : ℝ, 0 ≤ k0 ∧ 0 ≤ k1 ∧ ∀ t, 0 ≤ t → ∀ X : EucConfig d N,
      |s11q3_W d s β N ρ t X| ≤ N * ∏ a, s11q3_h a0 a1 B c k0 k1 (X a) ∧
      |s11q3_W' d s β N ρ D t X| ≤ N * ∏ a, s11q3_h a0 a1 B c k0 k1 (X a) := by
  obtain ⟨A0, A1, hA0, hA1, hG⟩ := s11q3_Gam_bound hd hs0 hsd R
  have hB := R.hB
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  set a0 : ℝ := β * B * A0 with ha0
  set a1 : ℝ := β * (1 + B * A1) with ha1
  set k0 : ℝ := β * B * A0 with hk0
  set k1 : ℝ := β * B * A1 with hk1
  have hk0n : 0 ≤ k0 := by positivity
  have hk1n : 0 ≤ k1 := by positivity
  refine ⟨a0, a1, k0, k1, hk0n, hk1n, fun t ht X => ?_⟩
  set b : Euc d → ℝ := fun x => B * Real.exp (-c * ‖x‖ ^ 2) with hb
  have hb0 : ∀ x, 0 ≤ b x := fun x => by positivity
  have hρb : ∀ a, |ρ t (X a)| ≤ b (X a) := fun a => R.g0 t ht (X a)
  have hDb : ∀ a, |D t (X a)| ≤ b (X a) := fun a => R.gD t ht (X a)
  set u : Fin N → ℝ := fun a => k0 + k1 * ‖X a‖ with hu
  have hu0 : ∀ a, 0 ≤ u a := fun a => by positivity
  -- the factor E
  have hE0 : 0 < s11q3_E d s β N ρ t X := Real.exp_pos _
  have hEle : s11q3_E d s β N ρ t X ≤ ∏ a, Real.exp (a0 + a1 * ‖X a‖) := by
    unfold s11q3_E
    rw [← Real.exp_sum]
    apply Real.exp_le_exp.2
    have hF := s11q3_F0_lower hs0 hN X
    have h1 : -β * N * s11q3_F0 d s N X ≤ β * ∑ a, ‖X a‖ := by
      have hNp : (0 : ℝ) < N := by linarith
      have := mul_le_mul_of_nonneg_left (neg_le_neg hF) (mul_nonneg hβ.le hNp.le)
      calc -β * N * s11q3_F0 d s N X = β * N * (-s11q3_F0 d s N X) := by ring
        _ ≤ β * N * ((1 / (N : ℝ)) * ∑ a, ‖X a‖) := by simpa using this
        _ = β * ∑ a, ‖X a‖ := by field_simp
    have h2 : β * ∑ a, s11q3_Gam d s (ρ t) (X a) ≤ ∑ a, β * B * (A0 + A1 * ‖X a‖) := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      calc β * s11q3_Gam d s (ρ t) (X a) ≤ β * (B * (A0 + A1 * ‖X a‖)) :=
            mul_le_mul_of_nonneg_left (le_trans (le_abs_self _) (hG t ht (X a)).1) hβ.le
        _ = _ := by ring
    have h3 : ∑ a, (a0 + a1 * ‖X a‖) = ∑ a, (β * ‖X a‖) + ∑ a, β * B * (A0 + A1 * ‖X a‖) := by
      rw [← Finset.sum_add_distrib]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [ha0, ha1]; ring
    rw [h3]
    have h4 : β * ∑ a, ‖X a‖ = ∑ a, (β * ‖X a‖) := Finset.mul_sum _ _ _
    linarith
  -- the factor P
  have hP : |s11q3_P ρ t X| ≤ ∏ a, b (X a) := by
    unfold s11q3_P
    rw [Finset.abs_prod]
    exact Finset.prod_le_prod₀ (fun a _ => abs_nonneg _) fun a _ => hρb a
  have hprod1 : 1 ≤ ∏ a, (1 + u a) := by
    have := s11q3_one_add_sum_le_prod Finset.univ u hu0
    have hs : 0 ≤ ∑ a, u a := Finset.sum_nonneg fun a _ => hu0 a
    linarith
  have hrew : (∏ a, s11q3_h a0 a1 B c k0 k1 (X a)) =
      (∏ a, Real.exp (a0 + a1 * ‖X a‖)) * (∏ a, b (X a)) * ∏ a, (1 + u a) := by
    unfold s11q3_h
    rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib]
  have hPpos : 0 ≤ ∏ a, b (X a) := Finset.prod_nonneg fun a _ => hb0 _
  have hEpos : 0 ≤ ∏ a, Real.exp (a0 + a1 * ‖X a‖) := Finset.prod_nonneg fun a _ => (Real.exp_pos _).le
  constructor
  · unfold s11q3_W
    rw [abs_mul, abs_of_pos hE0]
    calc s11q3_E d s β N ρ t X * |s11q3_P ρ t X| ≤ (∏ a, Real.exp (a0 + a1 * ‖X a‖)) * ∏ a, b (X a) :=
          mul_le_mul hEle hP (abs_nonneg _) hEpos
      _ = (∏ a, Real.exp (a0 + a1 * ‖X a‖)) * (∏ a, b (X a)) * 1 := by ring
      _ ≤ (∏ a, Real.exp (a0 + a1 * ‖X a‖)) * (∏ a, b (X a)) * ((N : ℝ) * ∏ a, (1 + u a)) := by
          (gcongr)
          nlinarith
      _ = N * ∏ a, s11q3_h a0 a1 B c k0 k1 (X a) := by rw [hrew]; ring
  · unfold s11q3_W'
    have hsum1 : β * ∑ a, |s11q3_Gam d s (D t) (X a)| ≤ ∑ a, u a := by
      rw [Finset.mul_sum]
      refine Finset.sum_le_sum fun a _ => ?_
      calc β * |s11q3_Gam d s (D t) (X a)| ≤ β * (B * (A0 + A1 * ‖X a‖)) :=
            mul_le_mul_of_nonneg_left (hG t ht (X a)).2 hβ.le
        _ = u a := by rw [hu, hk0, hk1]; ring
    have hsum2 : ∑ a, |(∏ j ∈ Finset.univ.erase a, ρ t (X j)) * D t (X a)| ≤ N * ∏ a, b (X a) := by
      calc ∑ a, |(∏ j ∈ Finset.univ.erase a, ρ t (X j)) * D t (X a)|
          ≤ ∑ a : Fin N, ∏ j, b (X j) := by
            refine Finset.sum_le_sum fun a _ => ?_
            rw [abs_mul, Finset.abs_prod]
            calc (∏ j ∈ Finset.univ.erase a, |ρ t (X j)|) * |D t (X a)|
                ≤ (∏ j ∈ Finset.univ.erase a, b (X j)) * b (X a) :=
                  mul_le_mul (Finset.prod_le_prod₀ (fun j _ => abs_nonneg _) fun j _ => hρb j) (hDb a)
                    (abs_nonneg _) (Finset.prod_nonneg fun j _ => hb0 _)
              _ = ∏ j, b (X j) := by
                  rw [mul_comm]; exact Finset.mul_prod_erase Finset.univ (fun j => b (X j)) (Finset.mem_univ a)
        _ = N * ∏ a, b (X a) := by simp
    have hT1 : |s11q3_E d s β N ρ t X * (β * ∑ a, s11q3_Gam d s (D t) (X a)) * s11q3_P ρ t X| ≤
        (∏ a, Real.exp (a0 + a1 * ‖X a‖)) * (∑ a, u a) * ∏ a, b (X a) := by
      rw [abs_mul, abs_mul, abs_of_pos hE0, abs_mul, abs_of_pos hβ]
      have hS : |∑ a, s11q3_Gam d s (D t) (X a)| ≤ ∑ a, |s11q3_Gam d s (D t) (X a)| :=
        Finset.abs_sum_le_sum_abs _ _
      have hS' : β * |∑ a, s11q3_Gam d s (D t) (X a)| ≤ ∑ a, u a :=
        (mul_le_mul_of_nonneg_left hS hβ.le).trans hsum1
      have hsu : 0 ≤ ∑ a, u a := Finset.sum_nonneg fun a _ => hu0 a
      have hmain : s11q3_E d s β N ρ t X * (β * |∑ a, s11q3_Gam d s (D t) (X a)|) * |s11q3_P ρ t X| ≤
          (∏ a, Real.exp (a0 + a1 * ‖X a‖)) * (∑ a, u a) * ∏ a, b (X a) := by
        (gcongr)
      exact hmain
    have hT2 : |s11q3_E d s β N ρ t X * ∑ a, (∏ j ∈ Finset.univ.erase a, ρ t (X j)) * D t (X a)| ≤
        (∏ a, Real.exp (a0 + a1 * ‖X a‖)) * (N * ∏ a, b (X a)) := by
      rw [abs_mul, abs_of_pos hE0]
      have hmain : s11q3_E d s β N ρ t X * |∑ a, (∏ j ∈ Finset.univ.erase a, ρ t (X j)) * D t (X a)| ≤
          (∏ a, Real.exp (a0 + a1 * ‖X a‖)) * (N * ∏ a, b (X a)) := by
        (gcongr)
        exact (Finset.abs_sum_le_sum_abs _ _).trans hsum2
      exact hmain
    have hUN : (∑ a, u a) + N ≤ N * ∏ a, (1 + u a) := by
      have := s11q3_one_add_sum_le_prod Finset.univ u hu0
      have hs : 0 ≤ ∑ a, u a := Finset.sum_nonneg fun a _ => hu0 a
      nlinarith
    refine (abs_add_le _ _).trans ?_
    calc _ ≤ (∏ a, Real.exp (a0 + a1 * ‖X a‖)) * (∑ a, u a) * (∏ a, b (X a)) +
          (∏ a, Real.exp (a0 + a1 * ‖X a‖)) * (N * ∏ a, b (X a)) := add_le_add hT1 hT2
      _ = (∏ a, Real.exp (a0 + a1 * ‖X a‖)) * (∏ a, b (X a)) * ((∑ a, u a) + N) := by ring
      _ ≤ (∏ a, Real.exp (a0 + a1 * ‖X a‖)) * (∏ a, b (X a)) * (N * ∏ a, (1 + u a)) := (by (gcongr))
      _ = N * ∏ a, s11q3_h a0 a1 B c k0 k1 (X a) := by rw [hrew]; ring

end W

end HRS.MS.S11Q3

end
