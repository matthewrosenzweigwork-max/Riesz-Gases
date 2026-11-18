import HRS.Main.T25PAux3

/-!
# T25P, part 4: the `L¹` bound for the weighted series `Ψ_a` of mode forcings (clause 1 of the remainder)

`Ψ_a(ω) = ∑_j ⟨j⟩^{-m} ∫_0^{a+T} w_a(r) |y_j(r,ω)| dr` with `y_j(r) = √N F_N^{h_{∇e_j}}(X_r, ρ_r)` and `w_a(r) = e^{-c(a-r)_+}`.
Pair input (`t25_pair_input`, horizon-free) gives `E|y_j(r)| ≤ c₀ ⟨j⟩² B_N/√N` for all `r ≤ a+T`; `∫_0^{a+T} w_a ≤ 1/c + T`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- The window weight `w_a(r) = e^{-c (a-r)_+}`. -/
def t25p_w (cr a r : ℝ) : ℝ := Real.exp (-cr * max (a - r) 0)

theorem t25p_w_pos (cr a r : ℝ) : 0 < t25p_w cr a r := Real.exp_pos _

theorem t25p_w_cont (cr a : ℝ) : Continuous (t25p_w cr a) := by
  unfold t25p_w
  exact Real.continuous_exp.comp (continuous_const.mul ((continuous_const.sub continuous_id).max continuous_const))

theorem t25p_w_le_one {cr : ℝ} (hcr : 0 ≤ cr) (a r : ℝ) : t25p_w cr a r ≤ 1 := by
  unfold t25p_w
  rw [Real.exp_le_one_iff]
  have : 0 ≤ max (a - r) 0 := le_max_right _ _
  nlinarith

/-- The mode forcings `y_j(r) = √N F_N^{h_{∇e_j}}(X_r, ρ_r)`. -/
def t25p_y (d : ℕ) (s : ℝ) (ρ : ℝ → Torus d → ℝ) {Ω : Type*} {N : ℕ} (X : ℝ≥0 → Ω → Config d N)
    (j : NonzeroLattice d) (r : ℝ) (ω : Ω) : ℝ :=
  Real.sqrt N * modulatedEnergy
    (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (X r.toNNReal ω)
    (withDensityReal (ρ r))

/-- The weighted series `Ψ_a`. -/
def t25p_Psi (d : ℕ) (s : ℝ) (ρ : ℝ → Torus d → ℝ) (m cr a T : ℝ) {Ω : Type*} {N : ℕ}
    (X : ℝ≥0 → Ω → Config d N) (ω : Ω) : ℝ≥0∞ :=
  ∑' j : NonzeroLattice d, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
    ∫⁻ r in Set.Ioc 0 (a + T), ENNReal.ofReal (t25p_w cr a r) * ‖t25p_y d s ρ X j r ω‖ₑ

/-! ### The integral of the weight -/

theorem t25p_w_lintegral_le {cr : ℝ} (hcr : 0 < cr) {a : ℝ} (ha : 0 ≤ a) {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ r in Set.Ioc 0 (a + T), ENNReal.ofReal (t25p_w cr a r) ≤ ENNReal.ofReal (1 / cr + T) := by
  have hcont := t25p_w_cont cr a
  have hnn : ∀ r, 0 ≤ t25p_w cr a r := fun r => (t25p_w_pos cr a r).le
  have hint : IntegrableOn (t25p_w cr a) (Set.Ioc 0 (a + T)) :=
    (hcont.integrableOn_Icc (a := 0) (b := a + T)).mono_set Set.Ioc_subset_Icc_self
  rw [← ofReal_integral_eq_lintegral_ofReal hint (Filter.Eventually.of_forall hnn)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hS : 0 ≤ a + T := by linarith
  rw [← intervalIntegral.integral_of_le hS]
  have hi1 : IntervalIntegrable (t25p_w cr a) volume 0 a := hcont.intervalIntegrable _ _
  have hi2 : IntervalIntegrable (t25p_w cr a) volume a (a + T) := hcont.intervalIntegrable _ _
  rw [← intervalIntegral.integral_add_adjacent_intervals hi1 hi2]
  have h2 : ∫ r in a..(a + T), t25p_w cr a r = T := by
    have : ∀ r ∈ Set.uIcc a (a + T), t25p_w cr a r = 1 := by
      intro r hr
      rw [Set.uIcc_of_le (by linarith)] at hr
      unfold t25p_w
      rw [max_eq_right (by linarith [hr.1]), mul_zero, Real.exp_zero]
    rw [intervalIntegral.integral_congr this]
    simp
  have h1 : ∫ r in (0 : ℝ)..a, t25p_w cr a r ≤ 1 / cr := by
    have e : ∀ r ∈ Set.uIcc (0 : ℝ) a, t25p_w cr a r = Real.exp (-cr * (a - r)) := by
      intro r hr
      rw [Set.uIcc_of_le ha] at hr
      unfold t25p_w
      rw [max_eq_left (by linarith [hr.2])]
    rw [intervalIntegral.integral_congr e]
    have hderiv : ∀ r ∈ Set.uIcc (0 : ℝ) a,
        HasDerivAt (fun r => Real.exp (-cr * (a - r)) / cr) (Real.exp (-cr * (a - r))) r := by
      intro r _
      have h1 : HasDerivAt (fun r : ℝ => -cr * (a - r)) cr r := by
        have := ((hasDerivAt_id r).const_sub a).const_mul (-cr)
        simpa using this
      have := (h1.exp).div_const cr
      convert this using 1
      field_simp
    rw [intervalIntegral.integral_eq_sub_of_hasDerivAt hderiv
      ((Real.continuous_exp.comp (continuous_const.mul (continuous_const.sub continuous_id))).intervalIntegrable _ _)]
    have : Real.exp (-cr * (a - a)) / cr - Real.exp (-cr * (a - 0)) / cr ≤ 1 / cr := by
      have e0 : Real.exp (-cr * (a - a)) = 1 := by simp
      rw [e0]
      have : 0 ≤ Real.exp (-cr * (a - 0)) / cr := by positivity
      linarith
    exact this
  linarith

end HRS.T25P
