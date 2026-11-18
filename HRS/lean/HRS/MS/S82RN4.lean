import HRS.MS.S82RN3

/-!
# S8.2 R02 (S82R), N4: the double convolution is `eps`-small relative to the pole
`int q(z-u) q(u-p) dmu(u) <= eps q(z-p) + C_eps`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MS.S82R
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

lemma s82r_log_le {e x : ℝ} (he : 0 < e) (he1 : e ≤ 1) (hx : 0 ≤ x) :
    Real.log (1 + x) ≤ e * x + Real.log (1 / e) := by
  have h1 : 1 + x = (1 / e) * (e + e * x) := by field_simp
  have hpos : 0 < e + e * x := by positivity
  rw [h1, Real.log_mul (by positivity) hpos.ne']
  have h2 : Real.log (e + e * x) ≤ e * x := by
    have : e + e * x ≤ 1 + e * x := by linarith
    have h3 := Real.log_le_log hpos this
    have h4 := Real.log_le_sub_one_of_pos (by positivity : 0 < 1 + e * x)
    linarith
  linarith

theorem s82r_conv2_eps (hd : 2 ≤ d) {q : Euc d → ℝ} (hq : ShortRangePole d q) (M : ℝ) {ε : ℝ}
    (hε : 0 < ε) :
    ∃ Cε : ℝ, 0 ≤ Cε ∧ ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ M) →
      ∀ z p : Euc d, z ≠ p →
        Integrable (fun u => q (z - u) * q (u - p)) (HRS.Whole.withDensityReal ρ) ∧
        ∫ u, q (z - u) * q (u - p) ∂(HRS.Whole.withDensityReal ρ) ≤ ε * q (z - p) + Cε := by
  obtain ⟨C, hC, H⟩ := s82r_conv2 hd hq M
  set e : ℝ := min 1 (ε / (C + 1)) with he
  have he0 : 0 < e := lt_min one_pos (by positivity)
  have he1 : e ≤ 1 := min_le_left _ _
  have hCe : C * e ≤ ε := by
    have : e ≤ ε / (C + 1) := min_le_right _ _
    calc C * e ≤ C * (ε / (C + 1)) := mul_le_mul_of_nonneg_left this hC
      _ ≤ ε := by
        rw [mul_div_assoc', div_le_iff₀ (by positivity)]; nlinarith
  have hlog : 0 ≤ Real.log (1 / e) := Real.log_nonneg (by rw [le_div_iff₀ he0]; linarith)
  refine ⟨C * (1 + Real.log (1 / e)), by positivity, fun ρ hρ hM z p hzp => ?_⟩
  obtain ⟨hint, hbd⟩ := H ρ hρ hM z p hzp
  refine ⟨hint, hbd.trans ?_⟩
  have hq0 : 0 ≤ q (z - p) := hq.nonneg _
  have := s82r_log_le he0 he1 hq0
  nlinarith [mul_le_mul_of_nonneg_left this hC, mul_nonneg hC hq0]

end HRS.MS.S82R

end
