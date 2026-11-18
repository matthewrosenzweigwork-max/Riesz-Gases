import HRS.MS.SpecAux54

/-!
# S8R: expected relative quadratic form of the covariance entries (S8.7, packet C4)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_entry_sum_bound`: for the canonical Gibbs law `Q`, with
`Δ_{ij}(X) = (2/β) e^{-τ(om_i+om_j)/2} (μ_N(∇e_i·∇e_j) - μ(∇e_i·∇e_j))` and `dv_l = 2 β⁻¹ om_l e^{-τ om_l}`,

`E_Q ∑_{ij} Δ_{ij}² / (dv_i + dv_j) ≤ C4⁴/(β om_0) (C_s/N + C_s² δ_N²) (∑_l e^{-(τ/2-2t₀) om_l})²`,

using the `L⁴` bounds `‖∇e_l‖_{L⁴(μ)} ≤ C4 e^{t₀ om_l}`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal RealInnerProductSpace ContDiff

namespace HRS.MS.Spec

open HRS.Whole
open HRS (Euc)

variable {d : ℕ}

theorem s8p_dv_add_ge {β : ℝ} (hβ : 0 < β) {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) (hmono : Monotone om)
    (τ : ℝ) (i j : ℕ) :
    4 * β⁻¹ * om 0 * Real.exp (-(τ * (om i + om j)) / 2) ≤ s8p_dv β om τ i + s8p_dv β om τ j := by
  unfold s8p_dv
  set x := Real.exp (-(τ * om i) / 2) with hx
  set y := Real.exp (-(τ * om j) / 2) with hy
  have hx0 : 0 < x := Real.exp_pos _
  have hy0 : 0 < y := Real.exp_pos _
  have hxy : Real.exp (-(τ * (om i + om j)) / 2) = x * y := by
    rw [hx, hy, ← Real.exp_add]; congr 1; ring
  have hx2 : Real.exp (-τ * om i) = x * x := by
    rw [hx, ← Real.exp_add]; congr 1; ring
  have hy2 : Real.exp (-τ * om j) = y * y := by
    rw [hy, ← Real.exp_add]; congr 1; ring
  rw [hxy, hx2, hy2]
  have h0 : 0 < om 0 := hom 0
  have hi : om 0 ≤ om i := hmono (Nat.zero_le i)
  have hj : om 0 ≤ om j := hmono (Nat.zero_le j)
  have hb : 0 < β⁻¹ := inv_pos.2 hβ
  have e1 : 2 * β⁻¹ * om 0 * (x * x) ≤ 2 * β⁻¹ * om i * (x * x) := by
    gcongr
  have e2 : 2 * β⁻¹ * om 0 * (y * y) ≤ 2 * β⁻¹ * om j * (y * y) := by
    gcongr
  nlinarith [sq_nonneg (x - y), mul_pos hb h0]

theorem s8p_term_bound {N : ℕ} (hN : 2 ≤ N) {s a β Cs : ℝ} (hCs : 0 ≤ Cs)
    (hS : S45.S45Static d s a β Cs N) [IsProbabilityMeasure (thermalMeasure d s a β)]
    (hβ : 0 < β) {om : ℕ → ℝ} (hom : ∀ l, 0 < om l) (hmono : Monotone om) {τ : ℝ} (hτ : 0 < τ)
    {t₀ C4 : ℝ} (hC4 : 0 ≤ C4) (e : ℕ → Euc d → ℝ) (he : ∀ l, ContDiff ℝ ∞ (e l))
    (hgrad : ∀ i j, ∫ x, s8p_f e i j x ∂(thermalMeasure d s a β) = if i = j then om i else 0)
    (hL4 : ∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 (thermalMeasure d s a β) ≤
      ENNReal.ofReal (C4 * Real.exp (t₀ * om l))) (p : ℕ × ℕ) :
    ∫⁻ X, ENNReal.ofReal (((2 / β) * Real.exp (-(τ * (om p.1 + om p.2)) / 2) *
        (linStat (s8p_f e p.1 p.2) X - ∫ x, s8p_f e p.1 p.2 x ∂(thermalMeasure d s a β))) ^ 2 /
        (s8p_dv β om τ p.1 + s8p_dv β om τ p.2)) ∂(s8p_QN d s a β N) ≤
      ENNReal.ofReal (C4 ^ 4 / (β * om 0) * (Cs / N + Cs ^ 2 * HRS.deltaN d s N ^ 2) *
        Real.exp (-(τ / 2 - 2 * t₀) * (om p.1 + om p.2))) := by
  obtain ⟨i, j⟩ := p
  simp only
  set μ := thermalMeasure d s a β with hμ
  set w := Real.exp (-(τ * (om i + om j)) / 2) with hw
  have hw0 : 0 < w := Real.exp_pos _
  set D := s8p_dv β om τ i + s8p_dv β om τ j with hD
  have hDpos : 0 < D := add_pos (s8p_dv_pos hβ hom τ i) (s8p_dv_pos hβ hom τ j)
  have hDge := s8p_dv_add_ge hβ hom hmono τ i j
  obtain ⟨hfL2, hfB⟩ := s8p_f_L2 (μ := μ) he hC4 hL4 i j
  have hfm : Measurable (s8p_f e i j) := (s8p_continuous_f he i j).measurable
  have hmom := s8p_linStat_moment hN hCs hS (s8p_f e i j) hfm hfL2
  set cN := Cs / N + Cs ^ 2 * HRS.deltaN d s N ^ 2 with hcN
  have hcN0 : 0 ≤ cN := by
    have : (0 : ℝ) ≤ Cs / N := by positivity
    positivity
  set F2 := ∫ x, s8p_f e i j x ^ 2 ∂μ with hF2
  have hF20 : 0 ≤ F2 := integral_nonneg fun x => sq_nonneg _
  -- factor the constant
  have hfac : ∀ X : EucConfig d N, ENNReal.ofReal (((2 / β) * w *
        (linStat (s8p_f e i j) X - ∫ x, s8p_f e i j x ∂μ)) ^ 2 / D) =
      ENNReal.ofReal ((2 / β * w) ^ 2 / D) *
        ENNReal.ofReal ((linStat (s8p_f e i j) X - ∫ x, s8p_f e i j x ∂μ) ^ 2) := by
    intro X
    rw [← ENNReal.ofReal_mul (by positivity)]
    congr 1
    ring
  simp_rw [hfac]
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  refine (mul_le_mul_right hmom _).trans ?_
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- the real estimate
  set K := C4 ^ 4 / (β * om 0) with hK
  have h0 : 0 < om 0 := hom 0
  have hB2 : F2 ≤ C4 ^ 4 * Real.exp (2 * t₀ * (om i + om j)) := by
    refine hfB.trans (le_of_eq ?_)
    have e1 : Real.exp (2 * t₀ * (om i + om j)) = (Real.exp (t₀ * om i) * Real.exp (t₀ * om j)) ^ 2 := by
      rw [← Real.exp_add, ← Real.exp_nat_mul]; congr 1; push_cast; ring
    rw [e1]; ring
  have hexp : w * Real.exp (2 * t₀ * (om i + om j)) =
      Real.exp (-(τ / 2 - 2 * t₀) * (om i + om j)) := by
    rw [hw, ← Real.exp_add]; congr 1; ring
  -- `(2/β w)² / D ≤ w / (β om_0)`
  have hq : (2 / β * w) ^ 2 / D ≤ w / (β * om 0) := by
    rw [div_le_div_iff₀ hDpos (by positivity)]
    have : (2 / β * w) ^ 2 * (β * om 0) = 4 * β⁻¹ * om 0 * w * w := by
      field_simp; ring
    rw [this]
    calc 4 * β⁻¹ * om 0 * w * w = (4 * β⁻¹ * om 0 * w) * w := by ring
      _ ≤ D * w := by gcongr
      _ = w * D := mul_comm _ _
  calc (2 / β * w) ^ 2 / D * (cN * F2) ≤ (w / (β * om 0)) * (cN * (C4 ^ 4 * Real.exp (2 * t₀ * (om i + om j)))) := by
        gcongr
    _ = K * cN * (w * Real.exp (2 * t₀ * (om i + om j))) := by
        rw [hK]; field_simp
    _ = K * cN * Real.exp (-(τ / 2 - 2 * t₀) * (om i + om j)) := by rw [hexp]

end HRS.MS.Spec
