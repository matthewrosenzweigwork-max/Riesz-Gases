import HRS.MS.Fp81S21GaussianMomentsUniform
import HRS.MS.Fp81S21GaussianDChaos

/-!
# Uniform drift moments for the selected retained quadratic field

The weak MomentRep in QuadraticPhysical31Payload bounds the coefficient
second moment by MB₀ = S.Kstar ^ 4 * S.B / 2. Its dual-norm identity is
an additional clause; no norm conversion or replacement field is needed.
The fourth-moment constant is exactly 15 * MB₀ ^ 2, independently of the
possibly different MB in the supplied origin-zero TimeL2Rep.

Binder adjustments: the small-δ threshold is inherited from the moving
operator theorem. The core chart's order and weight are definitionally
2 * p.d + 8 and (p.d : ℝ) + 2, matching GaussianDChaos's payload binders.
All c, K, MD precede the window origin a and every compatible O, MB, UB.
The displayed drift is definitionally gaussian_Dcum at the full horizon.
hB0, supplied by quadraticPhysical31_zero_mass in GaussianFieldsRetained,
remains an input to the physical identification of Dcum, not this bound.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- Uniform fourth moments of the actual weak field selected by the payload. -/
private theorem fp81s21_gaussian_qB_fourth_moments
    {p : Parameters} {δ : ℝ} {R : Trajectory p δ}
    {hμ₀ : IsProbabilityMeasure (r26t3_mu R 0)}
    (D : fp81s21_gaussian_source_retained_data p R hμ₀)
    {Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4)}
    {E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)}
    {ε : ℕ → ℝ} (S : fp81s21_QuadraticPhysical31 p R Es E ε) :
    ∀ u, 0 ≤ u → MemLp (S.qe D.G0 u) 4 D.G0.P ∧
      (∫ ω, ‖S.qe D.G0 u ω‖ ^ 4 ∂D.G0.P) ≤
        15 * (S.Kstar ^ 4 * S.B / 2) ^ 2 := by
  have he := (S.payload D.G0).2.2.2.2.1
  have hc := (fp81s21_gaussian_qB_secondChaos_coords D S).2
  intro u hu
  obtain ⟨h4, hbound⟩ := fp81s21_InQ2_coeff_fourth
    (fp81s21_gaussian_source_measurable_coords_std D).2.2
    (S.qe D.G0 u) (hc u hu).1 (hc u hu).2
  refine ⟨h4, hbound.trans ?_⟩
  exact mul_le_mul_of_nonneg_left
    (pow_le_pow_left₀ (integral_nonneg fun ω => sq_nonneg ‖S.qe D.G0 u ω‖)
      (he.2 u hu).2.1 2) (by norm_num)

/-- Radius-free third moments for the selected quadratic physical source,
using every compatible moving operator and its supplied full history. -/
theorem fp81s21_gaussian_D_moments_uniform_physical (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∀ {hμ₀ : IsProbabilityMeasure (r26t3_mu R 0)}
      (D : fp81s21_gaussian_source_retained_data p R hμ₀)
      {Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4)}
      {E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)}
      {ε : ℕ → ℝ} (S : fp81s21_QuadraticPhysical31 p R Es E ε),
    ∃ c K MD : ℝ, 0 < c ∧ 0 ≤ K ∧ 0 ≤ MD ∧
    ∀ a : ℝ, ∀ ha : 0 ≤ a,
      Nonempty (r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K) ∧
      ∀ O : r26t6_IntervalOperators E (r26t3_coeff R) p.T a c K,
      ∀ MB : ℝ, ∀ UB : D.G0.Ω → Lp r26t6_Coeff 2
        (volume.restrict (Icc (0 : ℝ) (a + p.T))),
      fp81s21_TimeL2Rep D.G0.P (S.qe D.G0) MB 0 (a + p.T) UB →
      let V := fun ω => O.drift 0 (a + p.T)
        (fp81s21_timeL2L1 (a + p.T) (add_nonneg ha p.hT.le) (UB ω))
      MemLp V 3 D.G0.P ∧ (∫ ω, ‖V ω‖ ^ 3 ∂D.G0.P) ≤ MD := by
  obtain ⟨δ0, hδ0, hhalf, hbound⟩ :=
    fp81s21_uniform_gaussian_D_moments_of_fourth p
  refine ⟨δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R hμ₀ D Es E ε S
  obtain ⟨c, K, MD, hc, hK, hMD, hwindow⟩ :=
    hbound δ hδ hδle R E (15 * (S.Kstar ^ 4 * S.B / 2) ^ 2) (by positivity)
  refine ⟨c, K, MD, hc, hK, hMD, ?_⟩
  intro a ha
  refine ⟨(hwindow a ha).1, ?_⟩
  intro O MB UB hUB
  exact (hwindow a ha).2 O D.G0 (S.qe D.G0)
    (fp81s21_gaussian_qB_secondChaos_coords D S).1
    (fp81s21_gaussian_qB_fourth_moments D S) MB UB hUB

#print axioms fp81s21_gaussian_qB_fourth_moments
#print axioms fp81s21_gaussian_D_moments_uniform_physical
end HRS.Fp81.S21
end
