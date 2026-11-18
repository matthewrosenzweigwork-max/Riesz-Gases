import HRS.MP.SelfSimP4MolC3

/-!
# MPP4MOL stage 5b (4): Fubini swaps and the identity `∫ f a = -∑_k ∫ ∂_k f (θ ∂_k u - B_k)`
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

theorem p4m_coord_abs_le_norm (w : EucConfig d N) (k : Fin N × Fin d) : |w k.1 k.2| ≤ ‖w‖ := by
  have h1 : ‖w k.1 k.2‖ ≤ ‖w k.1‖ := PiLp.norm_apply_le (w k.1) k.2
  have h2 : ‖w k.1‖ ≤ ‖w‖ := norm_le_pi_norm w k.1
  simpa [Real.norm_eq_abs] using h1.trans h2

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

theorem p4m_swap_cs [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν)
    {F : EucConfig d N → ℝ} (hF : Continuous F) (hFs : HasCompactSupport F)
    {φ : EucConfig d N → EucConfig d N → ℝ}
    (hφc : Continuous (fun p : EucConfig d N × EucConfig d N => φ p.1 p.2))
    {A : ℝ} (hφ : ∀ x y, |φ x y| ≤ A * (1 + ‖y‖)) :
    (∫ x, F x * ∫ y, φ x y ∂ν) = ∫ y, (∫ x, F x * φ x y) ∂ν ∧
    Integrable (fun y => ∫ x, F x * φ x y) ν ∧
    Integrable (fun x => F x * ∫ y, φ x y ∂ν) volume := by
  have hint := p4m_prod_integrable_cs hm hF hFs hφc hφ
  have e1 : ∀ x, F x * ∫ y, φ x y ∂ν = ∫ y, F x * φ x y ∂ν := fun x => (integral_const_mul _ _).symm
  refine ⟨?_, hint.integral_prod_right, ?_⟩
  · simp_rw [e1]
    exact integral_integral_swap (f := fun x y => F x * φ x y) hint
  · have := hint.integral_prod_left
    refine this.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [e1]

theorem p4m_gk_cont (v : ℝ) (k : Fin N × Fin d) :
    Continuous (fun p : EucConfig d N × EucConfig d N => p4m_gk v p.2 k p.1) := by
  unfold p4m_gk
  have hw : Continuous (fun p : EucConfig d N × EucConfig d N => p.1 - p.2) := continuous_fst.sub continuous_snd
  exact (continuous_const.mul ((p4m_continuous_gauss v).comp hw)).mul
    ((p4m_continuous_coord k).comp hw)

theorem p4m_gk_bound (hv : 0 < v) (k : Fin N × Fin d) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x y : EucConfig d N, |p4m_gk v y k x| ≤ A * (1 + ‖y‖) := by
  obtain ⟨C2, hC2, hb2⟩ := p4m_gauss_norm_le (d := d) (N := N) hv
  refine ⟨(1 / v) * C2, by positivity, fun x y => ?_⟩
  unfold p4m_gk
  have hG := p4m_gauss_pos (d := d) (N := N) hv (x - y)
  have h1 := p4m_coord_abs_le_norm (x - y) k
  have h2 := hb2 (x - y)
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  rw [abs_mul, abs_mul, abs_neg, abs_of_pos (by positivity : 0 < 1 / v), abs_of_pos hG]
  calc 1 / v * p4Gauss d N v (x - y) * |(x - y) k.1 k.2| ≤ 1 / v * p4Gauss d N v (x - y) * ‖x - y‖ := by gcongr
    _ = 1 / v * (p4Gauss d N v (x - y) * ‖x - y‖) := by ring
    _ ≤ 1 / v * C2 := by gcongr
    _ ≤ 1 / v * C2 * (1 + ‖y‖) := by
        have : 0 ≤ 1 / v * C2 := by positivity
        nlinarith

theorem p4m_hB_cont (v : ℝ) {b : EucConfig d N → EucConfig d N} (hbc : Continuous b) (k : Fin N × Fin d) :
    Continuous (fun p : EucConfig d N × EucConfig d N => p4Gauss d N v (p.1 - p.2) * b p.2 k.1 k.2) := by
  have hw : Continuous (fun p : EucConfig d N × EucConfig d N => p.1 - p.2) := continuous_fst.sub continuous_snd
  exact ((p4m_continuous_gauss v).comp hw).mul ((p4m_continuous_coord k).comp (hbc.comp continuous_snd))

theorem p4m_hB_bound (hv : 0 < v) {b : EucConfig d N → EucConfig d N} {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbg : ∀ y, ‖b y‖ ≤ B + K * ‖y‖) (k : Fin N × Fin d) :
    ∃ A : ℝ, 0 ≤ A ∧ ∀ x y : EucConfig d N, |p4Gauss d N v (x - y) * b y k.1 k.2| ≤ A * (1 + ‖y‖) := by
  obtain ⟨C0, hC0, hb0⟩ := p4m_gauss_poly_bound' (d := d) (N := N) hv 0
  refine ⟨C0 * (B + K), by positivity, fun x y => ?_⟩
  have hG := p4m_gauss_pos (d := d) (N := N) hv (x - y)
  have h0 := hb0 (x - y)
  simp only [pow_zero, one_mul] at h0
  have h1 := p4m_coord_abs_le_norm (b y) k
  have h2 := hbg y
  have hy : 0 ≤ ‖y‖ := norm_nonneg y
  rw [abs_mul, abs_of_pos hG]
  calc p4Gauss d N v (x - y) * |b y k.1 k.2| ≤ C0 * (B + K * ‖y‖) := by
        apply mul_le_mul h0 (h1.trans h2) (abs_nonneg _) hC0
    _ ≤ C0 * ((B + K) * (1 + ‖y‖)) := by gcongr; nlinarith
    _ = _ := by ring

end

end HRS.MP.SelfSimP4Mol
