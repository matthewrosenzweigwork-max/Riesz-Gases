import HRS.MP.SelfSimP4MolD2

/-!
# MPP4MOL stage 5c (3): the commutator `r_k = B_k - u b_k` and the pointwise Young inequality
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

theorem p4m_integrable_hB [IsProbabilityMeasure ν] (hv : 0 < v) (hm : Integrable p4m_q ν)
    {b : EucConfig d N → EucConfig d N} (hbc : Continuous b) {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbg : ∀ y, ‖b y‖ ≤ B + K * ‖y‖) (k : Fin N × Fin d) (x : EucConfig d N) :
    Integrable (fun y => p4Gauss d N v (x - y) * b y k.1 k.2) ν := by
  obtain ⟨A, hA0, hA⟩ := p4m_hB_bound hv hB hK hbg k
  exact p4m_integrable_lin hm ((p4m_hB_cont v hbc k).comp
    (Continuous.prodMk continuous_const continuous_id)).aestronglyMeasurable (fun y => hA x y)

theorem p4m_rk_eq [IsProbabilityMeasure ν] (hv : 0 < v) (hm : Integrable p4m_q ν)
    {b : EucConfig d N → EucConfig d N} (hbc : Continuous b) {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbg : ∀ y, ‖b y‖ ≤ B + K * ‖y‖) (k : Fin N × Fin d) (x : EucConfig d N) :
    ∫ y, p4Gauss d N v (x - y) * (b y k.1 k.2 - b x k.1 k.2) ∂ν =
      p4m_B v ν b k x - p4Mol v ν x * b x k.1 k.2 := by
  have h1 := p4m_integrable_hB hv hm hbc hB hK hbg k x
  have h2 : Integrable (fun y => p4Gauss d N v (x - y) * b x k.1 k.2) ν :=
    (p4m_integrable_gauss_sub hv ν x).mul_const _
  have e : ∀ y, p4Gauss d N v (x - y) * (b y k.1 k.2 - b x k.1 k.2) =
      p4Gauss d N v (x - y) * b y k.1 k.2 - p4Gauss d N v (x - y) * b x k.1 k.2 := fun y => by ring
  simp_rw [e]
  rw [integral_sub h1 h2, integral_mul_const]
  rfl

theorem p4m_J_eq [IsProbabilityMeasure ν] (hv : 0 < v) (hm : Integrable p4m_q ν) {θ : ℝ} (hθ : 0 < θ)
    (b : EucConfig d N → EucConfig d N) (k : Fin N × Fin d) (x : EucConfig d N) :
    θ * p4m_gu v ν k x - p4m_B v ν b k x =
      θ * p4Mol v ν x * p4m_ell v θ ν b k x - (p4m_B v ν b k x - p4Mol v ν x * b x k.1 k.2) := by
  have hu := (p4m_mol_pos hv hm x).ne'
  unfold p4m_ell
  field_simp
  ring

theorem p4m_Tint_integrable [IsProbabilityMeasure ν] (hv : 0 < v) {b : EucConfig d N → EucConfig d N}
    {Kl : ℝ≥0} (hbl : LipschitzWith Kl b) (x : EucConfig d N) :
    Integrable (fun y => p4Gauss d N v (x - y) * ∑ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) ^ 2) ν := by
  obtain ⟨C1, hC1, hb1⟩ := p4m_gauss_poly_bound' (d := d) (N := N) hv 1
  have hbc : Continuous b := hbl.continuous
  have hKn : (0 : ℝ) ≤ N * (Kl : ℝ) ^ 2 := by positivity
  have hcs : Continuous (fun y : EucConfig d N => p4Gauss d N v (x - y) *
      ∑ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) ^ 2) := by
    refine ((p4m_continuous_gauss v).comp (continuous_const.sub continuous_id)).mul ?_
    refine continuous_finset_sum _ fun k _ => ?_
    exact (((p4m_continuous_coord k).comp hbc).sub continuous_const).pow 2
  refine Integrable.of_bound hcs.aestronglyMeasurable (N * (Kl : ℝ) ^ 2 * C1) (Filter.Eventually.of_forall fun y => ?_)
  have hnn : 0 ≤ p4Gauss d N v (x - y) * ∑ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) ^ 2 :=
    mul_nonneg (p4m_gauss_pos hv _).le (Finset.sum_nonneg fun k _ => sq_nonneg _)
  rw [Real.norm_of_nonneg hnn]
  have h := p4m_sum_sq_le hbl x y
  have hG := p4m_gauss_pos (d := d) (N := N) hv (x - y)
  have := hb1 (x - y)
  simp only [pow_one] at this
  nlinarith [mul_le_mul_of_nonneg_left h hG.le, mul_le_mul_of_nonneg_left this hKn]

/-- The pointwise Young inequality for the commutator term. -/
theorem p4m_young_pt [IsProbabilityMeasure ν] (hv : 0 < v) (hm : Integrable p4m_q ν) {θ δ : ℝ} (hθ : 0 < θ)
    (hδ : 0 < δ) {b : EucConfig d N → EucConfig d N} {Kl : ℝ≥0} (hbl : LipschitzWith Kl b)
    {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K) (hbg : ∀ y, ‖b y‖ ≤ B + K * ‖y‖) (x : EucConfig d N) :
    ∑ k : Fin N × Fin d, (p4m_B v ν b k x - p4Mol v ν x * b x k.1 k.2) * p4m_ell v θ ν b k x ≤
      θ * δ * (p4Mol v ν x * ∑ k : Fin N × Fin d, p4m_ell v θ ν b k x ^ 2) +
        p4m_T v ν b x / (4 * θ * δ) := by
  have hbc : Continuous b := hbl.continuous
  set ℓ : Fin N × Fin d → ℝ := fun k => p4m_ell v θ ν b k x with hℓ
  have hG := p4m_integrable_gauss_sub hv ν x (d := d) (N := N)
  have hc : ∀ k : Fin N × Fin d, Integrable (fun y => p4Gauss d N v (x - y) * (b y k.1 k.2 - b x k.1 k.2)) ν := by
    intro k
    have h1 := p4m_integrable_hB hv hm hbc hB hK hbg k x
    have h2 : Integrable (fun y => p4Gauss d N v (x - y) * b x k.1 k.2) ν := hG.mul_const _
    refine (h1.sub h2).congr (Filter.Eventually.of_forall fun y => ?_)
    simp only [Pi.sub_apply]; ring
  have e1 : ∑ k : Fin N × Fin d, (p4m_B v ν b k x - p4Mol v ν x * b x k.1 k.2) * ℓ k =
      ∫ y, ∑ k : Fin N × Fin d, p4Gauss d N v (x - y) * (b y k.1 k.2 - b x k.1 k.2) * ℓ k ∂ν := by
    rw [integral_finset_sum _ fun k _ => (hc k).mul_const _]
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [← p4m_rk_eq hv hm hbc hB hK hbg k x, ← integral_mul_const]
  have hT := p4m_Tint_integrable hv hbl x (ν := ν)
  have e2 : θ * δ * (p4Mol v ν x * ∑ k : Fin N × Fin d, ℓ k ^ 2) + p4m_T v ν b x / (4 * θ * δ) =
      ∫ y, (p4Gauss d N v (x - y) * (θ * δ * ∑ k : Fin N × Fin d, ℓ k ^ 2) +
        (p4Gauss d N v (x - y) * ∑ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) ^ 2) / (4 * θ * δ)) ∂ν := by
    rw [integral_add (hG.mul_const _) (hT.div_const _), integral_mul_const, integral_div]
    unfold p4m_T p4Mol
    ring
  rw [e1, e2]
  refine integral_mono ?_ ?_ ?_
  · exact integrable_finset_sum _ fun k _ => (hc k).mul_const _
  · exact (hG.mul_const _).add (hT.div_const _)
  · intro y
    simp only
    have hGy := (p4m_gauss_pos (d := d) (N := N) hv (x - y)).le
    have hpt : ∀ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) * ℓ k ≤
        θ * δ * ℓ k ^ 2 + (b y k.1 k.2 - b x k.1 k.2) ^ 2 / (4 * θ * δ) := by
      intro k
      have hp : 0 < θ * δ := mul_pos hθ hδ
      have h4 : 0 < 4 * θ * δ := by positivity
      have : θ * δ * ℓ k ^ 2 + (b y k.1 k.2 - b x k.1 k.2) ^ 2 / (4 * θ * δ) -
          (b y k.1 k.2 - b x k.1 k.2) * ℓ k =
          θ * δ * (ℓ k - (b y k.1 k.2 - b x k.1 k.2) / (2 * θ * δ)) ^ 2 := by
        field_simp
        ring
      nlinarith [mul_nonneg hp.le (sq_nonneg (ℓ k - (b y k.1 k.2 - b x k.1 k.2) / (2 * θ * δ)))]
    have hsum := Finset.sum_le_sum fun k (_ : k ∈ Finset.univ) => hpt k
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.sum_div] at hsum
    have h2 := mul_le_mul_of_nonneg_left hsum hGy
    have e3 : ∑ k : Fin N × Fin d, p4Gauss d N v (x - y) * (b y k.1 k.2 - b x k.1 k.2) * ℓ k =
        p4Gauss d N v (x - y) * ∑ k : Fin N × Fin d, (b y k.1 k.2 - b x k.1 k.2) * ℓ k := by
      rw [Finset.mul_sum]
      exact Finset.sum_congr rfl fun k _ => by ring
    rw [e3]
    refine h2.trans (le_of_eq ?_)
    ring

end

end HRS.MP.SelfSimP4Mol
