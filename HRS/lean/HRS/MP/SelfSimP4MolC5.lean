import HRS.MP.SelfSimP4MolC4

/-!
# MPP4MOL stage 5b (5): the identity `∫ f a = -∑_k ∫ ∂_k f (θ ∂_k u - B_k)`
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

section
variable {v : ℝ} {ν : Measure (EucConfig d N)}

/-- The `x`-integral of `f · ha(·, y)` after two integrations by parts. -/
theorem p4m_ibp_inner (hv : 0 < v) (θ : ℝ) {b : EucConfig d N → EucConfig d N}
    {f : EucConfig d N → ℝ} (hf : ContDiff ℝ 1 f) (hfs : HasCompactSupport f) (y : EucConfig d N) :
    ∫ x, f x * p4m_ha v θ b x y =
      -θ * (∑ k : Fin N × Fin d, ∫ x, fderiv ℝ f x (configBasis d N k) * p4m_gk v y k x) +
        ∑ k : Fin N × Fin d, ∫ x, fderiv ℝ f x (configBasis d N k) *
          (p4Gauss d N v (x - y) * b y k.1 k.2) := by
  have hfc := hf.continuous
  have hint : ∀ g : EucConfig d N → ℝ, Continuous g → Integrable (fun x => f x * g x) volume := fun g hg =>
    (hfc.mul hg).integrable_of_hasCompactSupport hfs.mul_right
  have hG : Continuous (fun x : EucConfig d N => p4Gauss d N v (x - y)) :=
    (p4m_continuous_gauss v).comp (continuous_id.sub continuous_const)
  have hgk : ∀ k, Continuous (p4m_gk v y k) := fun k => (p4m_contDiff_gk (n := 0) v y k).continuous
  have hck : ∀ k : Fin N × Fin d, Continuous (fun x : EucConfig d N =>
      ((x - y) k.1 k.2 ^ 2 / v ^ 2 - 1 / v) * p4Gauss d N v (x - y)) := by
    intro k
    have : Continuous (fun x : EucConfig d N => (x - y) k.1 k.2) :=
      (p4m_continuous_coord k).comp (continuous_id.sub continuous_const)
    exact ((this.pow 2).div_const _ |>.sub continuous_const).mul hG
  have e : ∀ x, f x * p4m_ha v θ b x y = ∑ k : Fin N × Fin d,
      (θ * (f x * (((x - y) k.1 k.2 ^ 2 / v ^ 2 - 1 / v) * p4Gauss d N v (x - y))) -
        b y k.1 k.2 * (f x * p4m_gk v y k x)) := by
    intro x
    rw [p4m_ha_decomp]
    simp only [Finset.mul_sum, ← Finset.sum_sub_distrib]
    exact Finset.sum_congr rfl fun k _ => by ring
  simp_rw [e]
  have hIk : ∀ k : Fin N × Fin d, Integrable (fun x : EucConfig d N =>
      θ * (f x * (((x - y) k.1 k.2 ^ 2 / v ^ 2 - 1 / v) * p4Gauss d N v (x - y))) -
        b y k.1 k.2 * (f x * p4m_gk v y k x)) volume := fun k =>
    ((hint _ (hck k)).const_mul θ).sub ((hint _ (hgk k)).const_mul _)
  rw [integral_finset_sum _ fun k _ => hIk k]
  have hk : ∀ k : Fin N × Fin d,
      ∫ x, (θ * (f x * (((x - y) k.1 k.2 ^ 2 / v ^ 2 - 1 / v) * p4Gauss d N v (x - y))) -
        b y k.1 k.2 * (f x * p4m_gk v y k x)) =
      -θ * (∫ x, fderiv ℝ f x (configBasis d N k) * p4m_gk v y k x) +
        ∫ x, fderiv ℝ f x (configBasis d N k) * (p4Gauss d N v (x - y) * b y k.1 k.2) := by
    intro k
    rw [integral_sub ((hint _ (hck k)).const_mul θ) ((hint _ (hgk k)).const_mul _),
      integral_const_mul, integral_const_mul, p4m_ibp_gauss2 hv hf hfs y k, p4m_ibp_gauss1 hv hf hfs y k]
    have h3 : ∫ x, fderiv ℝ f x (configBasis d N k) * (p4Gauss d N v (x - y) * b y k.1 k.2) =
        b y k.1 k.2 * ∫ x, fderiv ℝ f x (configBasis d N k) * p4Gauss d N v (x - y) := by
      rw [← integral_const_mul]
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; ring
    rw [h3]
    ring
  simp_rw [hk]
  rw [Finset.sum_add_distrib, ← Finset.mul_sum]

theorem p4m_swap_gk (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν)
    {f : EucConfig d N → ℝ} (hf : ContDiff ℝ 1 f) (hfs : HasCompactSupport f) (k : Fin N × Fin d) :
    (∫ x, fderiv ℝ f x (configBasis d N k) * ∫ y, p4m_gk v y k x ∂ν) =
        ∫ y, (∫ x, fderiv ℝ f x (configBasis d N k) * p4m_gk v y k x) ∂ν ∧
      Integrable (fun y => ∫ x, fderiv ℝ f x (configBasis d N k) * p4m_gk v y k x) ν ∧
      Integrable (fun x => fderiv ℝ f x (configBasis d N k) * ∫ y, p4m_gk v y k x ∂ν) volume := by
  obtain ⟨Ak, hAk0, hAk⟩ := p4m_gk_bound hv (d := d) (N := N) k
  exact p4m_swap_cs hm (p4m_cont_deriv_coord hf k) (p4m_cs_deriv_coord hfs k)
    (φ := fun x y => p4m_gk v y k x) (p4m_gk_cont v k) hAk

theorem p4m_swap_hB (hv : 0 < v) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν)
    {b : EucConfig d N → EucConfig d N} (hbc : Continuous b) {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbg : ∀ y, ‖b y‖ ≤ B + K * ‖y‖)
    {f : EucConfig d N → ℝ} (hf : ContDiff ℝ 1 f) (hfs : HasCompactSupport f) (k : Fin N × Fin d) :
    (∫ x, fderiv ℝ f x (configBasis d N k) * ∫ y, p4Gauss d N v (x - y) * b y k.1 k.2 ∂ν) =
        ∫ y, (∫ x, fderiv ℝ f x (configBasis d N k) * (p4Gauss d N v (x - y) * b y k.1 k.2)) ∂ν ∧
      Integrable (fun y => ∫ x, fderiv ℝ f x (configBasis d N k) * (p4Gauss d N v (x - y) * b y k.1 k.2)) ν ∧
      Integrable (fun x => fderiv ℝ f x (configBasis d N k) *
        ∫ y, p4Gauss d N v (x - y) * b y k.1 k.2 ∂ν) volume := by
  obtain ⟨Ak, hAk0, hAk⟩ := p4m_hB_bound hv hB hK hbg k
  exact p4m_swap_cs hm (p4m_cont_deriv_coord hf k) (p4m_cs_deriv_coord hfs k)
    (φ := fun x y => p4Gauss d N v (x - y) * b y k.1 k.2) (p4m_hB_cont v hbc k) hAk

/-- **The integration-by-parts identity** `∫ f a = -∑_k ∫ ∂_k f (θ ∂_k u - B_k)`. -/
theorem p4m_ibp_identity (hv : 0 < v) (θ : ℝ) [IsProbabilityMeasure ν] (hm : Integrable p4m_q ν)
    {b : EucConfig d N → EucConfig d N} (hbc : Continuous b) {B K : ℝ} (hB : 0 ≤ B) (hK : 0 ≤ K)
    (hbg : ∀ y, ‖b y‖ ≤ B + K * ‖y‖) {f : EucConfig d N → ℝ} (hf : ContDiff ℝ 1 f)
    (hfs : HasCompactSupport f) :
    ∫ x, f x * p4m_a v θ ν b x =
      -∑ k : Fin N × Fin d, ∫ x, fderiv ℝ f x (configBasis d N k) *
        (θ * p4m_gu v ν k x - p4m_B v ν b k x) := by
  obtain ⟨A, hA0, hA⟩ := p4m_ha_bound hv θ hB hK hbg
  have hfc := hf.continuous
  have s1 := p4m_swap_cs hm hfc hfs (φ := fun x y => p4m_ha v θ b x y) (p4m_ha_cont hbc) hA
  have e1 : ∫ x, f x * p4m_a v θ ν b x = ∫ x, f x * ∫ y, p4m_ha v θ b x y ∂ν := rfl
  rw [e1, s1.1]
  simp_rw [p4m_ibp_inner hv θ hf hfs]
  -- the swaps for the two kinds of terms
  have sg := fun k : Fin N × Fin d => p4m_swap_gk hv hm hf hfs k
  have sb := fun k : Fin N × Fin d => p4m_swap_hB hv hm hbc hB hK hbg hf hfs k
  rw [integral_add ((integrable_finset_sum _ fun k _ => (sg k).2.1).const_mul (-θ))
      (integrable_finset_sum _ fun k _ => (sb k).2.1),
    integral_const_mul, integral_finset_sum _ fun k _ => (sg k).2.1,
    integral_finset_sum _ fun k _ => (sb k).2.1]
  have hk : ∀ k : Fin N × Fin d,
      ∫ x, fderiv ℝ f x (configBasis d N k) * (θ * p4m_gu v ν k x - p4m_B v ν b k x) =
        θ * (∫ y, (∫ x, fderiv ℝ f x (configBasis d N k) * p4m_gk v y k x) ∂ν) -
          ∫ y, (∫ x, fderiv ℝ f x (configBasis d N k) * (p4Gauss d N v (x - y) * b y k.1 k.2)) ∂ν := by
    intro k
    rw [← (sg k).1, ← (sb k).1]
    have h1 := (sg k).2.2
    have h2 := (sb k).2.2
    have eu : ∀ x, p4m_gu v ν k x = ∫ y, p4m_gk v y k x ∂ν := fun x => rfl
    have eB : ∀ x, p4m_B v ν b k x = ∫ y, p4Gauss d N v (x - y) * b y k.1 k.2 ∂ν := fun x => rfl
    simp_rw [eu, eB, mul_sub]
    rw [integral_sub, ← integral_const_mul]
    · congr 1
      refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
      simp only; ring
    · exact (h1.const_mul θ).congr (Filter.Eventually.of_forall fun x => by simp only; ring)
    · exact h2
  simp_rw [hk]
  rw [Finset.sum_sub_distrib, ← Finset.mul_sum]
  ring

end

end HRS.MP.SelfSimP4Mol
