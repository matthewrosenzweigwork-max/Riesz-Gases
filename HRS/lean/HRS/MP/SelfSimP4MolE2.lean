import HRS.MP.SelfSimP4MolE1

/-!
# MPP4MOL stage 5b/5c (6): the abstract data and the joint continuity of the mollified quantities
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

/-- The abstract, time-global data of the mollified dissipation inequality on `[0,T]`. -/
structure P4MolData (θ T : ℝ) (b : ℝ → EucConfig d N → EucConfig d N) (V W : ℝ → EucConfig d N → ℝ)
    (μ : ℝ → Measure (EucConfig d N)) (Kl : ℝ≥0) (B K M CV : ℝ) : Prop where
  prob : ∀ r, IsProbabilityMeasure (μ r)
  hm : ∀ r, Integrable p4m_q (μ r)
  hM : ∀ r, ∫ y, p4m_q y ∂(μ r) ≤ M
  narrow : ∀ g : EucConfig d N → ℝ, Continuous g → (∃ C : ℝ, ∀ y, |g y| ≤ C) →
    Continuous fun r => ∫ y, g y ∂(μ r)
  bc : Continuous (Function.uncurry b)
  bl : ∀ r, LipschitzWith Kl (b r)
  hB : 0 ≤ B
  hK : 0 ≤ K
  bg : ∀ r y, ‖b r y‖ ≤ B + K * ‖y‖
  Vc : Continuous (Function.uncurry V)
  grad : ∀ r x, HasFDerivAt (V r) (-(p4InnerL (b r x))) x
  Vg : ∀ r x, |V r x| ≤ CV * (1 + p4m_q x)
  Wc : Continuous (Function.uncurry W)
  Wd : ∀ r ∈ Set.Ioo (0 : ℝ) T, ∀ x, HasDerivAt (fun s => V s x) (W r x) r
  Wle : ∀ r x, W r x ≤ 0
  fp : ∀ g : EucConfig d N → ℝ, P4Test g → ∀ t ∈ Set.Icc (0 : ℝ) T,
    ∫ x, g x ∂(μ t) = ∫ x, g x ∂(μ 0) + ∫ r in Set.Icc (0 : ℝ) t, ∫ x, p4Gen θ b r g x ∂(μ r)

section
variable {θ T : ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {V W : ℝ → EucConfig d N → ℝ}
  {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B K M CV : ℝ} {v : ℝ}

theorem P4MolData.cont_u (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) :
    Continuous (fun p : ℝ × EucConfig d N => p4Mol v (μ p.1) p.2) := by
  haveI := h.prob
  have hw : Continuous (fun p : ℝ × EucConfig d N × EucConfig d N => p.2.1 - p.2.2) :=
    (continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)
  refine p4m_cont_param (h := fun r x y => p4Gauss d N v (x - y)) h.hm h.hM h.narrow
    ((p4m_continuous_gauss v).comp hw) fun x₀ => ⟨p4m_cst d N v, (p4m_cst_pos hv).le, fun r x _ y => ?_⟩
  rw [abs_of_pos (p4m_gauss_pos hv _)]
  have := p4m_gauss_le hv (x - y)
  have := p4m_cst_pos (d := d) (N := N) hv
  nlinarith [norm_nonneg y]

theorem P4MolData.cont_gu (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (k : Fin N × Fin d) :
    Continuous (fun p : ℝ × EucConfig d N => p4m_gu v (μ p.1) k p.2) := by
  haveI := h.prob
  obtain ⟨A, hA0, hA⟩ := p4m_gk_bound hv (d := d) (N := N) k
  have hc := p4m_gk_cont v k (d := d) (N := N)
  have hc' : Continuous (fun p : ℝ × EucConfig d N × EucConfig d N => p4m_gk v p.2.2 k p.2.1) :=
    hc.comp (Continuous.prodMk (continuous_fst.comp continuous_snd) (continuous_snd.comp continuous_snd))
  exact p4m_cont_param (h := fun r x y => p4m_gk v y k x) h.hm h.hM h.narrow hc'
    fun x₀ => ⟨A, hA0, fun r x _ y => hA x y⟩

theorem P4MolData.cont_B (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (k : Fin N × Fin d) :
    Continuous (fun p : ℝ × EucConfig d N => p4m_B v (μ p.1) (b p.1) k p.2) := by
  haveI := h.prob
  obtain ⟨A, hA0, hA⟩ := p4m_hB_bound_unif hv h.hB h.hK k (d := d) (N := N)
  have hw : Continuous (fun p : ℝ × EucConfig d N × EucConfig d N => p.2.1 - p.2.2) :=
    (continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)
  have hc' : Continuous (fun p : ℝ × EucConfig d N × EucConfig d N =>
      p4Gauss d N v (p.2.1 - p.2.2) * b p.1 p.2.2 k.1 k.2) := by
    refine ((p4m_continuous_gauss v).comp hw).mul ?_
    exact (p4m_continuous_coord k).comp (h.bc.comp (Continuous.prodMk continuous_fst (continuous_snd.comp continuous_snd)))
  exact p4m_cont_param (h := fun r x y => p4Gauss d N v (x - y) * b r y k.1 k.2) h.hm h.hM h.narrow hc'
    fun x₀ => ⟨A, hA0, fun r x _ y => hA (b r) (h.bg r) x y⟩

theorem P4MolData.cont_a (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) :
    Continuous (fun p : ℝ × EucConfig d N => p4m_a v θ (μ p.1) (b p.1) p.2) := by
  haveI := h.prob
  obtain ⟨A, hA0, hA⟩ := p4m_ha_bound_unif hv θ h.hB h.hK (d := d) (N := N)
  have hw : Continuous (fun p : ℝ × EucConfig d N × EucConfig d N => p.2.1 - p.2.2) :=
    (continuous_fst.comp continuous_snd).sub (continuous_snd.comp continuous_snd)
  have hc' : Continuous (fun p : ℝ × EucConfig d N × EucConfig d N => p4m_ha v θ (b p.1) p.2.1 p.2.2) := by
    unfold p4m_ha
    refine ((p4m_continuous_gauss v).comp hw).mul ?_
    refine (continuous_const.mul ((p4m_continuous_q.comp hw).div_const _ |>.sub continuous_const)).add ?_
    refine Continuous.div_const ?_ _
    exact (p4m_continuous_innerL.comp hw).clm_apply
      (h.bc.comp (Continuous.prodMk continuous_fst (continuous_snd.comp continuous_snd)))
  exact p4m_cont_param (h := fun r x y => p4m_ha v θ (b r) x y) h.hm h.hM h.narrow hc'
    fun x₀ => ⟨A, hA0, fun r x _ y => hA (b r) (h.bg r) x y⟩

end

end HRS.MP.SelfSimP4Mol
