import HRS.MP.SelfSimP4MolE2

/-!
# MPP4MOL stage 5b/5c (7): `∂_t u` from the weak Fokker-Planck equation, and the derivative of the free energy density
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MP.SelfSimP4Mol

variable {d N : ℕ}

/-- The free energy density `Φ = u log u + u V/θ` along the flow. -/
def p4m_Phi (v θ : ℝ) (μ : ℝ → Measure (EucConfig d N)) (V : ℝ → EucConfig d N → ℝ) (s : ℝ)
    (x : EucConfig d N) : ℝ :=
  p4Mol v (μ s) x * Real.log (p4Mol v (μ s) x) + p4Mol v (μ s) x * V s x / θ

section
variable {θ T : ℝ} {b : ℝ → EucConfig d N → EucConfig d N} {V W : ℝ → EucConfig d N → ℝ}
  {μ : ℝ → Measure (EucConfig d N)} {Kl : ℝ≥0} {B K M CV : ℝ} {v : ℝ}

theorem P4MolData.pos_u (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (s : ℝ) (x : EucConfig d N) :
    0 < p4Mol v (μ s) x := by
  haveI := h.prob s
  exact p4m_mol_pos hv (h.hm s) x

theorem P4MolData.cont_ell (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (k : Fin N × Fin d) :
    Continuous (fun p : ℝ × EucConfig d N => p4m_ell v θ (μ p.1) (b p.1) k p.2) := by
  unfold p4m_ell
  refine ((h.cont_gu hv k).div (h.cont_u hv) fun p => (h.pos_u hv p.1 p.2).ne').sub ?_
  exact ((p4m_continuous_coord k).comp (h.bc.comp (Continuous.prodMk continuous_fst continuous_snd))).div_const θ

theorem P4MolData.cont_J (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (k : Fin N × Fin d) :
    Continuous (fun p : ℝ × EucConfig d N => θ * p4m_gu v (μ p.1) k p.2 - p4m_B v (μ p.1) (b p.1) k p.2) :=
  (continuous_const.mul (h.cont_gu hv k)).sub (h.cont_B hv k)

theorem P4MolData.cont_Lam (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) :
    Continuous (fun p : ℝ × EucConfig d N => p4m_Lam v θ (μ p.1) (V p.1) p.2) := by
  unfold p4m_Lam
  refine (((h.cont_u hv).log fun p => (h.pos_u hv p.1 p.2).ne').add continuous_const).add ?_
  exact (h.Vc.comp (Continuous.prodMk continuous_fst continuous_snd)).div_const θ

theorem P4MolData.cont_Phi (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) :
    Continuous (fun p : ℝ × EucConfig d N => p4m_Phi v θ μ V p.1 p.2) := by
  unfold p4m_Phi
  have hu := h.cont_u hv
  refine (hu.mul (hu.log fun p => (h.pos_u hv p.1 p.2).ne')).add ?_
  exact (hu.mul (h.Vc.comp (Continuous.prodMk continuous_fst continuous_snd))).div_const θ

/-- The mollified density as an integral of its time derivative. -/
theorem P4MolData.u_eq (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (x : EucConfig d N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) T) :
    p4Mol v (μ t) x = p4Mol v (μ 0) x + ∫ r in Set.Icc (0 : ℝ) t, p4m_a v θ (μ r) (b r) x := by
  have := h.fp _ (p4m_test hv x) t ht
  refine this.trans ?_
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun r _ => ?_
  unfold p4m_a
  refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
  exact p4m_gen_gauss hv θ b r x y

theorem P4MolData.hasDerivAt_u (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (x : EucConfig d N)
    {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => p4Mol v (μ s) x) (p4m_a v θ (μ r) (b r) x) r := by
  have hac : Continuous (fun s => p4m_a v θ (μ s) (b s) x) :=
    (h.cont_a hv).comp (Continuous.prodMk continuous_id continuous_const)
  have h1 := (hac.integral_hasStrictDerivAt 0 r).hasDerivAt
  have h2 := h1.const_add (p4Mol v (μ 0) x)
  refine h2.congr_of_eventuallyEq ?_
  filter_upwards [Ioo_mem_nhds hr.1 hr.2] with s hs
  rw [h.u_eq hv x ⟨hs.1.le, hs.2.le⟩, intervalIntegral.integral_of_le hs.1.le,
    integral_Icc_eq_integral_Ioc]

theorem P4MolData.hasDerivAt_Phi (h : P4MolData θ T b V W μ Kl B K M CV) (hv : 0 < v) (x : EucConfig d N)
    {r : ℝ} (hr : r ∈ Set.Ioo (0 : ℝ) T) :
    HasDerivAt (fun s => p4m_Phi v θ μ V s x)
      (p4m_a v θ (μ r) (b r) x * p4m_Lam v θ (μ r) (V r) x + p4Mol v (μ r) x * W r x / θ) r := by
  have hu := h.hasDerivAt_u hv x hr
  have hpos := (h.pos_u hv r x).ne'
  have hl := hu.log hpos
  have hVd := h.Wd r hr x
  have h3 := (hu.mul hl).add ((hu.mul hVd).div_const θ)
  unfold p4m_Phi p4m_Lam
  convert h3 using 1
  field_simp
  ring

end

end HRS.MP.SelfSimP4Mol
