import HRS.MS.UniqN3aH

/-!
# N3a, part I: the Fourier bridge for the Riesz kernel on the application's test classes

**Theorem `n3a_bridge`** (`d ≥ 1`, `0 ≤ s`, `d - 2 ≤ s < d`, `g = rieszKernel d s`): there is `c > 0`
such that for every `q : Euc d`, every `u ∈ L²(ℝ^d)` (in particular every `u` with `MemSobolev 1 u`)
and every `v ∈ C²_c`,
`symbolForm (c (2π⟨ξ,q⟩)² ‖ξ‖^{s-d}) u v = - ∫ u (g * D_q² v)`, `D_q w = fderiv w · q`,
with the integrand `u (g * D_q² v)` and the Fourier integrand integrable.
-/

noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate SchwartzMap LineDeriv

namespace HRS.MS.UniqN3a
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux HRS.MS.UniqT2

variable {d : ℕ}

/-- Schwartz `u`, `v ∈ C²_c`. -/
theorem n3a_step2 {c s : ℝ} (hc : 0 < c) (hs0 : 0 ≤ s) (hs2 : (d : ℝ) - 2 ≤ s) (hsd : s < d)
    (hid : ∀ (q : Euc d) (u v : SchwartzMap (Euc d) ℝ), symbolForm (mq c s q) u v =
      - ∫ x, u x * HRS.Whole.convFun (rieszKernel d s) (qq q v) x)
    (q : Euc d) (u : SchwartzMap (Euc d) ℝ) {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) :
    symbolForm (mq c s q) u v = - ∫ x, u x * HRS.Whole.convFun (rieszKernel d s) (qq q v) x := by
  obtain ⟨R1, hR1⟩ := hvc.isCompact.isBounded.subset_closedBall (0 : Euc d)
  have hfs : Function.support (qq q v) ⊆ closedBall (0 : Euc d) R1 := fun x hx =>
    hR1 (qq_support_sub q v hx)
  have h1 := lhs_conv hc hs2 hsd q u hv hvc
  have h2 := (rhs_conv hs0 hsd u (qq_contDiff hv) (qq_hasCompactSupport hvc) hfs).neg
  have heq : ∀ n, symbolForm (mq c s q) u (Sn n hv hvc) =
      - ∫ x, u x * HRS.Whole.convFun (rieszKernel d s) (mo n (qq q v)) x := by
    intro n
    rw [hid q u (Sn n hv hvc), Sn_apply, qq_mo n hv hvc q]
  simp_rw [heq] at h1
  exact tendsto_nhds_unique h1 h2

/-- The extension to `u ∈ L²`. -/
theorem n3a_ext {c s : ℝ} (hd : 1 ≤ d) (hc : 0 < c) (hs0 : 0 ≤ s) (hs2 : (d : ℝ) - 2 ≤ s)
    (hsd : s < d)
    (hid : ∀ (q : Euc d) (u v : SchwartzMap (Euc d) ℝ), symbolForm (mq c s q) u v =
      - ∫ x, u x * HRS.Whole.convFun (rieszKernel d s) (qq q v) x)
    (q : Euc d) {u : Euc d → ℝ} (hu : MemLp u 2 volume) {v : Euc d → ℝ} (hv : ContDiff ℝ 2 v)
    (hvc : HasCompactSupport v) :
    Integrable (fun x => u x * HRS.Whole.convFun (rieszKernel d s) (qq q v) x) ∧
    Integrable (fun ξ => ((mq c s q ξ : ℝ) : ℂ) * (fourierL2 u ξ * conj (fourierL2 v ξ))) ∧
    symbolForm (mq c s q) u v = - ∫ x, u x * HRS.Whole.convFun (rieszKernel d s) (qq q v) x := by
  set w : Euc d → ℝ := HRS.Whole.convFun (rieszKernel d s) (qq q v) with hwdef
  have hw : MemLp w 2 volume := w_memLp hd hs0 hs2 hsd hv hvc q
  have hG := G_memLp hc hs2 hsd q hv hvc
  refine ⟨hu.integrable_mul hw, ?_, ?_⟩
  · refine (integrable_mul_conj (memLp_fourierL2 hu) hG).congr (Eventually.of_forall fun ξ => ?_)
    simp only [map_mul, Complex.conj_ofReal]; ring
  set CG : ℝ := Real.sqrt (∫ ξ, ‖((mq c s q ξ : ℝ) : ℂ) * fourierL2 v ξ‖ ^ 2) +
    Real.sqrt (∫ x, w x ^ 2) with hCG
  have hCG0 : 0 ≤ CG := by positivity
  have key : ∀ ε : ℝ, 0 < ε →
      |symbolForm (mq c s q) u v - (- ∫ x, u x * w x)| ≤ ε := by
    intro ε hε
    obtain ⟨φ, hφ⟩ := exists_schwartz_approx hu (ε := (ε / (CG + 1)) ^ 2) (by positivity)
    have hφm : MemLp (⇑φ) 2 volume := φ.memLp 2 volume
    have hs := Real.sqrt_le_sqrt hφ
    rw [Real.sqrt_sq (by positivity)] at hs
    have e2 := n3a_step2 hc hs0 hs2 hsd hid q φ hv hvc
    have b1 := lhs_diff_le (c := c) (s := s) q hu hφm hG
    have b2 := rhs_diff_le hu hφm hw
    have hsq : 0 ≤ Real.sqrt (∫ x, (u x - φ x) ^ 2) := Real.sqrt_nonneg _
    have : symbolForm (mq c s q) u v - (- ∫ x, u x * w x) =
        (symbolForm (mq c s q) u v - symbolForm (mq c s q) φ v) +
          ((∫ x, u x * w x) - ∫ x, φ x * w x) := by
      rw [e2]; ring
    rw [this]
    refine (abs_add_le _ _).trans ?_
    calc _ ≤ Real.sqrt (∫ x, (u x - φ x) ^ 2) * CG := by
          rw [hCG, mul_add]; exact add_le_add b1 b2
      _ ≤ ε / (CG + 1) * CG := by gcongr
      _ ≤ ε := by
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
  have h0 : |symbolForm (mq c s q) u v - (- ∫ x, u x * w x)| ≤ 0 := by
    by_contra hneg
    push Not at hneg
    have := key _ (half_pos hneg)
    linarith
  exact sub_eq_zero.1 (abs_nonpos_iff.1 h0)

/-- **N3a (Fourier bridge, application form).**  `d ≥ 1`, `0 ≤ s`, `d - 2 ≤ s < d`.  There is `c > 0`
such that for all `q`, all `u ∈ L²` and all `v ∈ C²_c`:
`symbolForm (c (2π⟨ξ,q⟩)² ‖ξ‖^{s-d}) u v = - ∫ u (g * D_q² v)`, both integrands being integrable. -/
theorem n3a_bridge (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs2 : (d : ℝ) - 2 ≤ s) (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : Euc d) (u v : Euc d → ℝ), MemLp u 2 volume → ContDiff ℝ 2 v →
      HasCompactSupport v →
      Integrable (fun x => u x * HRS.Whole.convFun (rieszKernel d s)
        (fun y => fderiv ℝ (fun z => fderiv ℝ v z q) y q) x) ∧
      Integrable (fun ξ : Euc d =>
        ((c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) *
          (fourierL2 u ξ * conj (fourierL2 v ξ))) ∧
      symbolForm (fun ξ : Euc d => c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d)) u v =
        - ∫ x, u x * HRS.Whole.convFun (rieszKernel d s)
            (fun y => fderiv ℝ (fun z => fderiv ℝ v z q) y q) x := by
  obtain ⟨c, hc, hid⟩ := n3a_schwartz hd hs0 hsd
  refine ⟨c, hc, fun q u v hu hv hvc => ?_⟩
  exact n3a_ext hd hc hs0 hs2 hsd hid q hu hv hvc

/-- The same with the hypothesis `MemSobolev 1 u` of the application. -/
theorem n3a_bridge_sobolev (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs2 : (d : ℝ) - 2 ≤ s)
    (hsd : s < d) :
    ∃ c : ℝ, 0 < c ∧ ∀ (q : Euc d) (u v : Euc d → ℝ), HRS.PDE.ToolboxRd.MemSobolev 1 u → ContDiff ℝ 2 v →
      HasCompactSupport v →
      Integrable (fun x => u x * HRS.Whole.convFun (rieszKernel d s)
        (fun y => fderiv ℝ (fun z => fderiv ℝ v z q) y q) x) ∧
      Integrable (fun ξ : Euc d =>
        ((c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d) : ℝ) : ℂ) *
          (fourierL2 u ξ * conj (fourierL2 v ξ))) ∧
      symbolForm (fun ξ : Euc d => c * (2 * Real.pi * inner ℝ ξ q) ^ 2 * ‖ξ‖ ^ (s - d)) u v =
        - ∫ x, u x * HRS.Whole.convFun (rieszKernel d s)
            (fun y => fderiv ℝ (fun z => fderiv ℝ v z q) y q) x := by
  obtain ⟨c, hc, h⟩ := n3a_bridge hd hs0 hs2 hsd
  exact ⟨c, hc, fun q u v hu hv hvc => h q u v hu.1 hv hvc⟩

end HRS.MS.UniqN3a
