import HRS.MS.R26T8AA03m

/-!
# S8.2 T8A A02b: `r26t8a_repeated_representative` (Pro contract, verbatim)
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_repeated_representative (d : ℕ) (hd : 2 ≤ d) (a beta M : ℝ)
    (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M) (rho : Euc d → ℝ)
    (hrho : IsThermalEquilibrium d (criticalS d) a beta rho) (f : Euc d → ℝ)
    (A : ℝ) (hA : 0 ≤ A) (Q : Euc d → Euc d → ℝ) (hQ : PairCorrector a beta rho M A f Q) :
    let B := fun x y => if x = y then 0 else repeatedB rho Q x y
    Measurable (Function.uncurry B) ∧ (∀ x y, B x y = B y x) ∧
      (∀ x y, x ≠ y → B x y = repeatedB rho Q x y) := by
  classical
  intro B
  have hsymm := hQ.symmetric
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.smooth.of_le (by norm_num)
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hoffm : MeasurableSet {p : Euc d × Euc d | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  have hFm : Measurable (forceMean rho) :=
    ((r26t8a_thermal_force d hd a beta ha hbeta rho hrho).1.continuous).measurable
  have hgm : Measurable (rieszKernelGrad d (criticalS d)) :=
    HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  set Xm : Euc d × Euc d → Euc d := Set.piecewise {p : Euc d × Euc d | p.1 ≠ p.2}
    (fun p => pairGradX Q p.1 p.2) (fun _ => 0) with hXm
  have hXmeas : Measurable Xm :=
    ContinuousOn.measurable_piecewise (r26t8a_a02_gradX_cont hQ2) continuousOn_const hoffm
  have gy : ∀ u v : Euc d, pairGradY Q u v = pairGradX Q v u := fun u v => r26t8a_a01_gradY_symm hsymm u v
  have hX : ∀ u v : Euc d, u ≠ v → Xm (u, v) = pairGradX Q u v := fun u v h =>
    Set.piecewise_eq_of_mem _ _ _ (show (u, v) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} from h)
  set Bf : Euc d × Euc d → ℝ := fun p =>
    inner ℝ (rieszKernelGrad d (criticalS d) (p.1 - p.2)) (Xm (p.1, p.2) - Xm (p.2, p.1)) -
      2 * (inner ℝ (forceMean rho p.1) (Xm (p.1, p.2)) + inner ℝ (forceMean rho p.2) (Xm (p.2, p.1))) with hBf
  have hBfm : Measurable Bf := by
    have h1 : Measurable (fun p : Euc d × Euc d => p.1) := measurable_fst
    have h2 : Measurable (fun p : Euc d × Euc d => p.2) := measurable_snd
    have x12 := hXmeas.comp (h1.prodMk h2)
    have x21 := hXmeas.comp (h2.prodMk h1)
    have g12 := hgm.comp (h1.sub h2)
    exact (Measurable.inner g12 (x12.sub x21)).sub
      (measurable_const.mul ((Measurable.inner (hFm.comp h1) x12).add (Measurable.inner (hFm.comp h2) x21)))
  have hBe : ∀ x y, x ≠ y → repeatedB rho Q x y = Bf (x, y) := by
    intro x y hxy
    simp only [hBf, hX x y hxy, hX y x hxy.symm]
    unfold repeatedB
    rw [gy x y]
  have hBdef : ∀ x y, B x y = if x = y then 0 else Bf (x, y) := by
    intro x y
    by_cases h : x = y
    · simp [B, h]
    · simp only [B, if_neg h, hBe x y h]
  refine ⟨?_, ?_, fun x y hxy => by simp [B, if_neg hxy]⟩
  · have hD : MeasurableSet {p : Euc d × Euc d | p.1 = p.2} := measurableSet_eq_fun measurable_fst measurable_snd
    have : Measurable (fun p : Euc d × Euc d => if p.1 = p.2 then (0 : ℝ) else Bf p) :=
      Measurable.ite hD measurable_const hBfm
    have e : Function.uncurry B = fun p : Euc d × Euc d => if p.1 = p.2 then (0 : ℝ) else Bf p := by
      funext p; exact hBdef p.1 p.2
    rw [e]; exact this
  · intro x y
    by_cases h : x = y
    · simp [B, h]
    · have h' : y ≠ x := Ne.symm h
      simp only [B, if_neg h, if_neg h']
      -- symmetry of repeatedB
      have hn : rieszKernelGrad d (criticalS d) (y - x) = -rieszKernelGrad d (criticalS d) (x - y) := by
        rw [show y - x = -(x - y) from (neg_sub x y).symm]
        exact HRS.MS.R2Interp.s102_rieszKernelGrad_neg (criticalS d) _
      unfold repeatedB
      simp only [gy, hn, inner_neg_left, inner_sub_right, inner_sub_left]
      ring

end HRS.MS.R26T8A
