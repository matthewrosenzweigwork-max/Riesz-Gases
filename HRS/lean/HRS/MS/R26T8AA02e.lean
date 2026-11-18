import HRS.MS.R26T8AA02d

/-!
# S8.2 T8A A02 (part e): Borel measurability of `tripleG` off the collision set
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_a02_G_meas (d : ℕ) (hd : 2 ≤ d) (a beta M A : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hA : 0 ≤ A) {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) :
    Measurable (fun p : Euc d × Euc d × Euc d =>
      if (p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2) then
        tripleG (critCoeff d a beta rho) rho Q p.1 p.2.1 p.2.2 else 0) := by
  classical
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.smooth.of_le (by norm_num)
  have hsymm := hQ.symmetric
  have hoffm : MeasurableSet {p : Euc d × Euc d | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  obtain ⟨Pm, hPm, hPeq⟩ := r26t8a_a02_pairJ_meas d hd a beta M A ha hbeta hM hA hrho hQ
  set Xm : Euc d × Euc d → Euc d := Set.piecewise {p : Euc d × Euc d | p.1 ≠ p.2}
    (fun p => pairGradX Q p.1 p.2) (fun _ => 0) with hXm
  have hXmeas : Measurable Xm :=
    ContinuousOn.measurable_piecewise (r26t8a_a02_gradX_cont hQ2) continuousOn_const hoffm
  have hFm : Measurable (forceMean rho) :=
    ((r26t8a_thermal_force d hd a beta ha hbeta rho hrho).1.continuous).measurable
  have hgm : Measurable (rieszKernelGrad d (criticalS d)) :=
    HRS.Whole.movtr_rieszKernelGrad_measurable (d := d) (criticalS d)
  set Gf : Euc d × Euc d × Euc d → ℝ := fun p =>
    (1 / 3 : ℝ) * (
      -inner ℝ (rieszKernelGrad d (criticalS d) (p.1 - p.2.2) - forceMean rho p.1) (Xm (p.1, p.2.1))
      - inner ℝ (rieszKernelGrad d (criticalS d) (p.2.1 - p.2.2) - forceMean rho p.2.1) (Xm (p.2.1, p.1))
      - inner ℝ (rieszKernelGrad d (criticalS d) (p.1 - p.2.1) - forceMean rho p.1) (Xm (p.1, p.2.2))
      + inner ℝ (rieszKernelGrad d (criticalS d) (p.2.1 - p.2.2) + forceMean rho p.2.2) (Xm (p.2.2, p.1))
      - inner ℝ (rieszKernelGrad d (criticalS d) (p.2.1 - p.1) - forceMean rho p.2.1) (Xm (p.2.1, p.2.2))
      + inner ℝ (rieszKernelGrad d (criticalS d) (p.1 - p.2.2) + forceMean rho p.2.2) (Xm (p.2.2, p.2.1))
      - Pm p.1 p.2.1 - Pm p.1 p.2.2 - Pm p.2.1 p.2.2) with hGf
  have h1 : Measurable (fun p : Euc d × Euc d × Euc d => p.1) := measurable_fst
  have h2 : Measurable (fun p : Euc d × Euc d × Euc d => p.2.1) := measurable_fst.comp measurable_snd
  have h3 : Measurable (fun p : Euc d × Euc d × Euc d => p.2.2) := measurable_snd.comp measurable_snd
  have hGfm : Measurable Gf := by
    simp only [hGf]
    refine measurable_const.mul ?_
    have gA := hgm.comp (h1.sub h3)
    have gB := hgm.comp (h2.sub h3)
    have gC := hgm.comp (h1.sub h2)
    have gD := hgm.comp (h2.sub h1)
    have fx := hFm.comp h1
    have fy := hFm.comp h2
    have fz := hFm.comp h3
    have x12 := hXmeas.comp (h1.prodMk h2)
    have x21 := hXmeas.comp (h2.prodMk h1)
    have x13 := hXmeas.comp (h1.prodMk h3)
    have x31 := hXmeas.comp (h3.prodMk h1)
    have x23 := hXmeas.comp (h2.prodMk h3)
    have x32 := hXmeas.comp (h3.prodMk h2)
    have p12 := hPm.comp (h1.prodMk h2)
    have p13 := hPm.comp (h1.prodMk h3)
    have p23 := hPm.comp (h2.prodMk h3)
    exact (((((((((Measurable.inner (gA.sub fx) x12).neg.sub (Measurable.inner (gB.sub fy) x21)).sub
      (Measurable.inner (gC.sub fx) x13)).add (Measurable.inner (gB.add fz) x31)).sub
      (Measurable.inner (gD.sub fy) x23)).add (Measurable.inner (gA.add fz) x32)).sub p12).sub p13).sub p23)
  have hD : MeasurableSet {p : Euc d × Euc d × Euc d | p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2} := by
    refine (measurableSet_eq_fun h1 h2).compl.inter ((measurableSet_eq_fun h1 h3).compl.inter
      (measurableSet_eq_fun h2 h3).compl)
  have hmeas : Measurable (fun p : Euc d × Euc d × Euc d =>
      if (p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2) then Gf p else 0) :=
    Measurable.ite hD hGfm (measurable_const (a := (0 : ℝ)))
  have hX : ∀ u v : Euc d, u ≠ v → Xm (u, v) = pairGradX Q u v := fun u v h =>
    Set.piecewise_eq_of_mem _ _ _ (show (u, v) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} from h)
  have e : (fun p : Euc d × Euc d × Euc d =>
      if (p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2) then
        tripleG (critCoeff d a beta rho) rho Q p.1 p.2.1 p.2.2 else 0) =
      fun p : Euc d × Euc d × Euc d =>
      if (p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2) then Gf p else 0 := by
    funext p
    by_cases hp : (p.1 ≠ p.2.1 ∧ p.1 ≠ p.2.2 ∧ p.2.1 ≠ p.2.2)
    · rw [if_pos hp, if_pos hp]
      obtain ⟨hxy, hxz, hyz⟩ := hp
      have u := r26t8a_a01_ungrouped (a := a) (beta := beta) (rho := rho) hsymm p.1 p.2.1 p.2.2
      simp only [hGf, hX _ _ hxy, hX _ _ hxy.symm, hX _ _ hxz, hX _ _ hxz.symm, hX _ _ hyz, hX _ _ hyz.symm,
        ← hPeq _ _ hxy, ← hPeq _ _ hxz, ← hPeq _ _ hyz]
      linarith
    · rw [if_neg hp, if_neg hp]
  rw [e]
  exact hmeas

end HRS.MS.R26T8A
