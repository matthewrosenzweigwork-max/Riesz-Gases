import HRS.MS.R26T8AA02b

/-!
# S8.2 T8A A02 (part c): a jointly measurable representative of `(x,y) ↦ oneJ(Q(·,y))(x)`
For `x ≠ y`, `oneJ C (Q(·,y)) x = ∫ ‖x-u‖^(-s) Stil(u,y) du` (P10a); the right side is a parametric integral of a jointly
measurable function, hence jointly measurable.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

variable {d : ℕ}

set_option maxHeartbeats 6400000 in
theorem r26t8a_a02_oneJ_meas (d : ℕ) (hd : 2 ≤ d) (a beta M A : ℝ) (ha : 0 < a) (hbeta : 0 < beta) (hM : 0 ≤ M)
    (hA : 0 ≤ A) {rho : Euc d → ℝ} (hrho : IsThermalEquilibrium d (criticalS d) a beta rho)
    {f : Euc d → ℝ} {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) :
    ∃ Jm : Euc d → Euc d → ℝ, Measurable (fun p : Euc d × Euc d => Jm p.1 p.2) ∧
      ∀ x y, x ≠ y → oneJ (critCoeff d a beta rho) (fun w => Q w y) x = Jm x y := by
  have hdd : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 < criticalS d := by unfold criticalS; linarith
  have hsd : criticalS d < d := by unfold criticalS; linarith
  have hρs : ContDiff ℝ ∞ rho :=
    (HRS.MS.Mov0.mv0_hgauss hd hs0.le hsd ha hbeta hrho).1
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.smooth.of_le (by norm_num)
  have hQt : Conormal (4 + 2) 1 M (criticalS d - 2) A Q := hQ.tangential
  have hoffm : MeasurableSet {p : Euc d × Euc d | p.1 ≠ p.2} :=
    (measurableSet_eq_fun measurable_fst measurable_snd).compl
  classical
  have hSc : ContinuousOn (Function.uncurry (r26t8a_Stil rho Q)) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    (r26t8a_f12_Stil_contDiffOn (k := 4) hQt.1 hρs).continuousOn
  set Sm : Euc d × Euc d → ℝ := Set.piecewise {p : Euc d × Euc d | p.1 ≠ p.2}
    (Function.uncurry (r26t8a_Stil rho Q)) (fun _ => 0) with hSm
  have hSmeas : Measurable Sm :=
    ContinuousOn.measurable_piecewise hSc continuousOn_const hoffm
  set s := criticalS d with hsdef
  refine ⟨fun x y => ∫ u, ‖x - u‖ ^ (-s) * Sm (u, y), ?_, ?_⟩
  · have hm : Measurable (fun q : (Euc d × Euc d) × Euc d => ‖q.1.1 - q.2‖ ^ (-s) * Sm (q.2, q.1.2)) :=
      ((((measurable_fst.comp measurable_fst).sub measurable_snd).norm).pow_const _).mul
        (hSmeas.comp (measurable_snd.prodMk (measurable_snd.comp measurable_fst)))
    exact (MeasureTheory.StronglyMeasurable.integral_prod_right
      (f := fun (p : Euc d × Euc d) (u : Euc d) => ‖p.1 - u‖ ^ (-s) * Sm (u, p.2)) hm.stronglyMeasurable).measurable
  · intro x y hxy
    obtain ⟨-, hid⟩ := r26t8a_conormal_potential_ibp d hd 4 1 a beta M (criticalS d) ha hbeta hM hsd rho hrho Q A hA
      hQt x y hxy
    rw [hid]
    have hker : ∀ w : Euc d, rieszKernel d (criticalS d) w = ‖w‖ ^ (-criticalS d) := fun w => by
      rw [rieszKernel, if_neg hs0.ne']
    have hopen : IsOpen ({y}ᶜ : Set (Euc d)) := isClosed_singleton.isOpen_compl
    have hf2 : ContDiffOn ℝ 2 (fun v => Q v y) {y}ᶜ := by
      have hg : ContDiff ℝ 2 (fun v : Euc d => (v, y)) := contDiff_id.prodMk contDiff_const
      have hmaps : Set.MapsTo (fun v : Euc d => (v, y)) {y}ᶜ {p : Euc d × Euc d | p.1 ≠ p.2} :=
        fun v hv => by simpa using hv
      exact hQ2.comp hg.contDiffOn hmaps
    haveI : Nontrivial (Euc d) := by
      apply Module.nontrivial_of_finrank_pos (R := ℝ)
      simp; omega
    have hae : ∀ᵐ u : Euc d ∂volume, u ≠ y := compl_mem_ae_iff.mpr (measure_singleton y)
    refine integral_congr_ae ?_
    filter_upwards [hae] with u hu
    have hfat : ContDiffAt ℝ 2 (fun v => Q v y) u := hf2.contDiffAt (hopen.mem_nhds (by simpa using hu))
    have hSu : Sm (u, y) = r26t8a_Stil rho Q u y := by
      rw [hSm, Set.piecewise_eq_of_mem _ _ _ (show (u, y) ∈ {p : Euc d × Euc d | p.1 ≠ p.2} from hu)]
      rfl
    rw [hSu, hker, ← r26t8a_f9_divSource_eq hfat]

end HRS.MS.R26T8A
