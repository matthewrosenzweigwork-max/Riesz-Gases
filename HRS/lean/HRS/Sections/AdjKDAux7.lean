import HRS.Sections.AdjKDAux6

/-!
# ADJKD, part 7: the pathwise bound for the integrated remainder (packet B2)

Deterministic content of B2: for a path `Y : ℝ → Config d N` such that the mode forcings `y_j(r)` have
`∑_j ⟨j⟩^{-m} ∫_0^T |y_j| < ∞`, the integrand `r ↦ √N F_N^{h_{∇U^{r,t}e_k}}(Y_r, ρ_r)` is interval integrable and
`‖(∫_0^t V^{t,r} R_r dr)‖_{E_m} ≤ C_V ∑_j ⟨j⟩^{-m} ∫_0^T |y_j|` for all `t ∈ [0,T]`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

/-- The coordinate series of the evolved forcing equals the forcing along the propagated test function. -/
theorem adjkd_forcing_series (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {m : ℝ} (hm : (d : ℝ) + 2 < m) {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution htr.dyn ρ m Vev) {CV : ℝ}
    (hCV : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ CV) {N : ℕ} (Yc : Config d N) {r t : ℝ}
    (hr : 0 ≤ r) (hrt : r ≤ t) {Λ₀ : ℝ} (hΛ₀ : 0 ≤ Λ₀) (hρ : ∀ x, ρ r x ≤ Λ₀)
    (k : NonzeroLattice d) :
    HasSum (fun j : NonzeroLattice d =>
        NegSobolev.fourierCoeff (Vev t r (adjkdEps m j)) k *
          (Real.sqrt N * modulatedEnergy
            (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) Yc
            (withDensityReal (ρ r))))
      (Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s)
          (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k)))) Yc (withDensityReal (ρ r))) := by
  have hd1 : 1 ≤ d := by omega
  set ψ := propagator htr.dyn ρ r t (Torus.realMode k) with hψ
  have hcoef : ∀ j, NegSobolev.fourierCoeff (Vev t r (adjkdEps m j)) k = Torus.funRealCoeff ψ j :=
    fun j => adjkd_dual_coeff hdual hr hrt j k
  have hbound : ∀ j, |Torus.funRealCoeff ψ j| ≤
      (Lattice.jp k.1 ^ m * CV) * Lattice.jp j.1 ^ (-m) := by
    intro j
    rw [← hcoef]
    refine (adjkd_abs_fourierCoeff_le m k _).trans ?_
    calc Lattice.jp k.1 ^ m * ‖Vev t r (adjkdEps m j)‖
        ≤ Lattice.jp k.1 ^ m * (CV * Lattice.jp j.1 ^ (-m)) := by
          refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg (Torus.jp_pos _).le _)
          calc ‖Vev t r (adjkdEps m j)‖ ≤ ‖Vev t r‖ * ‖adjkdEps m j‖ := (Vev t r).le_opNorm _
            _ ≤ CV * Lattice.jp j.1 ^ (-m) := by
              rw [adjkdEps_norm]
              exact mul_le_mul_of_nonneg_right (hCV r t hr hrt) (Real.rpow_nonneg (Torus.jp_pos _).le _)
      _ = _ := by ring
  have hm' : (d : ℝ) / 2 + 2 < (m + 2) / 2 := by linarith
  have hsum := adjkd_sobolev_summable (m := m) (m' := (m + 2) / 2) (by linarith) _ hbound
  have hψ2 : Torus.IsCk 2 ψ := adjkd_propagator_ck2 htr.dyn ρ hr hrt _
  have h1 := (adjkd_forcing_expansion hd1 htr.hs0 htr.hsd Yc hΛ₀ hρ hm' hψ2 hsum).mul_left
    (Real.sqrt N)
  convert h1 using 1
  funext j
  rw [hcoef]
  ring


theorem adjkd_pathwise (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {m : ℝ} (hm : (d : ℝ) + 2 < m) {T : ℝ} (hT : 0 < T)
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution htr.dyn ρ m Vev) (hplain : IsPlainEvolution Vev T) {CV : ℝ}
    (hCV : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ CV) {N : ℕ} (Y : ℝ → Config d N)
    (hy : ∀ j : NonzeroLattice d, AEMeasurable (fun r => Real.sqrt N * modulatedEnergy
      (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (Y r)
      (withDensityReal (ρ r))) (volume.restrict (Set.Ioc 0 T)))
    (hΨ : ∑' j : NonzeroLattice d, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
      ∫⁻ r in Set.Ioc 0 T, ‖Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (Y r)
        (withDensityReal (ρ r))‖ₑ ≠ ⊤) :
    ∀ t ∈ Set.Icc (0 : ℝ) T,
      (∀ k : NonzeroLattice d, IntervalIntegrable (fun r => Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s)
          (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k)))) (Y r)
        (withDensityReal (ρ r))) volume 0 t) ∧
      (∑' k : NonzeroLattice d, ENNReal.ofReal (Lattice.jp k.1 ^ (-2 * m) *
        (∫ r in (0 : ℝ)..t, -(Real.sqrt N * modulatedEnergy
          (commKernel (periodicRieszGrad d s)
            (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k)))) (Y r)
          (withDensityReal (ρ r)))) ^ 2)) ^ (1 / 2 : ℝ) ≤
        ENNReal.ofReal CV * ∑' j : NonzeroLattice d, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
          ∫⁻ r in Set.Ioc 0 T, ‖Real.sqrt N * modulatedEnergy
            (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (Y r)
            (withDensityReal (ρ r))‖ₑ := by
  intro t ht
  have hd1 : 1 ≤ d := by omega
  set y : NonzeroLattice d → ℝ → ℝ := fun j r => Real.sqrt N * modulatedEnergy
    (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (Y r)
    (withDensityReal (ρ r)) with hydef
  have hjc := Q40b.q40b_jointCont hd1 htr T
  have hbdρ : ∀ r ∈ Set.Icc (0 : ℝ) T, ∃ Λ₀ : ℝ, 0 ≤ Λ₀ ∧ ∀ x, ρ r x ≤ Λ₀ := by
    intro r hr
    have hc : Continuous (ρ r) :=
      hjc.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hr, Set.mem_univ _⟩)
    obtain ⟨M, hM0, hM⟩ := exists_abs_bound hc
    exact ⟨M, hM0, fun x => (le_abs_self _).trans (hM x)⟩
  have hcont : ∀ z : NegSobolev d m, ContinuousOn (fun r => Vev t r z) (Set.Icc 0 t) := by
    intro z
    have := (hplain.2.2 z).comp (continuousOn_const.prodMk continuousOn_id)
      (s := Set.Icc (0 : ℝ) t) (t := {p : ℝ × ℝ | 0 ≤ p.2 ∧ p.2 ≤ p.1 ∧ p.1 ≤ T}) (f := fun r => (t, r))
      (fun r hr => ⟨hr.1, hr.2, ht.2⟩)
    exact this
  have hbd : ∀ r ∈ Set.Icc (0 : ℝ) t, ‖Vev t r‖ ≤ CV := fun r hr => hCV r t hr.1 hr.2
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Ioc 0 T := Set.Ioc_subset_Ioc_right ht.2
  have hy' : ∀ j, AEMeasurable (y j) (volume.restrict (Set.Ioc 0 t)) := fun j =>
    (hy j).mono_measure (Measure.restrict_mono hsub le_rfl)
  have hmono : ∀ j, ∫⁻ r in Set.Ioc 0 t, ‖y j r‖ₑ ≤ ∫⁻ r in Set.Ioc 0 T, ‖y j r‖ₑ := fun j =>
    lintegral_mono_set hsub
  have hI : ∑' j : NonzeroLattice d, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
      ∫⁻ r in Set.Ioc 0 t, ‖y j r‖ₑ ≠ ⊤ :=
    ne_top_of_le_ne_top hΨ (ENNReal.tsum_le_tsum fun j => mul_le_mul' le_rfl (hmono j))
  obtain ⟨hint, hbound⟩ := adjkd_abs_convolution ht.1 Vev hcont hbd y hy' hI
  have hid : ∀ (k : NonzeroLattice d), Set.EqOn (fun r => ∑' j : NonzeroLattice d,
      NegSobolev.fourierCoeff (Vev t r (adjkdEps m j)) k * y j r)
      (fun r => Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s)
          (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k)))) (Y r)
        (withDensityReal (ρ r))) (Set.Ioc 0 t) := by
    intro k r hr
    obtain ⟨Λ₀, hΛ₀, hΛ⟩ := hbdρ r ⟨hr.1.le, hr.2.trans ht.2⟩
    exact (adjkd_forcing_series hd htr hm hdual hCV (Y r) hr.1.le hr.2 hΛ₀ hΛ k).tsum_eq
  refine ⟨fun k => ?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht.1]
    exact (hint k).congr_fun (hid k) measurableSet_Ioc
  · have hcongr : ∀ k : NonzeroLattice d, (∫ r in (0 : ℝ)..t, -(Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s)
          (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k)))) (Y r)
        (withDensityReal (ρ r)))) ^ 2 =
        (∫ r in Set.Ioc 0 t, ∑' j : NonzeroLattice d,
          NegSobolev.fourierCoeff (Vev t r (adjkdEps m j)) k * y j r) ^ 2 := by
      intro k
      rw [intervalIntegral.integral_of_le ht.1, integral_neg, neg_sq]
      congr 1
      exact (setIntegral_congr_fun measurableSet_Ioc (hid k)).symm
    simp_rw [hcongr]
    refine hbound.trans (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun j => mul_le_mul' le_rfl (hmono j)))

end HRS.AdjK
