import HRS.Main.T25PAux2

/-!
# T25P, part 3: the weighted pathwise bound for the integrated remainder (the `a`-uniform form of `adjkd_pathwise`)

`adjkd_pathwise` bounds the `E_m`-norm of the integrated forcing `∫_0^t V^{t,r} R^r dr` by `C_V ∑_j ⟨j⟩^{-m} ∫_0^T |y_j|` with a
horizon-dependent integral.  Here the decay `‖V^{t,r}‖ ≤ C g(r)` for `t ∈ [a,T]` (`g = e^{-c(a-r)_+}`) is kept: the evolution is
rescaled `Ṽ^{t,r} = g(r)^{-1} V^{t,r}`, `ỹ_j = g y_j`, which turns the weighted bound into the unweighted `adjkd_abs_convolution`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem t25p_pathwise (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ)
    {m : ℝ} (hm : (d : ℝ) + 2 < m) {T a : ℝ} (hT : 0 < T) (ha : 0 ≤ a)
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m}
    (hdual : IsDualEvolution htr.dyn ρ m Vev) (hplain : IsPlainEvolution Vev T) {CV C0 : ℝ}
    (hCV0 : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ C0)
    (g : ℝ → ℝ) (hgc : Continuous g) (hgpos : ∀ r, 0 < g r)
    (hg : ∀ t ∈ Set.Icc a T, ∀ r ∈ Set.Icc (0 : ℝ) t, ‖Vev t r‖ ≤ CV * g r)
    {N : ℕ} (Y : ℝ → Config d N)
    (hy : ∀ j : NonzeroLattice d, AEMeasurable (fun r => Real.sqrt N * modulatedEnergy
      (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (Y r)
      (withDensityReal (ρ r))) (volume.restrict (Set.Ioc 0 T)))
    (hΨ : ∑' j : NonzeroLattice d, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
      ∫⁻ r in Set.Ioc 0 T, ENNReal.ofReal (g r) * ‖Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (Y r)
        (withDensityReal (ρ r))‖ₑ ≠ ⊤) :
    ∀ t ∈ Set.Icc a T,
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
          ∫⁻ r in Set.Ioc 0 T, ENNReal.ofReal (g r) * ‖Real.sqrt N * modulatedEnergy
            (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (Y r)
            (withDensityReal (ρ r))‖ₑ := by
  intro t ht
  have ht0 : 0 ≤ t := ha.trans ht.1
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
  -- the rescaled evolution and forcing
  set Vev' : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m := fun t' r => (g r)⁻¹ • Vev t' r with hVev'
  set y' : NonzeroLattice d → ℝ → ℝ := fun j r => g r * y j r with hy'def
  have hcont' : ∀ z : NegSobolev d m, ContinuousOn (fun r => Vev' t r z) (Set.Icc 0 t) := by
    intro z
    have h1 : ContinuousOn (fun r => (g r)⁻¹) (Set.Icc 0 t) :=
      (hgc.inv₀ fun r => (hgpos r).ne').continuousOn
    exact h1.smul (hcont z)
  have hbd' : ∀ r ∈ Set.Icc (0 : ℝ) t, ‖Vev' t r‖ ≤ CV := by
    intro r hr
    have h1 := hg t ht r hr
    have hgp := hgpos r
    show ‖(g r)⁻¹ • Vev t r‖ ≤ CV
    rw [norm_smul, norm_inv, Real.norm_eq_abs, abs_of_pos hgp]
    calc (g r)⁻¹ * ‖Vev t r‖ ≤ (g r)⁻¹ * (CV * g r) := by gcongr
      _ = CV := by field_simp
  have hsub : Set.Ioc (0 : ℝ) t ⊆ Set.Ioc 0 T := Set.Ioc_subset_Ioc_right ht.2
  have hy'm : ∀ j, AEMeasurable (y' j) (volume.restrict (Set.Ioc 0 t)) := fun j =>
    hgc.measurable.aemeasurable.mul ((hy j).mono_measure (Measure.restrict_mono hsub le_rfl))
  have hnorm : ∀ j r, ‖y' j r‖ₑ = ENNReal.ofReal (g r) * ‖y j r‖ₑ := by
    intro j r
    simp only [hy'def, enorm_mul]
    rw [← ofReal_norm, Real.norm_eq_abs, abs_of_pos (hgpos r)]
  have hmono : ∀ j, ∫⁻ r in Set.Ioc 0 t, ‖y' j r‖ₑ ≤
      ∫⁻ r in Set.Ioc 0 T, ENNReal.ofReal (g r) * ‖y j r‖ₑ := fun j => by
    simp_rw [hnorm]
    exact lintegral_mono_set hsub
  have hI : ∑' j : NonzeroLattice d, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
      ∫⁻ r in Set.Ioc 0 t, ‖y' j r‖ₑ ≠ ⊤ :=
    ne_top_of_le_ne_top hΨ (ENNReal.tsum_le_tsum fun j => mul_le_mul' le_rfl (hmono j))
  obtain ⟨hint, hbound⟩ := adjkd_abs_convolution ht0 Vev' hcont' hbd' y' hy'm hI
  have hid : ∀ (k : NonzeroLattice d), Set.EqOn (fun r => ∑' j : NonzeroLattice d,
      NegSobolev.fourierCoeff (Vev' t r (adjkdEps m j)) k * y' j r)
      (fun r => Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s)
          (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k)))) (Y r)
        (withDensityReal (ρ r))) (Set.Ioc 0 t) := by
    intro k r hr
    obtain ⟨Λ₀, hΛ₀, hΛ⟩ := hbdρ r ⟨hr.1.le, hr.2.trans ht.2⟩
    have hser := (adjkd_forcing_series hd htr hm hdual hCV0 (Y r) hr.1.le hr.2 hΛ₀ hΛ k).tsum_eq
    dsimp only
    rw [← hser]
    refine tsum_congr fun j => ?_
    have hc : NegSobolev.fourierCoeff (Vev' t r (adjkdEps m j)) k =
        (g r)⁻¹ * NegSobolev.fourierCoeff (Vev t r (adjkdEps m j)) k := by
      show NegSobolev.fourierCoeff ((g r)⁻¹ • Vev t r (adjkdEps m j)) k = _
      rw [← adjkdCoord_apply, map_smul, adjkdCoord_apply, smul_eq_mul]
    rw [hc]
    simp only [hy'def, hydef]
    have := (hgpos r).ne'
    field_simp
  refine ⟨fun k => ?_, ?_⟩
  · rw [intervalIntegrable_iff_integrableOn_Ioc_of_le ht0]
    exact (hint k).congr_fun (hid k) measurableSet_Ioc
  · have hcongr : ∀ k : NonzeroLattice d, (∫ r in (0 : ℝ)..t, -(Real.sqrt N * modulatedEnergy
        (commKernel (periodicRieszGrad d s)
          (Torus.grad (propagator htr.dyn ρ r t (Torus.realMode k)))) (Y r)
        (withDensityReal (ρ r)))) ^ 2 =
        (∫ r in Set.Ioc 0 t, ∑' j : NonzeroLattice d,
          NegSobolev.fourierCoeff (Vev' t r (adjkdEps m j)) k * y' j r) ^ 2 := by
      intro k
      rw [intervalIntegral.integral_of_le ht0, integral_neg, neg_sq]
      congr 1
      exact (setIntegral_congr_fun measurableSet_Ioc (hid k)).symm
    simp_rw [hcongr]
    refine hbound.trans (mul_le_mul' le_rfl (ENNReal.tsum_le_tsum fun j => mul_le_mul' le_rfl (hmono j)))

end HRS.T25P
