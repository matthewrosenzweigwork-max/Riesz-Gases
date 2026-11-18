import HRS.Main.T25PAux16

/-!
# T25P, part 17: stage 1, the mild decomposition at level `m` on a window with a pathwise bound of the remainder
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem t25p_enorm_eq_tsum {m : ℝ} (F : NegSobolev d m) :
    ‖F‖ₑ = (∑' k : NonzeroLattice d, ENNReal.ofReal
      (Lattice.jp k.1 ^ (-2 * m) * NegSobolev.fourierCoeff F k ^ 2)) ^ (1 / 2 : ℝ) := by
  obtain ⟨hcs, hGn⟩ := NegSobolev.coord_sq F
  have hterm : ∀ k : NonzeroLattice d, Lattice.jp k.1 ^ (-2 * m) * NegSobolev.fourierCoeff F k ^ 2 =
      NegSobolev.coord F k ^ 2 := by
    intro k
    have h1 : NegSobolev.coord F k = Lattice.jp k.1 ^ (-m) * NegSobolev.fourierCoeff F k := by
      unfold NegSobolev.fourierCoeff
      rw [← mul_assoc, ← Real.rpow_add (Torus.jp_pos _)]
      simp
    rw [h1, mul_pow, Torus.jp_rpow_sq]
    congr 2
    ring
  simp_rw [hterm]
  rw [← ENNReal.ofReal_tsum_of_nonneg (fun k => sq_nonneg _) hcs, ← hGn]
  have hpow : (ENNReal.ofReal (‖F‖ ^ 2)) ^ (1 / 2 : ℝ) = ENNReal.ofReal ‖F‖ := by
    rw [ENNReal.ofReal_rpow_of_nonneg (sq_nonneg _) (by norm_num)]
    congr 1
    rw [← Real.rpow_natCast, ← Real.rpow_mul (norm_nonneg _)]
    norm_num
  rw [hpow, ofReal_norm]

set_option maxHeartbeats 1600000 in
theorem t25p_stage1 (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) + 2 < m) {T : ℝ} (hT : 0 < T) {Cr cr : ℝ} (hCr : 0 < Cr) (hcr : 0 < cr) {Cmax : ℝ}
    {Vev : ℝ → ℝ → NegSobolev d m →L[ℝ] NegSobolev d m} (hdual : IsDualEvolution htr.dyn ρ m Vev)
    (hEv : T25Ev m Cr cr T Cmax Vev) {N : ℕ} (hN : 2 ≤ N) {a : ℝ} (ha : 0 ≤ a)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hX : IsParticleSystem P htr.dyn (a + T) X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsFilteredSolution P ℱ W' W X) :
    ∃ (Mart Z : ℝ → Ω → NegSobolev d m),
      IsHilbertMartingaleWithCovariation P ℱ (a + T) Mart
        (fun r ω => covForm m β⁻¹ (empirical (X r.toNNReal ω))) ∧
      (∀ t ∈ Set.Icc (0 : ℝ) (a + T),
        IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Mart 0 t (Z t)) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T))) ∧ (∀ t, Measurable (Z t)) ∧
      (∀ᵐ ω ∂P, ContinuousOn (fun t => flucProc m (Real.sqrt N) X ρ t ω -
        Vev t 0 (flucProc m (Real.sqrt N) X ρ 0 ω) - Z t ω) (Set.Icc 0 (a + T))) ∧
      (∀ t, Measurable (fun ω => flucProc m (Real.sqrt N) X ρ t ω -
        Vev t 0 (flucProc m (Real.sqrt N) X ρ 0 ω) - Z t ω)) ∧
      (∀ᵐ ω ∂P, ∀ t ∈ Set.Icc a (a + T), ‖flucProc m (Real.sqrt N) X ρ t ω -
        Vev t 0 (flucProc m (Real.sqrt N) X ρ 0 ω) - Z t ω‖ₑ ≤
          ENNReal.ofReal Cr * t25p_Psi d s ρ m cr a T X ω) := by
  classical
  have hd1 : 1 ≤ d := by omega
  have hT' : 0 < a + T := by linarith
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hm0 : (d : ℝ) / 2 < m := by linarith
  have hplain := hEv.plain (a + T) hT'.le
  -- B0: the particle martingale
  obtain ⟨Mart, hM, hMid⟩ := adjk_particle_martingale_proof hd htr m hm1 (a + T) hT' hN P X₀ W X hX ℱ W' hF
  -- the convolution
  obtain ⟨Z₀, hZ₀S, hZ₀c, hZ₀m⟩ := hEv.exists_conv (a + T) hT' Ω P ℱ Mart _ hM
  obtain ⟨Z, hZm, hZc, hZeq⟩ := gf_measurable_modification_proof P (a + T) Z₀ hZ₀c hZ₀m
  have hZS : ∀ t ∈ Set.Icc (0 : ℝ) (a + T),
      IsStochConv P Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Mart 0 t (Z t) :=
    fun t ht => isStochConv_congr_ae (hZ₀S t ht) (hZeq t ht).symm
  have hZc' : ∀ᵐ ω ∂P, ContinuousOn (fun t => Z t ω) (Set.Icc 0 (a + T)) :=
    Filter.Eventually.of_forall hZc
  -- B3: the mild identity
  have hB3 := adjk_mild_decomposition_proof hd htr m hm1 (a + T) hT' hN P X₀ W X hX ℱ W' hF Mart hM hMid
    Vev hdual Z hZS (fun t _ => (hZm t).aemeasurable) hZc'
  -- the fluctuation process
  have hXm : ∀ t : ℝ≥0, Measurable (X t) := hX.sol.adapted
  have hflm : ∀ t : ℝ, Measurable (fun ω => flucProc m (Real.sqrt N) X ρ t ω) := fun t =>
    ((gf_measurable_ofMeasureDiff_proof m hm0 (withDensityReal (ρ t))).const_smul (Real.sqrt N)).comp
      (hXm (Real.toNNReal t))
  have hflc : ∀ᵐ ω ∂P, ContinuousOn (fun t => flucProc m (Real.sqrt N) X ρ t ω) (Set.Icc 0 (a + T)) := by
    filter_upwards [hX.sol.cont] with ω hω
    have := adjkd_fluc_cont_path hd htr m hm0 (a + T) hT'.le X (Real.sqrt N) ω hω
    exact continuousOn_iff_continuous_restrict.2 this
  have hVc : ∀ x : NegSobolev d m, ContinuousOn (fun t : ℝ => Vev t 0 x) (Set.Icc 0 (a + T)) := fun x =>
    Comp28.continuousOn_V_zero Vev hplain.2.2 x
  refine ⟨Mart, Z, hM, hZS, hZc', hZm, ?_, ?_, ?_⟩
  · filter_upwards [hflc, hZc'] with ω h1 h2
    exact (h1.sub (hVc _)).sub h2
  · intro t
    exact ((hflm t).sub ((Vev t 0).continuous.measurable.comp (hflm 0))).sub (hZm t)
  · -- the pathwise bound
    have hDens : ∀ r ∈ Set.Icc (0 : ℝ) (a + T), IsProbDensity (ρ r) := fun r hr =>
      (Q40b.q40b_meanField hd1 htr hT').density r hr
    have hCV0 : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Cr := by
      intro u t hu hut
      refine (hEv.decay u t hu hut).trans ?_
      have : Real.exp (-cr * (t - u)) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith)
      nlinarith
    have hg : ∀ t ∈ Set.Icc a (a + T), ∀ r ∈ Set.Icc (0 : ℝ) t, ‖Vev t r‖ ≤ Cr * t25p_w cr a r := by
      intro t ht r hr
      refine (hEv.decay r t hr.1 hr.2).trans ?_
      refine mul_le_mul_of_nonneg_left ?_ hCr.le
      unfold t25p_w
      rw [Real.exp_le_exp]
      have : max (a - r) 0 ≤ t - r := max_le (by linarith [ht.1]) (by linarith [hr.2])
      nlinarith
    filter_upwards [hB3] with ω hω
    intro t ht
    have ht0 : t ∈ Set.Icc (0 : ℝ) (a + T) := ⟨ha.trans ht.1, ht.2⟩
    -- the coordinates of the remainder
    set Rt : NegSobolev d m := flucProc m (Real.sqrt N) X ρ t ω -
      Vev t 0 (flucProc m (Real.sqrt N) X ρ 0 ω) - Z t ω with hRt
    have hcoord : ∀ k : NonzeroLattice d, NegSobolev.fourierCoeff Rt k = evolvingForcingCoord htr.dyn ρ X k t ω := by
      intro k
      have h1 := hω t ht0 k
      have e1 : etaE m (X t.toNNReal ω) (withDensityReal (ρ t)) = flucProc m (Real.sqrt N) X ρ t ω := rfl
      have e0 : etaE m (X 0 ω) (withDensityReal (ρ 0)) = flucProc m (Real.sqrt N) X ρ 0 ω := by
        simp only [flucProc, etaE, flucE, Real.toNNReal_zero]
      rw [e1, e0] at h1
      have hsub : NegSobolev.fourierCoeff Rt k = NegSobolev.fourierCoeff (flucProc m (Real.sqrt N) X ρ t ω) k -
          NegSobolev.fourierCoeff (Vev t 0 (flucProc m (Real.sqrt N) X ρ 0 ω)) k -
          NegSobolev.fourierCoeff (Z t ω) k := by
        rw [hRt, ← adjkdCoord_apply, map_sub, map_sub]
        simp only [adjkdCoord_apply]
      rw [hsub, h1]
      ring
    rw [t25p_enorm_eq_tsum Rt]
    simp_rw [hcoord]
    by_cases htop : t25p_Psi d s ρ m cr a T X ω = ⊤
    · rw [htop, ENNReal.mul_top (ENNReal.ofReal_pos.2 hCr).ne']
      exact le_top
    · have hy : ∀ j : NonzeroLattice d, AEMeasurable (fun r => Real.sqrt N * modulatedEnergy
          (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (X r.toNNReal ω)
          (withDensityReal (ρ r))) (volume.restrict (Set.Ioc 0 (a + T))) := fun j =>
        (t25p_y_aemeas hd htr hT' P hF.progressive j).2 ω
      have hΨ : ∑' j : NonzeroLattice d, ENNReal.ofReal (Lattice.jp j.1 ^ (-m)) *
          ∫⁻ r in Set.Ioc 0 (a + T), ENNReal.ofReal (t25p_w cr a r) * ‖Real.sqrt N * modulatedEnergy
            (commKernel (periodicRieszGrad d s) (Torus.grad (Torus.realMode j))) (X r.toNNReal ω)
            (withDensityReal (ρ r))‖ₑ ≠ ⊤ := htop
      have := (t25p_pathwise hd htr hm hT' ha hdual hplain hCV0 (t25p_w cr a) (t25p_w_cont cr a)
        (t25p_w_pos cr a) hg (fun r => X r.toNNReal ω) hy hΨ t ht).2
      have hsd : htr.dyn.s = s := rfl
      simpa [evolvingForcingCoord, t25p_Psi, t25p_y, hsd] using this

end HRS.T25P
