import HRS.Main.T25PAux18

/-!
# T25P, part 19: the deterministic covariation density `C̄^r` and the integrated trace discrepancy
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.T25P

open HRS HRS.Uniform HRS.GF HRS.AdjK

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem t25p_detCov (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) {T' : ℝ} (hT' : 0 < T') :
    IsDetCovDensity T' (covDensT m β⁻¹ T' ρ) := by
  have hd1 : 1 ≤ d := by omega
  have hMF := Q40b.q40b_meanField hd1 htr hT'
  have hjc := Q40b.q40b_jointCont hd1 htr T'
  have hprob : ∀ σ ∈ Set.Icc (0 : ℝ) T', IsProbDensity (ρ σ) := fun σ hσ => hMF.density σ hσ
  have hcts : ∀ σ ∈ Set.Icc (0 : ℝ) T', Continuous (ρ σ) := fun σ hσ =>
    hjc.comp_continuous (continuous_const.prodMk continuous_id) (fun x => ⟨hσ, Set.mem_univ _⟩)
  have hweak := adjkd_weak_cont hd htr T'
  exact Q54c.isDetCovDensity_covDens hm (inv_nonneg.2 htr.hβ.le) hprob hweak hcts

theorem t25p_covDensT_zero {m q T' : ℝ} {r : ℝ} (hr : T' < r) (ρ' : ℝ → Torus d → ℝ) :
    covDensT m q T' ρ' r = 0 := by
  unfold covDensT
  rw [if_neg]
  intro h
  exact absurd h.2 (not_le.2 hr)

/-- `∫_0^{a+T} e^{-2c(a-r)_+}` weighted trace discrepancy, `E ≤ C √(B/N)`, uniformly in `a`. -/
theorem t25p_trace_int (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) + 2 < m) {cr : ℝ} (hcr : 0 < cr) {T : ℝ} (hT : 0 < T) :
    ∃ Ct : ℝ, 0 ≤ Ct ∧ ∀ N : ℕ, 2 ≤ N → ∀ a : ℝ, 0 ≤ a →
      ∀ {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
        (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N),
        IsParticleSystem P htr.dyn (a + T) X₀ W X →
        (∃ (ℱ : MeasureTheory.Filtration ℝ ‹MeasurableSpace Ω›) (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ),
          IsFilteredSolution P ℱ W' W X) →
        relEntropy (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) ≠ ⊤ →
        ∀ (ℱ : Filtration ℝ mΩ) (Mart : ℝ → Ω → NegSobolev d m),
          IsHilbertMartingaleWithCovariation P ℱ (a + T) Mart
            (fun r ω => covForm m β⁻¹ (empirical (X r.toNNReal ω))) →
          ∫⁻ ω, (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal
            (Real.exp (-cr * max (a - r) 0) ^ 2 * traceNormForm
              (covForm m β⁻¹ (empirical (X r.toNNReal ω)) - covDensT m β⁻¹ (a + T) ρ r))) ∂P ≤
            ENNReal.ofReal (Ct * Real.sqrt (entropyScale d s N (P.map X₀)
              (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / N)) := by
  classical
  obtain ⟨Ctr, hCtr0, hCtr⟩ := t25p_trace_L1 hd htr hm
  refine ⟨(1 / (2 * cr) + T) * Ctr, by positivity, ?_⟩
  intro N hN a ha Ω _ P _ X₀ W X hP hfilt hfin ℱ Mart hM
  have hT' : 0 < a + T := by linarith
  have hm1 : (d : ℝ) / 2 + 2 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hCb := t25p_detCov hd htr hm1 hT'
  set Bq : ℝ≥0∞ := ENNReal.ofReal (Ctr * Real.sqrt (entropyScale d s N (P.map X₀)
    (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / N)) with hBq
  have hFm : Measurable fun q : ℝ × Ω => ENNReal.ofReal (Real.exp (-cr * max (a - q.1) 0) ^ 2 *
      traceNormForm (covForm m β⁻¹ (empirical (X q.1.toNNReal q.2)) - covDensT m β⁻¹ (a + T) ρ q.1)) := by
    have h1 := measurable_discrepancy_density P hM hCb
    have hg : Continuous fun r : ℝ => Real.exp (-cr * max (a - r) 0) ^ 2 :=
      (Real.continuous_exp.comp (continuous_const.mul
        ((continuous_const.sub continuous_id).max continuous_const))).pow 2
    have h2 : Measurable fun q : ℝ × Ω => Real.exp (-cr * max (a - q.1) 0) ^ 2 :=
      hg.measurable.comp measurable_fst
    exact (h2.mul h1).ennreal_ofReal
  rw [← lintegral_lintegral_swap (μ := volume.restrict (Set.Icc (0 : ℝ) (a + T))) (ν := P)
    (f := fun r ω => ENNReal.ofReal (Real.exp (-cr * max (a - r) 0) ^ 2 * traceNormForm
      (covForm m β⁻¹ (empirical (X r.toNNReal ω)) - covDensT m β⁻¹ (a + T) ρ r))) hFm.aemeasurable]
  have hw2 : ∀ r, Real.exp (-cr * max (a - r) 0) ^ 2 = t25p_w (2 * cr) a r := by
    intro r
    unfold t25p_w
    rw [sq, ← Real.exp_add]
    congr 1
    ring
  have hinner : ∀ r ∈ Set.Icc (0 : ℝ) (a + T), ∫⁻ ω, ENNReal.ofReal (Real.exp (-cr * max (a - r) 0) ^ 2 *
      traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) - covDensT m β⁻¹ (a + T) ρ r)) ∂P ≤
      ENNReal.ofReal (t25p_w (2 * cr) a r) * Bq := by
    intro r hr
    have hCbr : covDensT m β⁻¹ (a + T) ρ r = covForm m β⁻¹ (withDensityReal (ρ r)) := by
      unfold covDensT; rw [if_pos hr]
    obtain ⟨ℱ', W', hF'⟩ := hfilt
    have := hCtr N hN (a + T) hT' P X₀ W X hP ⟨ℱ', W', hF'⟩ hfin r hr
    simp_rw [hCbr, hw2]
    calc ∫⁻ ω, ENNReal.ofReal (t25p_w (2 * cr) a r * traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) -
          covForm m β⁻¹ (withDensityReal (ρ r)))) ∂P
        = ∫⁻ ω, ENNReal.ofReal (t25p_w (2 * cr) a r) * ENNReal.ofReal (traceNormForm
            (covForm m β⁻¹ (empirical (X r.toNNReal ω)) - covForm m β⁻¹ (withDensityReal (ρ r)))) ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [ENNReal.ofReal_mul (t25p_w_pos _ _ _).le]
      _ = ENNReal.ofReal (t25p_w (2 * cr) a r) * ∫⁻ ω, ENNReal.ofReal (traceNormForm
            (covForm m β⁻¹ (empirical (X r.toNNReal ω)) - covForm m β⁻¹ (withDensityReal (ρ r)))) ∂P := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (t25p_w (2 * cr) a r) * Bq := mul_le_mul' le_rfl this
  calc ∫⁻ r in Set.Icc (0 : ℝ) (a + T), (∫⁻ ω, ENNReal.ofReal (Real.exp (-cr * max (a - r) 0) ^ 2 *
        traceNormForm (covForm m β⁻¹ (empirical (X r.toNNReal ω)) - covDensT m β⁻¹ (a + T) ρ r)) ∂P)
      ≤ ∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (t25p_w (2 * cr) a r) * Bq := by
        refine setLIntegral_mono' measurableSet_Icc fun r hr => hinner r hr
    _ = (∫⁻ r in Set.Icc (0 : ℝ) (a + T), ENNReal.ofReal (t25p_w (2 * cr) a r)) * Bq := by
        rw [lintegral_mul_const' _ _ (by simp [hBq])]
    _ ≤ ENNReal.ofReal (1 / (2 * cr) + T) * Bq := by
        refine mul_le_mul' ?_ le_rfl
        have h := t25p_w_lintegral_le (cr := 2 * cr) (by positivity) ha hT.le
        rw [setLIntegral_congr Ioc_ae_eq_Icc] at h
        exact h
    _ = ENNReal.ofReal ((1 / (2 * cr) + T) * Ctr * Real.sqrt (entropyScale d s N (P.map X₀)
          (modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ 0))) / N)) := by
        rw [hBq, ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

end HRS.T25P
