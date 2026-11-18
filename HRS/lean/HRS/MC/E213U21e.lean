import HRS.MC.E213U21d

/-!
# Packet e213u21 (part e): integrability of the near parts of the particle Riemann--Stieltjes integrals

The near drift (resp. covariance) integral is, a.s., the value of the continuous functional `u10_FD` (resp. `u10_GJ`) at the
pair `pairN`; the functional is dominated by `CD √L ‖x.2‖` (resp. `CJ L ‖x.1 + mm‖`) and the pair has finite second
moments, hence integrability.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213U21

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan HRS.MC.E213U10

variable {d : ℕ}

/-- A nonnegative function with integrable square is integrable on a finite measure. -/
theorem u21_integrable_of_sq {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsFiniteMeasure P] (f : Ω → ℝ)
    (hf : AEStronglyMeasurable f P) (hsq : Integrable (fun ω => ‖f ω‖ ^ (2 : ℝ)) P) : Integrable f P := by
  refine ((integrable_const (1 : ℝ)).add hsq).mono' hf (Eventually.of_forall fun ω => ?_)
  have h0 : 0 ≤ ‖f ω‖ := norm_nonneg _
  show ‖f ω‖ ≤ 1 + ‖f ω‖ ^ (2 : ℝ)
  rw [Real.rpow_two]
  nlinarith [sq_nonneg (‖f ω‖ - 1)]

section Particle

variable {S : PreparedData d} {β₀ m : ℝ}

theorem u21_near_int_A (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 5) (b L : ℝ) (hb : 0 ≤ b) (hba : b ≤ a)
    (hL : 0 < L) (hH : a + T ≤ b + L) (CD CY : ℝ) (hCD0 : 0 ≤ CD) (hCY0 : 0 ≤ CY)
    (hCD : U10_DriftNear hE T a ha b CD) (hCY : U10_PredBound hE T a ha CY)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization (regime S β₀ hE).D P
      (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
        (withDensityReal (regime S β₀ hE).ρ₀)) X₀ W X)
    (hq : Integrable (fun ω => ‖(pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ P X ω).2‖ ^ (2 : ℝ)) P) :
    Integrable (fun ω => rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
        (nearCoef b (fun v => quadFieldAt m (regime S β₀ hE).D.s
          (fun t => withDensityReal ((regime S β₀ hE).ρ t)) P X v ω))) P := by
  have hΦ1 : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have hcb : cbNorm 5 Φ ≤ 1 := hΦ.2.2
  have hpm := HRS.MC.Sec7.S7FCF5E.fcf5_G1_pair_aemeasurable_proof (regime S β₀ hE) (rLvl d) rfl L hL P
    (by omega) X₀ W X hreal b hb
  have hFDc := u10_FD_cont hE T hT a ha Φ hΦ1 hcb b L hb hL.le hH CD CY hCD0 hCY0 hCD hCY
  have hA1 := u10_particle_A hE T hT a ha Φ hΦ1 b L hb hba hL hH hN P X₀ W X hreal
  have hfm : AEStronglyMeasurable (fun ω => ‖(pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ P X ω).2‖) P :=
    (continuous_snd.norm).aestronglyMeasurable.comp_aemeasurable hpm
  have hf1 := u21_integrable_of_sq P _ hfm (by simpa only [norm_norm] using hq)
  have hmeas : AEStronglyMeasurable (fun ω => u10_FD hE T a ha Φ b L hL.le hH
      (pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ P X ω)) P :=
    hFDc.aestronglyMeasurable.comp_aemeasurable hpm
  have hint : Integrable (fun ω => u10_FD hE T a ha Φ b L hL.le hH
      (pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ P X ω)) P := by
    refine (hf1.const_mul (CD * Real.sqrt L)).mono' hmeas (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact u10_FD_abs_le hE T hT a ha Φ hΦ1 hcb b L hL.le hH CD hCD0 hCD _
  exact hint.congr (hA1.mono fun ω h => h.symm)

theorem u21_near_int_J (hE : EdgeworthHyp S β₀ m) (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a)
    (Φ : PathSpace d m T → ℝ) (hΦ : Φ ∈ CbUnitBall (PathSpace d m T) 5) (b L : ℝ) (hb : 0 ≤ b) (hba : b ≤ a)
    (hL : 0 < L) (hH : a + T ≤ b + L) (CJ CY : ℝ) (hCJ0 : 0 ≤ CJ) (hCY0 : 0 ≤ CY)
    (hJ : U10_JNear hE T a ha b CJ) (hCY : U10_PredBound hE T a ha CY)
    {N : ℕ} (hN : 2 ≤ N) {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N)
    (hreal : PreparedRealization (regime S β₀ hE).D P
      (modulatedGibbs (periodicRiesz d (regime S β₀ hE).D.s) N (regime S β₀ hE).β₀
        (withDensityReal (regime S β₀ hE).ρ₀)) X₀ W X)
    (mm : PathSpace d (rLvl d) L)
    (hmm : ∀ᵐ ω ∂P, zetaWin (rLvl d) L b P X ω =
      HRS.Main.windowFluc (rLvl d) L b (Real.sqrt N) X (regime S β₀ hE).ρ ω - mm)
    (hf : Integrable (fun ω => ‖HRS.Main.windowFluc (rLvl d) L b (Real.sqrt N) X (regime S β₀ hE).ρ ω‖ ^ (2 : ℝ)) P) :
    Integrable (fun ω => rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 P X ω)
        (nearCoef b (fun v => etaE m (X v.toNNReal ω) (withDensityReal ((regime S β₀ hE).ρ v))))) P := by
  have hΦ1 : MemCb 5 Φ := ⟨hΦ.1, hΦ.2.1⟩
  have hcb : cbNorm 5 Φ ≤ 1 := hΦ.2.2
  have hpm := HRS.MC.Sec7.S7FCF5E.fcf5_G1_pair_aemeasurable_proof (regime S β₀ hE) (rLvl d) rfl L hL P
    (by omega) X₀ W X hreal b hb
  have hGJc := u10_GJ_cont hE T hT a ha Φ hΦ1 hcb b L hb hL.le hH CJ CY hCJ0 hCY0 hJ hCY mm
  have hJ1 := u10_particle_J hE T hT a ha Φ hΦ1 b L hb hba hL hH hN P X₀ W X hreal mm hmm
  have hcm : Continuous fun x : U10B d L => ‖x.1 + mm‖ := (continuous_fst.add continuous_const).norm
  have hfm : AEStronglyMeasurable (fun ω => ‖(pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ P X ω).1 + mm‖) P :=
    hcm.aestronglyMeasurable.comp_aemeasurable hpm
  have hfeq : ∀ᵐ ω ∂P, ‖(pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ P X ω).1 + mm‖ =
      ‖HRS.Main.windowFluc (rLvl d) L b (Real.sqrt N) X (regime S β₀ hE).ρ ω‖ := by
    filter_upwards [hmm] with ω h
    show ‖zetaWin (rLvl d) L b P X ω + mm‖ = _
    rw [h, sub_add_cancel]
  have hf1 : Integrable (fun ω => ‖(pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ P X ω).1 + mm‖) P := by
    refine u21_integrable_of_sq P _ hfm ?_
    refine hf.congr ?_
    filter_upwards [hfeq] with ω h
    simp only [norm_norm, h]
  have hmeas : AEStronglyMeasurable (fun ω => u10_GJ hE T a ha Φ b L hL.le hH mm
      (pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ P X ω)) P :=
    hGJc.aestronglyMeasurable.comp_aemeasurable hpm
  have hint : Integrable (fun ω => u10_GJ hE T a ha Φ b L hL.le hH mm
      (pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ P X ω)) P := by
    refine (hf1.const_mul (CJ * L)).mono' hmeas (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs]
    exact u10_FJ_abs_le hE T hT a ha Φ hΦ1 hcb b L hb hL.le hH CJ hCJ0 hJ _
  exact hint.congr (hJ1.mono fun ω h => h.symm)

end Particle

end HRS.MC.E213U21

end
