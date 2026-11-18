import HRS.MC.E213U10Q
import HRS.MC.S7FCF5NF6c
import HRS.MC.S7FCHA1
import HRS.MC.S7FCF5RE3b
import HRS.MC.S7UCAE

/-!
# Packet e213u10, part R: the pointwise (in `N, a, Φ`) near estimate for a prepared family

For a window start `b ≤ a`, length `L` and a particle number `N ≥ 2`, the particle and Gaussian integrals of `rsA`, `rsJ`
equal integrals of `u10_FD`, `u10_GJ` against the laws of the pairs `pairN`, `pairLim`.  Together with the mean shift
`mm` of `S7UCD5` and the law-level bounds of part Q this gives `u10_near_pointwise`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E213U10

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Plan

variable {d : ℕ} {S : PreparedData d} {β₀ m : ℝ}

/-- Second-moment transfer along an `AEMeasurable` map: if `ν ∘ f = g` a.s. with `g²` integrable of integral `≤ M`, then
`ν ∈ L²(P.map f)` with second moment `≤ M`. -/
theorem u10_moment_transfer {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) (L : ℝ) (f : Ω → U10B d L)
    (hf : AEMeasurable f P) (ν : U10B d L → ℝ) (hν : Continuous ν) (g : Ω → ℝ)
    (hae : ∀ᵐ ω ∂P, ν (f ω) = g ω) (M : ℝ) (hint : Integrable (fun ω => g ω ^ 2) P)
    (hM : ∫ ω, g ω ^ 2 ∂P ≤ M) :
    MemLp ν 2 (P.map f) ∧ ∫ x, ν x ^ 2 ∂(P.map f) ≤ M := by
  have hsm : AEStronglyMeasurable (ν ∘ f) P := hν.aestronglyMeasurable.comp_aemeasurable hf
  have hint' : Integrable (fun ω => (ν ∘ f) ω ^ 2) P := by
    refine hint.congr ?_
    filter_upwards [hae] with ω h
    simp [Function.comp, h]
  refine ⟨(memLp_map_measure_iff hν.aestronglyMeasurable hf).2 ((memLp_two_iff_integrable_sq hsm).2 hint'), ?_⟩
  rw [integral_map hf (f := fun x : U10B d L => ν x ^ 2) (hν.pow 2).aestronglyMeasurable]
  calc ∫ ω, ν (f ω) ^ 2 ∂P = ∫ ω, g ω ^ 2 ∂P := by
        refine integral_congr_ae ?_
        filter_upwards [hae] with ω h
        simp [h]
    _ ≤ M := hM

theorem u10_pairN_aemeasurable (hE : EdgeworthHyp S β₀ m) (fam : PrepFamily S β₀ hE) (L : ℝ) (hL : 0 < L) (b : ℝ)
    (hb : 0 ≤ b) (N : ℕ) (hN : 1 ≤ N) :
    AEMeasurable (pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ (fam.P N) (fam.X N)) (fam.P N) :=
  HRS.MC.Sec7.S7FCF5E.fcf5_G1_pair_aemeasurable_proof (regime S β₀ hE) (rLvl d) rfl L hL (fam.P N) hN (fam.X₀ N)
    (fam.W N) (fam.X N) (fam.hreal N hN) b hb

theorem u10_pairLim_aemeasurable (hE : EdgeworthHyp S β₀ m) (gd : GaussData S β₀ hE) (L : ℝ) (hL : 0 < L) (b : ℝ)
    (hb : 0 ≤ b) : AEMeasurable (pairLim (rLvl d) L b gd.η gd.B) gd.P₀ := by
  obtain ⟨ε₂, c, K, hK⟩ := HRS.MC.Sec7.S7FCH.S7FCHA_kernelData (regime S β₀ hE)
  exact (HRS.MC.Sec7.S7UCA.s7_UC_E4_limit_measurable_proof (regime S β₀ hE) (rLvl d) rfl L hL gd.P₀ gd.η gd.limit
    gd.B gd.B_meas b hb ∅ (fun k => K k 0)).1

theorem u10_near_pointwise (hE : EdgeworthHyp S β₀ m) (gd : GaussData S β₀ hE) (fam : PrepFamily S β₀ hE)
    (T : ℝ) (hT : 0 < T) (a : ℝ) (ha : 0 ≤ a) (Φ : PathSpace d m T → ℝ) (hΦ : MemCb 5 Φ) (hcb : cbNorm 5 Φ ≤ 1)
    (b L : ℝ) (hb : 0 ≤ b) (hba : b ≤ a) (hL : 0 < L) (hH : a + T ≤ b + L)
    (CD CJ CY : ℝ) (hCD0 : 0 ≤ CD) (hCJ0 : 0 ≤ CJ) (hCY0 : 0 ≤ CY) (hCD : U10_DriftNear hE T a ha b CD)
    (hJ : U10_JNear hE T a ha b CJ) (hCY : U10_PredBound hE T a ha CY) (N : ℕ) (hN : 2 ≤ N)
    (Mq Mf : ℝ) (hMq : 0 ≤ Mq) (hMf : 0 ≤ Mf)
    (hq : Integrable (fun ω => ‖(pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ (fam.P N) (fam.X N) ω).2‖ ^
        (2 : ℝ)) (fam.P N) ∧
      ∫ ω, ‖(pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ (fam.P N) (fam.X N) ω).2‖ ^ (2 : ℝ)
        ∂(fam.P N) ≤ Mq ^ 2)
    (hf : Integrable (fun ω => ‖HRS.Main.windowFluc (rLvl d) L b (Real.sqrt N) (fam.X N) (regime S β₀ hE).ρ ω‖ ^
        (2 : ℝ)) (fam.P N) ∧
      ∫ ω, ‖HRS.Main.windowFluc (rLvl d) L b (Real.sqrt N) (fam.X N) (regime S β₀ hE).ρ ω‖ ^ (2 : ℝ)
        ∂(fam.P N) ≤ Mf ^ 2) :
    ∃ mm : PathSpace d (rLvl d) L,
      ENNReal.ofReal ‖mm‖ ≤ wassersteinE 2
        (law (fam.P N) (HRS.Main.windowFluc (rLvl d) L b (Real.sqrt N) (fam.X N) (regime S β₀ hE).ρ))
        (law gd.P₀ (procWin (rLvl d) L b gd.η)) ∧
      |∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
          (nearCoef b (fun v => quadFieldAt m (regime S β₀ hE).D.s
            (fun t => withDensityReal ((regime S β₀ hE).ρ t)) (fam.P N) (fam.X N) v ω)) ∂(fam.P N)| ≤
        CD * Real.sqrt L * Mq ∧
      |∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
          (nearCoef b (fun v => etaE m ((fam.X N) v.toNNReal ω)
            (withDensityReal ((regime S β₀ hE).ρ v)))) ∂(fam.P N)| ≤ CJ * L * Mf ∧
      (wassersteinE 2
          (law (fam.P N) (pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ (fam.P N) (fam.X N)))
          (law gd.P₀ (pairLim (rLvl d) L b gd.η gd.B)) ≠ ⊤ →
        |∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
            (nearCoef b (fun v => quadFieldAt m (regime S β₀ hE).D.s
              (fun t => withDensityReal ((regime S β₀ hE).ρ t)) (fam.P N) (fam.X N) v ω)) ∂(fam.P N) -
          ∫ ω, rsA (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
            (nearCoef b (fun v => NegSobolev.embed m (gd.B v ω))) ∂gd.P₀| ≤
          CD * Real.sqrt L * ((CY * Mq + 1) * (wassersteinE 2
            (law (fam.P N) (pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ (fam.P N) (fam.X N)))
            (law gd.P₀ (pairLim (rLvl d) L b gd.η gd.B))).toReal) ∧
        |∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (zetaWin m (a + T) 0 (fam.P N) (fam.X N) ω)
            (nearCoef b (fun v => etaE m ((fam.X N) v.toNNReal ω)
              (withDensityReal ((regime S β₀ hE).ρ v)))) ∂(fam.P N) -
          ∫ ω, rsJ (regime S β₀ hE) m T a ha (Ucan hE T a ha Φ) (gd.Zwin (a + T) 0 ω)
            (nearCoef b (fun v => NegSobolev.embed m (gd.η v ω))) ∂gd.P₀| ≤
          CJ * L * ((CY * Mf + 1) * (wassersteinE 2
            (law (fam.P N) (pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ (fam.P N) (fam.X N)))
            (law gd.P₀ (pairLim (rLvl d) L b gd.η gd.B))).toReal + ‖mm‖)) := by
  have hN1 : 1 ≤ N := by omega
  obtain ⟨mm, hmm1, hmm2⟩ := HRS.MC.Sec7.S7UCD.s7_UC_D5_mean_window_proof (regime S β₀ hE) (rLvl d) rfl L hL
    fam.P fam.X₀ fam.W fam.X fam.hreal gd.P₀ gd.η gd.limit b hb N hN
  refine ⟨mm, hmm1, ?_⟩
  have hpm := u10_pairN_aemeasurable hE fam L hL b hb N hN1
  have hpl := u10_pairLim_aemeasurable hE gd L hL b hb
  have hFDc := u10_FD_cont hE T hT a ha Φ hΦ hcb b L hb hL.le hH CD CY hCD0 hCY0 hCD hCY
  have hGJc := u10_GJ_cont hE T hT a ha Φ hΦ hcb b L hb hL.le hH CJ CY hCJ0 hCY0 hJ hCY
  -- integral identities
  have hA1 := integral_congr_ae (u10_particle_A hE T hT a ha Φ hΦ b L hb hba hL hH hN (fam.P N) (fam.X₀ N)
    (fam.W N) (fam.X N) (fam.hreal N hN1))
  have hA1' := integral_map hpm (hFDc.aestronglyMeasurable)
  have hJ1 := integral_congr_ae (u10_particle_J hE T hT a ha Φ hΦ b L hb hba hL hH hN (fam.P N) (fam.X₀ N)
    (fam.W N) (fam.X N) (fam.hreal N hN1) mm hmm2)
  have hJ1' := integral_map hpm ((hGJc mm).aestronglyMeasurable)
  have hA2 := integral_congr_ae (u10_gauss_A hE gd T hT a ha Φ hΦ b L hb hba hL hH)
  have hA2' := integral_map hpl (hFDc.aestronglyMeasurable)
  have hJ2 := integral_congr_ae (u10_gauss_J hE gd T hT a ha Φ hΦ b L hb hba hL hH)
  have hJ2' := integral_map hpl ((hGJc 0).aestronglyMeasurable)
  -- moments
  have hν1 := u10_moment_transfer (fam.P N) L _ hpm (fun x : U10B d L => ‖x.2‖) continuous_snd.norm
    (fun ω => ‖(pairN (rLvl d) L b (regime S β₀ hE).D.s (regime S β₀ hE).ρ (fam.P N) (fam.X N) ω).2‖)
    (Filter.Eventually.of_forall fun ω => rfl) (Mq ^ 2) (by simpa only [Real.rpow_two] using hq.1)
    (by simpa only [Real.rpow_two] using hq.2)
  have hcm : Continuous fun x : U10B d L => ‖x.1 + mm‖ := (continuous_fst.add continuous_const).norm
  have hν2 := u10_moment_transfer (fam.P N) L _ hpm (fun x : U10B d L => ‖x.1 + mm‖) hcm
    (fun ω => ‖HRS.Main.windowFluc (rLvl d) L b (Real.sqrt N) (fam.X N) (regime S β₀ hE).ρ ω‖)
    (by
      filter_upwards [hmm2] with ω h
      show ‖zetaWin (rLvl d) L b (fam.P N) (fam.X N) ω + mm‖ = _
      rw [h, sub_add_cancel])
    (Mf ^ 2) (by simpa only [Real.rpow_two] using hf.1) (by simpa only [Real.rpow_two] using hf.2)
  refine ⟨?_, ?_, ?_⟩
  · rw [hA1, ← hA1']
    exact u10_FD_crude hE T hT a ha Φ hΦ hcb b L hL.le hH CD hCD0 hCD CY hCY0 hCY hb _ Mq hMq hν1.1 hν1.2
  · rw [hJ1, ← hJ1']
    exact u10_GJ_crude hE T hT a ha Φ hΦ hcb b L hL.le hH CJ hCJ0 hJ CY hCY0 hCY hb mm _ Mf hMf hν2.1 hν2.2
  · intro hW
    refine ⟨?_, ?_⟩
    · rw [hA1, hA2, ← hA1', ← hA2']
      exact u10_FD_law hE T hT a ha Φ hΦ hcb b L hb hL.le hH CD CY hCD0 hCY0 hCD hCY _ _ Mq hMq hν1.1 hν1.2 hW
    · rw [hJ1, hJ2, ← hJ1', ← hJ2']
      exact u10_GJ_law hE T hT a ha Φ hΦ hcb b L hb hL.le hH CJ CY hCJ0 hCY0 hJ hCY mm _ _ Mf hMf hν2.1 hν2.2 hW

end HRS.MC.E213U10

end
