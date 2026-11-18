import HRS.Sections.Sec5
import HRS.Stochastic.DualityProof
import HRS.Stochastic.BDG
import HRS.Sections.Q40bAux3

/-!
# Packet Q40b, part 5: joint measurability and Fubini for the commutator forcing

`Fm F ρ X r ω = F_N^{h_{∇F^r}}(X^r(ω), μ^r)`.  Joint measurability in `(r,ω)` (the particle path is
progressively measurable, `F` is jointly continuous with its derivatives, `ρ` is jointly continuous),
and the integrability on `(0,t] × Ω` from an `L¹(P)` bound uniform in `r`.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section
namespace HRS.Q40b

variable {d N : ℕ} {s : ℝ}

/-- The commutator forcing at time `r`: `F_N^{h_{∇F^r}}(X^r, μ^r)`. -/
def Fm (d : ℕ) (s : ℝ) {Ω : Type*} {N : ℕ} (F ρ : ℝ → Torus d → ℝ) (X : ℝ≥0 → Ω → Config d N)
    (r : ℝ) (ω : Ω) : ℝ :=
  modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad (F r))) (X r.toNNReal ω)
    (withDensityReal (ρ r))


section Meas

variable {t : ℝ} {F ft ρ : ℝ → Torus d → ℝ}

theorem q40b_rho_clamp_meas (ht : 0 ≤ t)
    (hρJ : ContinuousOn (fun p : ℝ × Torus d => ρ p.1 p.2) (Set.Icc 0 t ×ˢ Set.univ)) :
    Measurable (fun q : ℝ × Torus d => ρ (clampTI t q.1) q.2) := by
  have hq : Continuous fun q : ℝ × Torus d => (clampTI t q.1, q.2) :=
    ((continuous_clampTI t).comp continuous_fst).prodMk continuous_snd
  exact (ContinuousOn.comp_continuous hρJ hq
    (fun q => ⟨clampTI_mem ht q.1, Set.mem_univ _⟩)).measurable

theorem q40b_K_meas (ht : 0 ≤ t) (hsd : s < d) (hF : IsC12Test t F ft) :
    Measurable (fun q : ℝ × Torus d × Torus d =>
      commKernel (periodicRieszGrad d s) (Torus.grad (F (clampTI t q.1))) q.2.1 q.2.2) := by
  have hA := measurable_grad_clamp ht hF
  unfold commKernel
  refine Measurable.ite (measurableSet_eq_fun (measurable_fst.comp measurable_snd)
    (measurable_snd.comp measurable_snd)) measurable_const ?_
  refine Measurable.inner ?_ ?_
  · exact (hA.comp (measurable_fst.prodMk (measurable_fst.comp measurable_snd))).sub
      (hA.comp (measurable_fst.prodMk (measurable_snd.comp measurable_snd)))
  · exact (KernelGrad.measurable_periodicRieszGrad hsd).comp
      ((measurable_fst.comp measurable_snd).sub (measurable_snd.comp measurable_snd))


theorem q40b_Psi_meas (ht : 0 ≤ t) (hsd : s < d) (hF : IsC12Test t F ft)
    (hρJ : ContinuousOn (fun p : ℝ × Torus d => ρ p.1 p.2) (Set.Icc 0 t ×ˢ Set.univ))
    (hρP : ∀ r ∈ Set.Icc 0 t, IsProbDensity (ρ r)) :
    Measurable (fun p : ℝ × Config d N =>
      modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad (F (clampTI t p.1)))) p.2
        (withDensityReal (ρ (clampTI t p.1)))) := by
  have hK := q40b_K_meas ht hsd hF
  have hρc := q40b_rho_clamp_meas ht hρJ
  have hdens : ∀ r : ℝ, IsProbDensity (ρ (clampTI t r)) := fun r => hρP _ (clampTI_mem ht r)
  have hform : ∀ p : ℝ × Config d N,
      modulatedEnergy (commKernel (periodicRieszGrad d s) (Torus.grad (F (clampTI t p.1)))) p.2
        (withDensityReal (ρ (clampTI t p.1))) =
      (1 / (2 * (N : ℝ) ^ 2)) * (∑ i, ∑ j ∈ Finset.univ.erase i,
          commKernel (periodicRieszGrad d s) (Torus.grad (F (clampTI t p.1))) (p.2 i) (p.2 j))
        - (1 / (N : ℝ)) * (∑ i, ∫ y, ρ (clampTI t p.1) y *
          commKernel (periodicRieszGrad d s) (Torus.grad (F (clampTI t p.1))) (p.2 i) y)
        + (1 / 2) * ∫ x, ρ (clampTI t p.1) x * ∫ y, ρ (clampTI t p.1) y *
          commKernel (periodicRieszGrad d s) (Torus.grad (F (clampTI t p.1))) x y := by
    intro p
    unfold modulatedEnergy
    have hd := hdens p.1
    simp only [PDE.MFPairing.integral_withDensityReal hd.measurable hd.nonneg]
  simp_rw [hform]
  refine Measurable.add (Measurable.sub ?_ ?_) ?_
  · refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => Finset.measurable_sum _ fun j _ => ?_) _
    have hmap : Measurable (fun p : ℝ × Config d N => (p.1, (p.2 i, p.2 j))) := by fun_prop
    exact hK.comp hmap
  · refine Measurable.const_mul (Finset.measurable_sum _ fun i _ => ?_) _
    have hf : StronglyMeasurable (fun q : (ℝ × Config d N) × Torus d =>
        ρ (clampTI t q.1.1) q.2 * commKernel (periodicRieszGrad d s)
          (Torus.grad (F (clampTI t q.1.1))) (q.1.2 i) q.2) := by
      refine Measurable.stronglyMeasurable ?_
      refine Measurable.mul (hρc.comp (measurable_fst.comp measurable_fst |>.prodMk measurable_snd)) ?_
      have hmap : Measurable (fun q : (ℝ × Config d N) × Torus d => (q.1.1, (q.1.2 i, q.2))) := by
        fun_prop
      exact hK.comp hmap
    exact (hf.integral_prod_right' (ν := volume)).measurable
  · refine Measurable.const_mul ?_ _
    have hin : StronglyMeasurable (fun u : ℝ × Torus d => ∫ y, ρ (clampTI t u.1) y *
        commKernel (periodicRieszGrad d s) (Torus.grad (F (clampTI t u.1))) u.2 y) := by
      have hf : StronglyMeasurable (fun q : (ℝ × Torus d) × Torus d =>
          ρ (clampTI t q.1.1) q.2 * commKernel (periodicRieszGrad d s)
            (Torus.grad (F (clampTI t q.1.1))) q.1.2 q.2) := by
        refine Measurable.stronglyMeasurable ?_
        refine Measurable.mul (hρc.comp (measurable_fst.comp measurable_fst |>.prodMk measurable_snd)) ?_
        exact hK.comp ((measurable_fst.comp measurable_fst).prodMk
          ((measurable_snd.comp measurable_fst).prodMk measurable_snd))
      exact hf.integral_prod_right' (ν := volume)
    have hf2 : StronglyMeasurable (fun q : (ℝ × Config d N) × Torus d =>
        ρ (clampTI t q.1.1) q.2 * ∫ y, ρ (clampTI t q.1.1) y *
          commKernel (periodicRieszGrad d s) (Torus.grad (F (clampTI t q.1.1))) q.2 y) := by
      refine StronglyMeasurable.mul ?_ ?_
      · exact (hρc.comp (measurable_fst.comp measurable_fst |>.prodMk measurable_snd)).stronglyMeasurable
      · exact hin.comp_measurable ((measurable_fst.comp measurable_fst).prodMk measurable_snd)
    exact (hf2.integral_prod_right' (ν := volume)).measurable

end Meas


section Fubini

variable {Ω : Type*} {mΩ : MeasurableSpace Ω}

theorem toNNReal_clampTI (t r : ℝ) : (clampTI t r).toNNReal = (min r t).toNNReal := by
  unfold clampTI
  rcases le_total 0 (min r t) with h | h
  · rw [max_eq_right h]
  · rw [max_eq_left h, Real.toNNReal_of_nonpos h, Real.toNNReal_zero]

theorem q40b_integrable_prod {P : Measure Ω} [IsProbabilityMeasure P] {t : ℝ} (ht : 0 ≤ t)
    {H : ℝ → Ω → ℝ} (hm : Measurable (fun p : ℝ × Ω => H (clampTI t p.1) p.2))
    {K : ℝ≥0∞} (hK : K ≠ ⊤) (hbd : ∀ r ∈ Set.Ioc 0 t, ∫⁻ ω, ‖H r ω‖ₑ ∂P ≤ K) :
    Integrable (fun p : ℝ × Ω => H p.1 p.2) ((volume.restrict (Set.Ioc 0 t)).prod P) := by
  have hμ : (volume.restrict (Set.Ioc (0 : ℝ) t)) = (volume.restrict (Set.Ioc (0 : ℝ) t)) := rfl
  have hae : (fun p : ℝ × Ω => H p.1 p.2) =ᵐ[(volume.restrict (Set.Ioc 0 t)).prod P]
      (fun p : ℝ × Ω => H (clampTI t p.1) p.2) := by
    have h1 : ∀ᵐ r ∂(volume.restrict (Set.Ioc (0 : ℝ) t)), r ∈ Set.Ioc 0 t :=
      ae_restrict_mem measurableSet_Ioc
    have h2 : ∀ᵐ p ∂((volume.restrict (Set.Ioc (0 : ℝ) t)).prod P), p.1 ∈ Set.Ioc 0 t :=
      Measure.QuasiMeasurePreserving.ae (Measure.quasiMeasurePreserving_fst) h1
    filter_upwards [h2] with p hp
    rw [clampTI_of_mem ⟨hp.1.le, hp.2⟩]
  refine Integrable.congr ?_ hae.symm
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  unfold HasFiniteIntegral
  have hmeas : Measurable (fun p : ℝ × Ω => ‖H (clampTI t p.1) p.2‖ₑ) := hm.enorm
  rw [lintegral_prod _ hmeas.aemeasurable]
  calc ∫⁻ r, ∫⁻ ω, ‖H (clampTI t r) ω‖ₑ ∂P ∂(volume.restrict (Set.Ioc 0 t))
      ≤ ∫⁻ r, K ∂(volume.restrict (Set.Ioc 0 t)) := by
        refine lintegral_mono_ae ?_
        filter_upwards [ae_restrict_mem measurableSet_Ioc] with r hr
        rw [clampTI_of_mem ⟨hr.1.le, hr.2⟩]
        exact hbd r hr
    _ < ⊤ := by
        rw [lintegral_const, Measure.restrict_apply_univ, Real.volume_Ioc]
        exact ENNReal.mul_lt_top hK.lt_top (by simp)

end Fubini

section FmMeas

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {t : ℝ} {F ft ρ : ℝ → Torus d → ℝ}
  {X : ℝ≥0 → Ω → Config d N}

theorem q40b_Fm_meas {ℱ : Filtration ℝ mΩ} (ht : 0 ≤ t) (hsd : s < d) (hF : IsC12Test t F ft)
    (hρJ : ContinuousOn (fun p : ℝ × Torus d => ρ p.1 p.2) (Set.Icc 0 t ×ˢ Set.univ))
    (hρP : ∀ r ∈ Set.Icc 0 t, IsProbDensity (ρ r))
    (hX : IsProgressive ℱ (ofNNRealTime X)) :
    Measurable (fun p : ℝ × Ω => Fm d s F ρ X (clampTI t p.1) p.2) := by
  have hΨ := q40b_Psi_meas (N := N) ht hsd hF hρJ hρP
  have hu : Measurable (fun p : ℝ × Ω => X (clampTI t p.1).toNNReal p.2) := by
    have h2 : (fun p : ℝ × Ω => X (clampTI t p.1).toNNReal p.2) =
        fun p => ofNNRealTime X (min p.1 t) p.2 := by
      funext p
      simp only [ofNNRealTime_apply, toNNReal_clampTI]
    rw [h2]
    exact isProgressive_measurable_uncurry_min hX t
  have h3 := hΨ.comp (measurable_fst.prodMk hu)
  exact h3

end FmMeas

end HRS.Q40b
