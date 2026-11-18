import HRS.Main.ThermLin2Fu10

/-!
# THERMLIN2 Fu11: measurability in `r` of the Fourier coefficients of the forward generators along `F(t-r)`

* `tl2fu_forwardGen_ae`: `r ↦ (𝓛^{ρ_r} F(t-r))^(k)` is a.e.-measurable (it is integrable: `IsForwardSolution`);
* `tl2fu_frozen_gen_cont`: `r ↦ (𝓛^{ρ_β} F(t-r))^(k)` is continuous when `F ∈ C([0,t];H^{q+2})`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c

variable {d : ℕ}

open HRS.PDE HRS.PDE.MFAdjoint in
theorem tl2fu_forwardGen_ae {D : DynData d} {μ : ℝ → Torus d → ℝ} {t : ℝ} (ht : 0 ≤ t) {φc : Coeff d}
    {F : ℝ → Coeff d} (hF : IsForwardSolution D μ t φc F) (k : Lattice d) :
    AEMeasurable (fun r => forwardGen D (μ r) (F (t - r)) k) (volume.restrict (Set.Icc (0 : ℝ) t)) := by
  have hI : IntervalIntegrable (fun σ => forwardGen D (μ (t - σ)) (F σ) k) volume 0 t :=
    (intervalIntegrable_iff_integrableOn_Icc_of_le ht).2 (hF.integrable k)
  have h2 := (hI.comp_sub_left t).symm
  simp only [sub_self, sub_zero, sub_sub_cancel] at h2
  have h3 : IntervalIntegrable (fun r => forwardGen D (μ r) (F (t - r)) k) volume 0 t := h2
  exact ((intervalIntegrable_iff_integrableOn_Icc_of_le ht).1 h3).aestronglyMeasurable.aemeasurable

open HRS.PDE HRS.PDE.MFAdjoint in
theorem tl2fu_frozen_gen_cont (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {R : Regime} {MB Λ VB : ℝ}
    {D : DynData d} {ν₀ T : ℝ} {ρβ : Torus d → ℝ} (q : ℕ)
    (hA : AdjointData s q R MB Λ VB D ν₀ T (fun _ => ρβ)) {t : ℝ}
    {F : ℝ → Coeff d} (hFc : ContinuousInHs ((q + 2 : ℕ) : ℝ) F t) (k : Lattice d) :
    ContinuousOn (fun r => forwardGen D ρβ (F (t - r)) k) (Set.Icc (0 : ℝ) t) := by
  obtain ⟨c, hc, hgen⟩ := forwardGen_hsNorm_le hd hs0 hsd q MB Λ VB D hA.hs hA.hM hA.hV
  have hr0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hA.hT.le⟩
  have hprob := hA.hμ.prob 0 hr0
  have hsm := hA.hμ.smooth 0 hr0
  have hbd := hA.hμ.bound 0 hr0
  have hlin := fun {u v : Coeff d} (hu : MemHs 1 u) (hv : MemHs 1 v) => StabAux.forwardGen_sub_adj hd hA hr0 hu hv
  intro r₀ hr₀
  have hτ₀ : t - r₀ ∈ Set.Icc (0 : ℝ) t := ⟨by linarith [hr₀.2], by linarith [hr₀.1]⟩
  have hmaps : Set.MapsTo (fun r : ℝ => t - r) (Set.Icc 0 t) (Set.Icc 0 t) :=
    fun r hr => ⟨by linarith [hr.2], by linarith [hr.1]⟩
  have hcw : ContinuousWithinAt (fun r : ℝ => t - r) (Set.Icc 0 t) r₀ :=
    (continuous_const.sub continuous_id).continuousWithinAt
  have htend := (hFc.2 (t - r₀) hτ₀).comp (hcw.tendsto_nhdsWithin hmaps)
  have hmem1 : ∀ τ ∈ Set.Icc (0 : ℝ) t, MemHs 1 (F τ) := fun τ hτ =>
    (hFc.1 τ hτ).mono (by push_cast; have : (0 : ℝ) ≤ q := Nat.cast_nonneg q; linarith)
  rw [ContinuousWithinAt, tendsto_iff_norm_sub_tendsto_zero]
  refine squeeze_zero' (Eventually.of_forall fun _ => norm_nonneg _) ?_
    (by simpa using htend.const_mul c)
  refine eventually_nhdsWithin_of_forall fun r hr => ?_
  have hrτ : t - r ∈ Set.Icc (0 : ℝ) t := hmaps hr
  have e1 := hlin (hmem1 _ hrτ) (hmem1 _ hτ₀)
  have hsub : MemHs ((q + 2 : ℕ) : ℝ) (F (t - r) - F (t - r₀)) := memHs_sub (hFc.1 _ hrτ) (hFc.1 _ hτ₀)
  obtain ⟨hm1, hm2⟩ := hgen ρβ hprob hsm hbd _ hsub
  have hdiff : forwardGen D ρβ (F (t - r)) k - forwardGen D ρβ (F (t - r₀)) k =
      forwardGen D ρβ (F (t - r) - F (t - r₀)) k := by
    rw [e1]; rfl
  show ‖forwardGen D ρβ (F (t - r)) k - forwardGen D ρβ (F (t - r₀)) k‖ ≤ _
  rw [hdiff]
  push_cast at hm2
  exact (norm_coeff_le_hsNorm_of_nonneg (Nat.cast_nonneg q) hm1 k).trans hm2

end HRS.ThermLin.Plan2
