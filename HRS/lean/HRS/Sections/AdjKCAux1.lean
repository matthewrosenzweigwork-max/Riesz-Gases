import HRS.Sections.AdjKSpec
import HRS.Sections.Q40bAux5
import HRS.Sections.Q40bAux3
import HRS.Sections.Q40bAux2
import HRS.Sections.MovLogAux1

/-!
# ADJKC Aux1: continuity in time of the commutator forcing along a collision-free path (packet C2)

Pure analysis: if the gradient field `Gf r`, the density `ρt r` and the configuration path `Xc r` are jointly continuous, the
gradient fields uniformly Lipschitz and the path collision free, then `r ↦ F_N^{h_r}(X_r, ρ_r)` is continuous.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjKC

variable {d N : ℕ} {s : ℝ}

/-- Parametric integral `∫ y, ρ_r(y) h_r(x,y) dy`: jointly continuous in `(r,x)` and uniformly bounded. -/
theorem adjkc_param_integral (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {Gf : ℝ → Torus d → Euc d} (hGc : Continuous fun p : ℝ × Torus d => Gf p.1 p.2)
    {L : ℝ} (hL : 0 ≤ L) (hLip : ∀ r, IsLipschitzVF L (Gf r))
    {ρt : ℝ → Torus d → ℝ} (hρc : Continuous fun p : ℝ × Torus d => ρt p.1 p.2)
    {Λ : ℝ} (hΛ : ∀ r y, |ρt r y| ≤ Λ) :
    Continuous (fun p : ℝ × Torus d =>
      ∫ y, ρt p.1 y * commKernel (periodicRieszGrad d s) (Gf p.1) p.2 y) ∧
    ∃ B : ℝ, ∀ p : ℝ × Torus d,
      |∫ y, ρt p.1 y * commKernel (periodicRieszGrad d s) (Gf p.1) p.2 y| ≤ B := by
  obtain ⟨cstar, A, hA, -, hc0, hdom⟩ := Q40b.q40b_hdom hd hs0 hsd
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hΛ 0 0)
  have hshift : ∀ p : ℝ × Torus d, ∫ y, ρt p.1 y * commKernel (periodicRieszGrad d s) (Gf p.1) p.2 y
      = ∫ z, ρt p.1 (p.2 - z) * commKernel (periodicRieszGrad d s) (Gf p.1) p.2 (p.2 - z) := fun p =>
    (integral_sub_left_eq_self (fun y => ρt p.1 y *
      commKernel (periodicRieszGrad d s) (Gf p.1) p.2 y) volume p.2).symm
  have hint : Integrable (fun z : Torus d => Λ * ((A * L) * (periodicRiesz d s z + cstar))) := by
    have := (KernelAux.integrable_periodicRiesz hd hs0 hsd).add
      (integrable_const (μ := (volume : Measure (Torus d))) cstar)
    exact (this.const_mul (A * L)).const_mul Λ
  have hbd : ∀ (p : ℝ × Torus d) (z : Torus d),
      ‖ρt p.1 (p.2 - z) * commKernel (periodicRieszGrad d s) (Gf p.1) p.2 (p.2 - z)‖ ≤
        Λ * ((A * L) * (periodicRiesz d s z + cstar)) := by
    intro p z
    rw [Real.norm_eq_abs, abs_mul]
    have h1 := hdom L (Gf p.1) hL (hLip p.1) p.2 (p.2 - z)
    rw [sub_sub_cancel] at h1
    exact mul_le_mul (hΛ _ _) h1 (abs_nonneg _) hΛ0
  refine ⟨?_, ?_⟩
  · simp_rw [hshift]
    refine continuous_of_dominated (bound := fun z => Λ * ((A * L) * (periodicRiesz d s z + cstar)))
      (fun p => ?_) (fun p => Eventually.of_forall fun z => hbd p z) hint ?_
    · have hGp : Continuous (Gf p.1) := hGc.comp (continuous_const.prodMk continuous_id)
      have hK := Q40b.q40b_commKernel_meas (s := s) hsd hGp
      have hρp : Continuous (ρt p.1) := hρc.comp (continuous_const.prodMk continuous_id)
      refine Measurable.aestronglyMeasurable ?_
      refine (hρp.measurable.comp (measurable_const.sub measurable_id)).mul ?_
      exact hK.comp (measurable_const.prodMk (measurable_const.sub measurable_id))
    · filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with z hz
      have hne : ∀ p : ℝ × Torus d, ¬ (p.2 = p.2 - z) := fun p h => hz (by
        have := sub_eq_self.1 h.symm
        exact this)
      have : (fun p : ℝ × Torus d => ρt p.1 (p.2 - z) *
          commKernel (periodicRieszGrad d s) (Gf p.1) p.2 (p.2 - z)) =
          fun p => ρt p.1 (p.2 - z) * inner ℝ (Gf p.1 p.2 - Gf p.1 (p.2 - z))
            (periodicRieszGrad d s z) := by
        funext p
        unfold commKernel
        rw [if_neg (hne p), sub_sub_cancel]
      rw [this]
      have hq : Continuous fun p : ℝ × Torus d => (p.1, p.2 - z) :=
        continuous_fst.prodMk (continuous_snd.sub continuous_const)
      exact (hρc.comp hq).mul ((hGc.sub (hGc.comp hq)).inner continuous_const)
  · refine ⟨∫ z, Λ * ((A * L) * (periodicRiesz d s z + cstar)), fun p => ?_⟩
    rw [hshift p]
    exact (norm_integral_le_of_norm_le hint (Eventually.of_forall fun z => hbd p z))


theorem adjkc_G_continuousAt (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {z : Torus d} (hz : z ≠ 0) :
    ContinuousAt (periodicRieszGrad d s) z := by
  have hsm := KernelGrad.periodicRieszGrad_smoothOffZero hd hs0 hsd
  have hopen : IsOpen {x : Euc d | Torus.mk x ≠ 0} :=
    (isOpen_ne : IsOpen {w : Torus d | w ≠ 0}).preimage KernelGrad.isOpenQuotientMap_mk.continuous
  have hr : Torus.mk (Torus.rep z) ≠ 0 := by rw [Torus.mk_rep]; exact hz
  have h1 : ContinuousAt (Torus.lift (periodicRieszGrad d s)) (Torus.rep z) :=
    (hsm.continuousOn).continuousAt (hopen.mem_nhds hr)
  have h2 : ContinuousAt (periodicRieszGrad d s ∘ (Torus.mk : Euc d → Torus d)) (Torus.rep z) := h1
  have h3 := (KernelGrad.isOpenQuotientMap_mk.continuousAt_comp_iff).mp h2
  rwa [Torus.mk_rep] at h3

/-- The modulated energy of the commutator kernel along a collision-free continuous path is continuous in time. -/
theorem adjkc_modEnergy_continuous (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d)
    {Gf : ℝ → Torus d → Euc d} (hGc : Continuous fun p : ℝ × Torus d => Gf p.1 p.2)
    {L : ℝ} (hL : 0 ≤ L) (hLip : ∀ r, IsLipschitzVF L (Gf r))
    {ρt : ℝ → Torus d → ℝ} (hρc : Continuous fun p : ℝ × Torus d => ρt p.1 p.2)
    {Λ : ℝ} (hΛ : ∀ r y, |ρt r y| ≤ Λ) (hρP : ∀ r, IsProbDensity (ρt r))
    {Xc : ℝ → Config d N} (hX : Continuous Xc) (hcol : ∀ r, ∀ i j, i ≠ j → Xc r i ≠ Xc r j) :
    Continuous fun r => modulatedEnergy (commKernel (periodicRieszGrad d s) (Gf r)) (Xc r)
      (withDensityReal (ρt r)) := by
  obtain ⟨hAc, B, hB⟩ := adjkc_param_integral hd hs0 hsd hGc hL hLip hρc hΛ
  have hform : ∀ r : ℝ, modulatedEnergy (commKernel (periodicRieszGrad d s) (Gf r)) (Xc r)
      (withDensityReal (ρt r)) =
      (1 / (2 * (N : ℝ) ^ 2)) * (∑ i, ∑ j ∈ Finset.univ.erase i,
          commKernel (periodicRieszGrad d s) (Gf r) (Xc r i) (Xc r j))
        - (1 / (N : ℝ)) * (∑ i, ∫ y, ρt r y *
          commKernel (periodicRieszGrad d s) (Gf r) (Xc r i) y)
        + (1 / 2) * ∫ x, ρt r x * ∫ y, ρt r y *
          commKernel (periodicRieszGrad d s) (Gf r) x y := by
    intro r
    unfold modulatedEnergy
    have hd' := hρP r
    simp only [PDE.MFPairing.integral_withDensityReal hd'.measurable hd'.nonneg]
  simp_rw [hform]
  have hΛ0 : 0 ≤ Λ := (abs_nonneg _).trans (hΛ 0 0)
  refine Continuous.add (Continuous.sub ?_ ?_) ?_
  · refine continuous_const.mul (continuous_finset_sum _ fun i _ => continuous_finset_sum _ fun j hj => ?_)
    have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
    refine continuous_iff_continuousAt.2 fun r0 => ?_
    have hne : ∀ r, ¬ (Xc r i = Xc r j) := fun r h => hcol r i j hij h
    have : (fun r => commKernel (periodicRieszGrad d s) (Gf r) (Xc r i) (Xc r j)) =
        fun r => inner ℝ (Gf r (Xc r i) - Gf r (Xc r j)) (periodicRieszGrad d s (Xc r i - Xc r j)) := by
      funext r
      unfold commKernel
      rw [if_neg (hne r)]
    rw [this]
    have hXi : Continuous fun r => Xc r i := (continuous_apply i).comp hX
    have hXj : Continuous fun r => Xc r j := (continuous_apply j).comp hX
    have hz : Xc r0 i - Xc r0 j ≠ 0 := sub_ne_zero.2 (hcol r0 i j hij)
    refine ContinuousAt.inner ?_ ?_
    · exact ((hGc.comp (continuous_id.prodMk hXi)).sub (hGc.comp (continuous_id.prodMk hXj))).continuousAt
    · exact (adjkc_G_continuousAt hd hs0 hsd hz).comp (f := fun r => Xc r i - Xc r j) (hXi.sub hXj).continuousAt
  · refine continuous_const.mul (continuous_finset_sum _ fun i _ => ?_)
    exact hAc.comp (continuous_id.prodMk ((continuous_apply i).comp hX))
  · refine continuous_const.mul ?_
    refine continuous_of_dominated (bound := fun _ => Λ * B) (fun r => ?_)
      (fun r => Eventually.of_forall fun x => ?_) (integrable_const _) ?_
    · have h1 : Continuous fun x => ρt r x :=
        hρc.comp (continuous_const.prodMk continuous_id)
      have h2 : Continuous fun x => ∫ y, ρt r y * commKernel (periodicRieszGrad d s) (Gf r) x y :=
        hAc.comp (continuous_const.prodMk continuous_id)
      exact (h1.mul h2).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_mul]
      exact mul_le_mul (hΛ _ _) (hB (r, x)) (abs_nonneg _) hΛ0
    · refine Eventually.of_forall fun x => ?_
      exact (hρc.comp (continuous_id.prodMk continuous_const)).mul
        (hAc.comp (continuous_id.prodMk continuous_const))

end HRS.AdjKC
