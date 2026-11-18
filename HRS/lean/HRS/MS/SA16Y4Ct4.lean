import HRS.MS.SA16Y4Ct3
import HRS.MS.SA16Y3Ex7

/-!
# S.A.16 (SA16Y4) Ct4: the mollification operator `R_n` on `WmpSpace d k p` (no cut-off)

`sa16y4_Rop k n`: a CLM `R : W^{k,p} → W^{k,p}` with `‖R‖ ≤ card(WIndex)` and `R (Jcc ψ) = Jcc (ρ_n ⋆ ψ)` for `ψ ∈ C_c^∞`
(extension principle, `sa16y3_mol_jet_le` for the bound).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution Phase2SA16Transfer

section Ct4
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

lemma sa16y4_mol_cc {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (n : ℕ) :
    IsCcInfty (sa16q_mol n ψ) := by
  refine ⟨?_, ?_⟩
  · exact sa16y3_conv_contDiff (sa16y_rho_integrable n).locallyIntegrable hψ
  · have h : HasCompactSupport (convolution (sa16y_rho d n) ψ (ContinuousLinearMap.lsmul ℝ ℝ)
        (volume : Measure (EuclideanSpace ℝ (Fin d)))) :=
      HasCompactSupport.convolution (μ := (volume : Measure (EuclideanSpace ℝ (Fin d))))
        (ContinuousLinearMap.lsmul ℝ ℝ) (sa16y_rho_compact (d := d) n) hψ.2
    rw [← sa16y3_conv_eq] at h
    exact h

lemma sa16y4_mol_add (n : ℕ) {ψ₁ ψ₂ : EuclideanSpace ℝ (Fin d) → ℝ} (h₁ : IsCcInfty ψ₁) (h₂ : IsCcInfty ψ₂) :
    sa16q_mol n (fun y => ψ₁ y + ψ₂ y) = fun x => sa16q_mol n ψ₁ x + sa16q_mol n ψ₂ x := by
  funext x
  unfold sa16q_mol sa16j_conv
  simp only [mul_add]
  rw [← integral_add (sa16y3_mol_integrable n h₁ x) (sa16y3_mol_integrable n h₂ x)]

lemma sa16y4_mol_smul (n : ℕ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (c : ℝ) :
    sa16q_mol n (fun y => c * ψ y) = fun x => c * sa16q_mol n ψ x := by
  funext x
  unfold sa16q_mol sa16j_conv
  rw [← integral_const_mul]
  exact integral_congr_ae (Eventually.of_forall fun z => by ring)

lemma sa16y4_mol_mem {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) (k : ℕ) (n : ℕ) :
    sa16q_mol n ψ ∈ sa16r_S d k p := by
  have hc := sa16y4_mol_cc hψ n
  exact ⟨hc.1, ⟨sa16r_Jcc d k p ⟨sa16q_mol n ψ, hc⟩, by
    rw [sa16r_Jcc_eq]; exact sa16r_cc_elt_wrep (p := p) hc k⟩⟩

def sa16y4_Rl (k : ℕ) (p : ℝ) [Fact (2 ≤ p)] (n : ℕ) : ccSub d →ₗ[ℝ] sa16r_S d k p where
  toFun ψ := ⟨sa16q_mol n ψ.1, sa16y4_mol_mem ψ.2 k n⟩
  map_add' ψ₁ ψ₂ := Subtype.ext (sa16y4_mol_add n ψ₁.2 ψ₂.2)
  map_smul' c ψ := Subtype.ext (sa16y4_mol_smul n c)

lemma sa16y4_Rl_eq (k n : ℕ) (ψ : ccSub d) :
    sa16r_J d k p (sa16y4_Rl k p n ψ) = sa16r_Jcc d k p ⟨sa16q_mol n ψ.1, sa16y4_mol_cc ψ.2 n⟩ := by
  refine sa16r_wrep_inj d k p _ _ ?_
  have h2 : wrep d k p (sa16r_Jcc d k p ⟨sa16q_mol n ψ.1, sa16y4_mol_cc ψ.2 n⟩) =ᵐ[volume] sa16q_mol n ψ.1 := by
    rw [sa16r_Jcc_eq]
    exact sa16r_cc_elt_wrep (p := p) (sa16y4_mol_cc ψ.2 n) k
  exact (sa16r_J_spec d k p (sa16y4_Rl k p n ψ)).trans h2.symm

/-- `‖J f‖ ≤ ∑_τ ‖∂^τ f‖_p` for `f ∈ C_c^∞` -/
lemma sa16y4_jet_eLp_le {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : IsCcInfty f) (k : ℕ) {p : ℝ} (hp : 1 ≤ p) :
    eLpNorm (fun x => ‖wJet k f x‖) (ENNReal.ofReal p) volume ≤
      ∑ τ : WIndex d k, eLpNorm (partialDeriv τ.2 f) (ENNReal.ofReal p) volume := by
  have hcont : Continuous (fun x => ‖wJet k f x‖) := (sa16j_jet_cont hf.1 k).norm
  have hA : ∀ x, ‖wJet k f x‖ ≤ ∑ τ : WIndex d k, ‖partialDeriv τ.2 f x‖ := by
    intro x
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun τ => ?_
    exact Finset.single_le_sum (f := fun τ : WIndex d k => ‖partialDeriv τ.2 f x‖)
      (fun _ _ => norm_nonneg _) (Finset.mem_univ τ)
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  calc eLpNorm (fun x => ‖wJet k f x‖) (ENNReal.ofReal p) volume
      ≤ eLpNorm (fun x => ∑ τ : WIndex d k, ‖partialDeriv τ.2 f x‖) (ENNReal.ofReal p) volume :=
        eLpNorm_mono_real hcont.aestronglyMeasurable (fun x => by
          rw [Real.norm_of_nonneg (norm_nonneg _)]; exact hA x)
    _ = eLpNorm (∑ τ : WIndex d k, fun x => ‖partialDeriv τ.2 f x‖) (ENNReal.ofReal p) volume := by
        congr 1; funext x; simp [Finset.sum_apply]
    _ ≤ ∑ τ : WIndex d k, eLpNorm (fun x => ‖partialDeriv τ.2 f x‖) (ENNReal.ofReal p) volume :=
        eLpNorm_sum_le hp1
    _ = ∑ τ : WIndex d k, eLpNorm (partialDeriv τ.2 f) (ENNReal.ofReal p) volume := by
        refine Finset.sum_congr rfl fun τ _ => ?_
        exact eLpNorm_norm _ (sa16s_cc_partialDeriv hf τ.2).1.continuous.aestronglyMeasurable

lemma sa16y4_pd_eLp_le_jet {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : IsCcInfty f) (k : ℕ) (τ : WIndex d k) {p : ℝ} :
    eLpNorm (partialDeriv τ.2 f) (ENNReal.ofReal p) volume ≤
      eLpNorm (fun x => ‖wJet k f x‖) (ENNReal.ofReal p) volume := by
  have hτm : (τ.1 : ℕ) ≤ k := Nat.lt_succ_iff.mp τ.1.isLt
  refine eLpNorm_mono_real (sa16s_cc_partialDeriv hf τ.2).1.continuous.aestronglyMeasurable (fun x => ?_)
  have := sa16j_pd_le_jet k f x hτm τ.2
  simpa [Real.norm_eq_abs] using this

end Ct4

end HRS.Whole.AppendixA.Phase2SA16R
