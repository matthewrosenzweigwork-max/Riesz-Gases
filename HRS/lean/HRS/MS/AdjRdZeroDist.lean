import HRS.MS.AdjRdNorms
import HRS.MS.AdjRdWeakTerm
import HRS.MS.AdjRdInitialZero

/-!
# S.A.12 U2c: a zero-datum weak solution of bounded `H¹_uloc` norm is an S.A.33 distributional solution
-/

set_option autoImplicit false

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.SA12BD

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

theorem sa12_zero_forward_dist (d : ℕ) (hd : 1 ≤ d) (s : ℝ)
    (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (MB Λ ΛV G₀ νbar T : ℝ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ)
    (D : WholeDyn d) (μ : ℝ → Euc d → ℝ)
    (hD : AdjointRdData s m MB Λ ΛV G₀ νbar D T μ)
    (t : ℝ) (ht : t ∈ Set.Ioc (0 : ℝ) T) (F : ℝ → Euc d → ℝ)
    (hF : IsForwardSolutionRd (D.coeff μ) t (fun _ => 0) F)
    (hb : IsUlBounded χ 1 t F) :
    IsForwardDistSolutionW D μ t F := by
  obtain ⟨B, hB⟩ := hb
  have hfin : ∀ τ ∈ Set.Icc (0 : ℝ) t, ulocNormE 0 χ (F τ) < ⊤ := fun τ hτ =>
    lt_of_le_of_lt ((sa12_uloc_mono d 1 0 (by norm_num) χ (F τ)).trans (hB τ hτ))
      ENNReal.ofReal_lt_top
  have h0t : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht.1.le⟩
  have hinit : F 0 =ᵐ[volume] 0 :=
    sa12_initial_zero d hd χ hχ (D.coeff μ) t ht.1.le F hF (hfin 0 h0t)
  have hbridge : ∀ ψ : Euc d → ℝ, IsCcInfty ψ → ∀ σ ∈ Set.Icc (0 : ℝ) t,
      forwardWeakTerm (D.coeff μ) t F ψ σ = forwardPairing D μ t σ (F σ) ψ := fun ψ hψ σ hσ =>
    sa12_weak_term_bridge d hd s hs0 hsd m hm MB Λ ΛV G₀ νbar T χ hχ D μ hD t ht ψ hψ F σ hσ
      (hfin σ hσ)
  refine ⟨hinit, ?_, ?_⟩
  · intro ψ hψ hψc
    have hI := hF.integrable_σ ψ ⟨hψ, hψc⟩
    refine hI.congr_fun (fun σ hσ => ?_) measurableSet_Icc
    exact hbridge ψ ⟨hψ, hψc⟩ σ hσ
  · intro ψ hψ hψc τ hτ
    have hτt : Set.Icc (0 : ℝ) τ ⊆ Set.Icc (0 : ℝ) t := Set.Icc_subset_Icc_right hτ.2
    have q := hF.eq ψ ⟨hψ, hψc⟩ τ hτ
    have e0 : ∫ x, F 0 x * ψ x = 0 := by
      have : (fun x => F 0 x * ψ x) =ᵐ[volume] fun _ => 0 := by
        filter_upwards [hinit] with x hx
        simp [hx]
      rw [integral_congr_ae this]; simp
    rw [e0, zero_add]
    simp only [zero_mul, integral_zero, zero_add] at q
    rw [q]
    exact setIntegral_congr_fun measurableSet_Icc fun σ hσ =>
      hbridge ψ ⟨hψ, hψc⟩ σ (hτt hσ)

end HRS.MS.SA12BD
