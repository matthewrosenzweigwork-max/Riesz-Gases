import HRS.Commutator.Torus.TEXTAux17

/-!
# T-EXT-A helpers, part 18: `bernstein_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- Reproducing property: `a = Ψ ⋆ a` a.e. when the coefficients of `a` vanish where `Ψ̂ ≠ 1`. -/
lemma text_repro {a Ψ : Torus d → ℝ} (ha : Integrable a) (hΨ : Integrable Ψ)
    (h : ∀ k : Lattice d, Torus.fcoef Ψ k ≠ 1 → Torus.fcoef a k = 0) :
    a =ᵐ[volume] textConv Ψ a := by
  have hc := text_integrable_conv hΨ ha
  have hg : Integrable (fun x => a x - textConv Ψ a x) := ha.sub hc
  have hcoef : ∀ k, Torus.fcoef (fun x => a x - textConv Ψ a x) k = 0 := by
    intro k
    rw [text_fcoef_sub ha hc, text_fcoef_conv hΨ ha]
    by_cases hk : Torus.fcoef Ψ k = 1
    · rw [hk]; ring
    · rw [h k hk]; ring
  have := text_ae_eq_zero_of_fcoef hg hcoef
  filter_upwards [this] with x hx
  simpa [sub_eq_zero] using hx

end HRS.Commutator.TorusNote
