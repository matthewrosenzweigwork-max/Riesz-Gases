import HRS.MS.SA12K11

/-!
# S.A.12 C1, bookkeeping: reversed density path, shifted potential, nonnegativity
-/

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option linter.unusedVariables false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MS.ToriCoefA HRS.MS.ToriCoefB HRS.MS.ToriConv

variable {d : ℕ}

/-- The reversed, clamped path `τ ↦ ρ (max (t - τ) 0)` keeps the coefficient hypothesis on `[0,T]`. -/
theorem sa12k_rev_hyp {s : ℝ} {m : ℕ} {Λ T : ℝ} {ρ : ℝ → Euc d → ℝ} (hρ : CoeffHypRd s m Λ T ρ)
    {t : ℝ} (ht : t ∈ Ioc (0 : ℝ) T) :
    CoeffHypRd s m Λ T (fun τ => ρ (max (t - τ) 0)) := by
  have hmem : ∀ τ ∈ Icc (0 : ℝ) T, max (t - τ) 0 ∈ Icc (0 : ℝ) T := fun τ hτ =>
    ⟨le_max_right _ _, max_le (by linarith [ht.2, hτ.1]) (by linarith [ht.1, ht.2])⟩
  obtain ⟨h1, h2⟩ := hρ.regular
  refine ⟨fun τ hτ => hρ.prob _ (hmem τ hτ), ⟨fun τ hτ => h1 _ (hmem τ hτ),
    fun hs τ hτ x => h2 hs _ (hmem τ hτ) x⟩, fun ψ hψ hb => ?_⟩
  have hc : Continuous (fun r : ℝ => max (t - r) 0) := by fun_prop
  exact (hρ.cont ψ hψ hb).comp hc.continuousOn (fun r hr => hmem r hr)

theorem sa12k_grad_shift (V : Euc d → ℝ) (c : ℝ) :
    gradient (fun x => V x - c) = gradient V := by
  funext x
  unfold gradient
  rw [fderiv_sub_const]

/-- Shifting the potential by a constant keeps `VHypRd` and makes the value at `0` vanish. -/
theorem sa12k_shift_hyp {mV : ℕ} {ΛV G₀ : ℝ} {V : Euc d → ℝ} (hV : VHypRd mV ΛV G₀ V) :
    VHypRd mV ΛV G₀ (fun x => V x - V 0) := by
  refine ⟨hV.1.sub contDiff_const, fun j hj hjm x => ?_, ?_⟩
  · have hc : ContDiffAt ℝ (j : WithTop ℕ∞) V x :=
      (hV.1.of_le (by exact_mod_cast le_top)).contDiffAt
    have h := iteratedFDeriv_sub_apply (𝕜 := ℝ) (f := V) (g := fun _ : Euc d => V 0) (i := j) (x := x)
      hc contDiffAt_const
    have e : (fun x => V x - V 0) = V - fun _ => V 0 := rfl
    rw [e, h, iteratedFDeriv_const_of_ne (by omega : j ≠ 0)]
    simpa using hV.2.1 j hj hjm x
  · rw [sa12k_grad_shift]; exact hV.2.2

theorem sa12k_moll_nonneg {δ : ℝ} {η : Euc d → ℝ} (hη : SA12KMoll δ η) {f : Euc d → ℝ}
    (hf : ∀ y, 0 ≤ f y) (x : Euc d) : 0 ≤ sa12k_moll η f x := by
  unfold sa12k_moll
  exact integral_nonneg fun u => by
    show 0 ≤ η u • f (x - u)
    rw [smul_eq_mul]; exact mul_nonneg (hη.nonneg u) (hf _)

theorem sa12k_perL_nonneg (L : ℝ) {f : Euc d → ℝ} (hf : ∀ y, 0 ≤ f y) (x : Euc d) :
    0 ≤ perL L f x := tsum_nonneg fun z => hf _

end HRS.MH.AdjointRd.Phase2SA12Construction
