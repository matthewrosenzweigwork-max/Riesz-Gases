import HRS.MS.Mov63EAux9

/-!
# S6.3, packet N6 (part 10): pointwise time derivative

Namespace `HRS.MS.Mov63`, prefix `mne_`.  See `Mov63EAux1`.  `mne_hasDeriv`, `mne_hasDerivAt`: `∂_t ρ_t(x) = div Y_t(x)` for every `x` and `t ≥ 0`
(right derivative at `t = 0`, two-sided for `t > 0`), from `mne_pointwise`; no positivity.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1 HRS.MS.MovForce HRS.MS.MovLin HRS.MH.DualityRd

variable {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ}

section Classical

variable {m : ℕ} (hm : (d : ℝ) / 2 + 3 < m) (H : Mov2dTh d s β q ρ) {v : ℝ → OscSpace d (m : ℝ)}

include H in
/-- **Pointwise time derivative** of `t ↦ ρ_t(x) = ρ(x) + √ρ(x) V_t(x)` on `[0,∞)`: it equals `div Y_t (x)`. -/
theorem mne_hasDeriv (hmild : MneMild H hm v) {t : ℝ} (ht : 0 ≤ t) (x : Euc d) :
    HasDerivWithinAt (fun τ => mneRho ρ hm (v τ) x) (movDiv (mneY d s q β ρ hm (v t)) x) (Ici 0) t := by
  have hc := mne_Ec_cont hm H hmild
  have hcx : Continuous fun σ : ℝ => mneEc d s q β ρ hm v (σ, x) := hc.comp (continuous_id.prodMk continuous_const)
  have hΦ : HasDerivAt (fun τ => mneRho ρ hm (v 0) x + ∫ σ in (0 : ℝ)..τ, mneEc d s q β ρ hm v (σ, x))
      (mneEc d s q β ρ hm v (t, x)) t := by
    have := (hcx.integral_hasStrictDerivAt 0 t).hasDerivAt
    exact this.const_add _
  have hcongr : ∀ τ ∈ Ici (0 : ℝ), mneRho ρ hm (v τ) x =
      mneRho ρ hm (v 0) x + ∫ σ in (0 : ℝ)..τ, mneEc d s q β ρ hm v (σ, x) := by
    intro τ hτ
    have := mne_pointwise hm H hmild (show 0 ≤ τ from hτ) x
    simp only [mneRho]
    linarith
  rw [← mneEc_eq hm ht x]
  exact (hΦ.hasDerivWithinAt).congr hcongr (hcongr t ht)

include H in
/-- For `t > 0` the derivative is two-sided. -/
theorem mne_hasDerivAt (hmild : MneMild H hm v) {t : ℝ} (ht : 0 < t) (x : Euc d) :
    HasDerivAt (fun τ => mneRho ρ hm (v τ) x) (movDiv (mneY d s q β ρ hm (v t)) x) t := by
  have hc := mne_Ec_cont hm H hmild
  have hcx : Continuous fun σ : ℝ => mneEc d s q β ρ hm v (σ, x) := hc.comp (continuous_id.prodMk continuous_const)
  have hΦ : HasDerivAt (fun τ => mneRho ρ hm (v 0) x + ∫ σ in (0 : ℝ)..τ, mneEc d s q β ρ hm v (σ, x))
      (mneEc d s q β ρ hm v (t, x)) t := by
    have := (hcx.integral_hasStrictDerivAt 0 t).hasDerivAt
    exact this.const_add _
  rw [← mneEc_eq hm ht.le x]
  refine hΦ.congr_of_eventuallyEq ?_
  filter_upwards [Ici_mem_nhds ht] with τ hτ
  have := mne_pointwise hm H hmild (show 0 ≤ τ from hτ) x
  simp only [mneRho]
  linarith

end Classical

end HRS.MS.Mov63

end
