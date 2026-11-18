import HRS.Main.ThermLin2Fu9
import HRS.Main.ThermLin2Dy4

/-!
# THERMLIN2 Fu10: regularity of `ψ_r = (𝓛_r - 𝓛_β) U^{r,t} φ`

For smooth `φ` and `t > 0`: `ψ_r` is smooth, lies in `H^m` with a uniform bound (`m` arbitrary), using the
moving/frozen facts `tl2dy_moving_facts` of the packet `Dy` (wk/tl2dyson).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.ThermLin.Plan2

open HRS HRS.Uniform HRS.GF HRS.AdjK HRS.T25P HRS.Uniform.Q54c

variable {d : ℕ}

/-- A continuous function in `H^N` for all natural `N` is smooth. -/
theorem tl2fu_smooth_of_sobolev {ψ : Torus d → ℝ} (hc : Continuous ψ)
    (h : ∀ N : ℕ, MemSobolev (N : ℝ) ψ) : Torus.IsSmooth ψ := by
  have hdec : ∀ N : ℕ, PDE.MemHs (N : ℝ) (PDE.coeffOf ψ) := fun N => (PDE.hsNormSq_coeffOf _ ψ (h N)).1
  have hreal : PDE.IsRealCoeff (PDE.coeffOf ψ) :=
    PDE.isRealCoeff_coeffOf ψ (PDE.ClassicalAux.integrable_of_continuous hc)
  have hs : Summable fun k => ‖PDE.coeffOf ψ k‖ := by
    refine PDE.summable_norm_of_memHs ((d + 1 : ℕ) : ℝ) ?_ _ (hdec (d + 1))
    push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have e := PDE.MFThermalReg.toFun_coeffOf hc hs
  rw [← e]
  exact PDE.isSmooth_toFun_of_decay _ hreal hdec

open HRS.PDE HRS.PDE.MFAdjoint in
/-- Regularity of `ψ_r`: smooth, in `H^m`, uniformly bounded in `H^m`. -/
theorem tl2fu_psi_regular (S : HRS.Main.PreparedData d) {ρβ : Torus d → ℝ}
    (h : IsThermalDensity (periodicRiesz d S.s) S.V S.β ρβ) (m : ℝ)
    {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) {t : ℝ} (ht : 0 < t) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Set.Icc (0 : ℝ) t,
      Torus.IsSmooth (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) ∧
      MemSobolev m (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ)) ∧
      ‖lpFun m (tl2Delta S ρβ r (propagator S.dyn S.ρ r t φ))‖ ≤ B := by
  -- a natural number `j'` admissible for `tl2dy_moving_facts` and `≥ m`
  have hadm : ∀ n : ℕ, ∃ j' : ℕ, n ≤ j' ∧ (PDE.mStar d ≤ j') ∧ (d : ℝ) / 2 + 2 < j' := by
    intro n
    refine ⟨n + PDE.mStar d + d + 4, by omega, by omega, ?_⟩
    have : d + 4 ≤ n + PDE.mStar d + d + 4 := by omega
    have h2 : ((d + 4 : ℕ) : ℝ) ≤ ((n + PDE.mStar d + d + 4 : ℕ) : ℝ) := by exact_mod_cast this
    have h3 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    push_cast at h2 ⊢
    linarith
  obtain ⟨j', hj'm, hj'ms, hj'd⟩ := hadm ⌈m⌉₊
  have hmj : m ≤ (j' : ℝ) := by
    refine (Nat.le_ceil m).trans ?_
    exact_mod_cast hj'm
  obtain ⟨B, hB, hfacts⟩ := tl2dy_moving_facts S h j' hj'ms hj'd hφ ht
  refine ⟨B, hB, fun r hr => ?_⟩
  obtain ⟨-, -, -, hcont, -, hΔS, hΔn⟩ := hfacts r hr
  refine ⟨?_, tl2dy_memSob_mono hmj hΔS, ?_⟩
  · refine tl2fu_smooth_of_sobolev hcont fun N => ?_
    obtain ⟨j'', hj''N, hj''ms, hj''d⟩ := hadm N
    obtain ⟨_, _, hf''⟩ := tl2dy_moving_facts S h j'' hj''ms hj''d hφ ht
    obtain ⟨-, -, -, -, -, hΔS'', -⟩ := hf'' r hr
    refine tl2dy_memSob_mono ?_ hΔS''
    exact_mod_cast hj''N
  · exact (norm_lpFun_le m _).trans ((tl2dy_sobNorm_mono hmj hΔS).trans hΔn)

end HRS.ThermLin.Plan2
