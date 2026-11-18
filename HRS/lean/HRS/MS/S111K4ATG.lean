import HRS.MS.S111K4ATD
import HRS.MS.S111K4ATF

/-!
# S11.1 / all-tests boundary (S111K4AT), piece G: the covariance envelope

`k4at_jets`: uniform jet control of `U^{s,t}φ` and of `U^{s,t}(φ_n) - U^{s,t}φ` (orbit approximation).  `k4at_cov_envelope`: the pairing
`z s ⟨∇U^{s,Ta}φ_n, ∇U^{s,Tb}ψ_n⟩` converges to `z s ⟨∇U^{s,Ta}φ, ∇U^{s,Tb}ψ⟩` with an explicit envelope.
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4AT

open HRS HRS.Whole HRS.MS.FixEq HRS.MS.CovMeas

variable {d : ℕ}

theorem k4at_z_bound_iter {r : ℕ} {Pw T' : ℝ} (hP : (d : ℝ) < 2 * Pw) {z : ℝ → (Euc d → ℝ) → ℝ}
    (hz : IsR2L1F r Pw T' z) {t0 : ℝ} (ht0 : t0 ∈ Set.Icc (0 : ℝ) T') {f : Euc d → ℝ}
    (hf : ContDiff ℝ r f) {B : ℝ} (hB : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) :
    ENNReal.ofReal |z t0 f| ≤ dualNormE r Pw (z t0) * ENNReal.ofReal (s57pC d r Pw * B) := by
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 (Nat.zero_le _) 0)
  exact s57p_initial_bound hP (k4at_bounded_of_L1F hz ht0) hf hB

theorem k4at_z_diff_bound_iter {r : ℕ} {Pw T' : ℝ} (hP : (d : ℝ) < 2 * Pw) {z : ℝ → (Euc d → ℝ) → ℝ}
    (hz : IsR2L1F r Pw T' z) {t0 : ℝ} (ht0 : t0 ∈ Set.Icc (0 : ℝ) T') {f g : Euc d → ℝ}
    (hf : ContDiff ℝ r f) (hg : ContDiff ℝ r g) {B Bδ : ℝ}
    (hBf : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ B) (hBg : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j g x‖ ≤ B)
    (hdiff : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j (fun y => f y - g y) x‖ ≤ Bδ) :
    ENNReal.ofReal |z t0 f - z t0 g| ≤ dualNormE r Pw (z t0) * ENNReal.ofReal (s57pC d r Pw * Bδ) := by
  have hη := k4at_bounded_of_L1F hz ht0
  have hs := s57p_eta_sub hP hη hf hg hBf hBg
  rw [← hs]
  exact s57p_initial_bound hP hη (hf.sub hg) hdiff

theorem k4at_jets {r : ℕ} {C : WholeCoeff d} {m H : ℝ} (horb : K4OscOrbitApprox C m H r)
    {φ : Euc d → ℝ} (hφ : IsOscTest m φ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) H) :
    ∃ b : ℝ, 0 ≤ b ∧ ∃ ε : ℕ → ℝ, (∀ n, 0 ≤ ε n) ∧ Tendsto ε atTop (𝓝 0) ∧
      (∀ s ∈ Set.Icc (0 : ℝ) t, ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (propagatorW C s t φ) ∧
        ∀ j ≤ r + 1, ∀ x, ‖iteratedFDeriv ℝ j (propagatorW C s t φ) x‖ ≤ b) ∧
      (∀ n : ℕ, ∀ s ∈ Set.Icc (0 : ℝ) t,
        ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (propagatorW C s t (k4hs m n φ))) ∧
      ∀ᶠ n : ℕ in atTop, ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ j ≤ r + 1, ∀ x,
        ‖iteratedFDeriv ℝ j (fun y => propagatorW C s t (k4hs m n φ) y - propagatorW C s t φ y) x‖ ≤ ε n := by
  obtain ⟨K, hK0, hKb⟩ := horb.bound
  have hst : ∀ s ∈ Set.Icc (0 : ℝ) t, s ∈ Set.Icc (0 : ℝ) H ∧ t ∈ Set.Icc s H := fun s hs =>
    ⟨⟨hs.1, hs.2.trans ht.2⟩, ⟨hs.2, ht.2⟩⟩
  set δ : ℕ → ℝ≥0∞ := fun n => ⨆ v ∈ Set.Icc (0 : ℝ) H, ⨆ t ∈ Set.Icc v H,
    weightedSupE (r + 1) 0 (propagatorW C v t (k4hs m n φ) - propagatorW C v t φ) with hδ
  have hδt : Tendsto δ atTop (𝓝 0) := horb.limit φ hφ
  have hcd : ∀ s ∈ Set.Icc (0 : ℝ) t, ∀ (ψ : Euc d → ℝ), IsOscTest m ψ →
      ContDiff ℝ ((r + 1 : ℕ) : WithTop ℕ∞) (propagatorW C s t ψ) := by
    intro s hs ψ hψ
    obtain ⟨hsH, htH⟩ := hst s hs
    have := horb.smooth ψ hψ s hsH t htH
    exact_mod_cast this
  refine ⟨((d : ℝ) + 1) ^ (r + 1) * max (K * oscNorm m φ) 0, mul_nonneg (by positivity) (le_max_right _ _),
    fun n => ((d : ℝ) + 1) ^ (r + 1) * (δ n).toReal, fun n => mul_nonneg (by positivity) ENNReal.toReal_nonneg,
    ?_, ?_, fun n s hs => hcd s hs _ (k4hs_osc m n φ), ?_⟩
  · have h0 := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hδt
    rw [ENNReal.toReal_zero] at h0
    simpa using h0.const_mul (((d : ℝ) + 1) ^ (r + 1))
  · intro s hs
    obtain ⟨hsH, htH⟩ := hst s hs
    refine ⟨hcd s hs φ hφ, ?_⟩
    have hb := k4at_pd_of_wse (hKb φ hφ s hsH t htH)
    exact k4at_iter_le (le_max_right _ _) hb
  · have hfin : ∀ᶠ n in atTop, δ n < ⊤ := hδt.eventually (gt_mem_nhds (by simp))
    filter_upwards [hfin] with n hn s hs
    obtain ⟨hsH, htH⟩ := hst s hs
    have hdle : weightedSupE (r + 1) 0 (propagatorW C s t (k4hs m n φ) - propagatorW C s t φ) ≤ δ n :=
      le_iSup₂_of_le s hsH (le_iSup₂_of_le t htH le_rfl)
    have hdle' : weightedSupE (r + 1) 0 (propagatorW C s t (k4hs m n φ) - propagatorW C s t φ) ≤
        ENNReal.ofReal (δ n).toReal := by rwa [ENNReal.ofReal_toReal hn.ne]
    have hd := k4at_pd_of_wse hdle'
    have hmx : max (δ n).toReal 0 = (δ n).toReal := max_eq_left ENNReal.toReal_nonneg
    rw [hmx] at hd
    exact k4at_iter_le ENNReal.toReal_nonneg hd

end HRS.MS.S111K4AT
