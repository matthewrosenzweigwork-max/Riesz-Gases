import HRS.MS.R2WinOrbTRE3
import HRS.MS.S103dLip1

/-!
# S10.3 (S103D), part 2: weighted time continuity of `ρ'` (`S103cRhoPrimeUC`) for small `ε_*`

Namespace `HRS.MS.R2WinOrbNL`, prefix `s103d_`.  Paper: `S103_weighted_time_continuity` (Theorem 1.1 and Corollary 4.1).

Identification (the point flagged by S103C2): our `ρ'` is the pointwise RIGHT derivative `∂_t^+ ρ_t(x)` from `mov_schwartz`; for a trajectory in the S6.3 class,
`ρ_t = ρ_* + √ρ_* V_{v_t}` with the constructed mild solution `v` (uniqueness `mov_nl_unique_conjunct`), and `mne_hasDeriv` gives the right derivative
`div Y_{v_t}(x)` of `τ ↦ ρ_τ(x)`; uniqueness of a right derivative of a real function gives `ρ'_t(x) = div Y_{v_t}(x)` for every `t ≥ 0`, `x`.
Then `s103d_div_lip` (the weighted Lipschitz estimate for `u ↦ div Y_u`) and the continuity of `v` into `Σ^m` give the weighted continuity.

* `s103d_ident`: for `ε_* ≤ ε₀` (`ε₀` depending on `c₁, C₁`) every trajectory of the class is `ρ_t = ρ_* + √ρ_* V_{v_t}` with `v` continuous into `Σ^m` of norm `≤ r`
  and with right derivative `div Y_{v_t}`.
* `s103d_uc_small`: `S103cRhoPrimeUC d s a β ρβ ε_* c₁ C₁ K L` for all `0 < ε_* ≤ ε₀` (any `K`, `L` with `K + d/2 + 4 < 102 d + 1020`).
* `s103d_rhoPrimeUCsmall`: `S103cRhoPrimeUCsmall d s a β` (unconditional).
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory Metric
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.R2WinOrbNL

open HRS HRS.Whole HRS.MS.Wad HRS.MS.Ul HRS.MS.Who HRS.MS.BreakdownS67 HRS.MS.MovLin HRS.MS.R2WinOrb
  HRS.MS.MovOsc HRS.MS.Mov63 HRS.MS.MovAdj HRS.MS.MovSch

variable {d : ℕ}

theorem s103d_hm3 (d : ℕ) : (d : ℝ) / 2 + 3 < ((102 * d + 1020 : ℕ) : ℝ) := by
  have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  push_cast; linarith

/-- A trajectory of the class, for small `ε_*`, is the constructed mild solution: `ρ_t = ρ_* + √ρ_* V_{v_t}`, `v` continuous into `Σ^m`, `‖v_t‖ ≤ r`, and the
right derivative of `τ ↦ ρ_τ(x)` at every `t ≥ 0` is `div Y_{v_t}(x)`. -/
theorem s103d_ident {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) {c₁ : ℝ} (hc₁ : 0 < c₁) (C₁ : ℝ) :
    ∃ ε₀ r : ℝ, 0 < ε₀ ∧ 0 < r ∧ ∀ εstar : ℝ, 0 < εstar → εstar ≤ ε₀ →
      ∀ (ε : ℝ) (ψ : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ), IsAdmissiblePerturbation ρβ εstar ε ψ →
        IsResultingSolution d s a β ρβ εstar ε ψ c₁ C₁ ρ →
        ∃ v : ℝ → OscSpace d ((102 * d + 1020 : ℕ) : ℝ), ContinuousOn v (Set.Ici 0) ∧
          (∀ t : ℝ, 0 ≤ t → ‖v t‖ ≤ r) ∧
          (∀ t : ℝ, 0 ≤ t → ρ t = mneRho ρβ (s103d_hm3 d) (v t)) ∧
          ∀ t : ℝ, 0 ≤ t → ∀ x : Euc d,
            HasDerivWithinAt (fun τ => ρ τ x) (movDiv (mneY d s a β ρβ (s103d_hm3 d) (v t)) x) (Set.Ici t) t := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hj : 1 ≤ 100 * d + 1000 := by omega
  have hm : (d : ℝ) / 2 + ((100 * d + 1000 : ℕ) : ℝ) + 6 < ((102 * d + 1020 : ℕ) : ℝ) := by
    push_cast; linarith
  have hm3 := s103d_hm3 d
  obtain ⟨c₁', hc₁', h⟩ := mov63_decay_f0 H hj
  obtain ⟨εS, r, c, C₀, hεS, -, hr, -, -, hf⟩ := h (102 * d + 1020) hm
  set K₁ : ℝ := max C₁ 1 with hK₁
  have hK₁0 : 0 < K₁ := lt_of_lt_of_le one_pos (le_max_right _ _)
  refine ⟨min εS (r / K₁), r, lt_min hεS (div_pos hr hK₁0), hr, fun εstar hεpos hεle ε ψ ρ hψ hres => ?_⟩
  have hCε : C₁ * εstar ≤ r := by
    calc C₁ * εstar ≤ K₁ * εstar := mul_le_mul_of_nonneg_right (le_max_left _ _) hεpos.le
      _ ≤ K₁ * (r / K₁) := mul_le_mul_of_nonneg_left (hεle.trans (min_le_right _ _)) hK₁0.le
      _ = r := by field_simp
  have hsm := s103n_small_class hres hCε
  have hI := s103n_initial_class H (hεle.trans (min_le_left _ _)) hψ
  have hcont := mnh_contDiff3 H hm3 hI.cb hj hI.osc
  have hmass := mnh_massZero H hm3 hI.osc hI.mean
  obtain ⟨v, hmild, -, hcls, -, -, -, -⟩ := hf hm3 _ hcont hI.cb hI.osc hmass hI.small
  have huniq := mov_nl_unique_conjunct H.hd H.hs0 H.hsd H.hβ H.hq H.hρ hj hm hcls ρ (hsm.mono_rate hc₁.le)
  have hrt : ∀ t : ℝ, 0 ≤ t → ρ t = mneRho ρβ hm3 (v t) := fun t ht => by
    rw [huniq t ht, mneP_eq hm3 ht]
  refine ⟨v, hmild.cont, fun t ht => ?_, hrt, fun t ht x => ?_⟩
  · have h1 := (hcls.weighted t ht).2
    rw [mne_movV hm3 H t ht, mneV_norm hm3] at h1
    refine h1.trans ?_
    have : Real.exp (-(c₁' / 2) * t) ≤ 1 := Real.exp_le_one_iff.mpr (by nlinarith)
    nlinarith
  · have hder := mne_hasDeriv hm3 H hmild ht x
    refine (hder.mono (Set.Ici_subset_Ici.2 ht)).congr (fun τ hτ => ?_) ?_
    · rw [hrt τ (ht.trans hτ)]
    · rw [hrt t ht]

/-- `U2Dec` is monotone in the amplitude. -/
theorem s103d_u2dec_mono_A {k : ℕ} {L A A' : ℝ} {f : Euc d → ℝ} (hf : U2Dec k L A f) (h : A ≤ A') :
    U2Dec k L A' f := by
  refine ⟨hf.1, fun i hi y => (hf.2 i hi y).trans (mul_le_mul_of_nonneg_right h ?_)⟩
  unfold u2Wt
  exact Real.rpow_nonneg (by linarith [norm_nonneg y]) _

/-- Weighted time continuity of `ρ'` for small `ε_*`: `S103cRhoPrimeUC` at every `0 < ε_* ≤ ε₀`. -/
theorem s103d_uc_small {s a β : ℝ} {ρβ : Euc d → ℝ} (H : Mov2dTh d s β a ρβ) (c₁ C₁ : ℝ) (K L : ℕ)
    (hK : (K : ℝ) + d / 2 + 4 < ((102 * d + 1020 : ℕ) : ℝ)) :
    ∃ ε₀ : ℝ, 0 < ε₀ ∧ ∀ εstar : ℝ, 0 < εstar → εstar ≤ ε₀ →
      S103cRhoPrimeUC d s a β ρβ εstar c₁ C₁ K L := by
  by_cases hc₁ : 0 < c₁
  swap
  · exact ⟨1, one_pos, fun εstar _ _ ε ψ ρ ρ' _ hres => absurd hres.cpos hc₁⟩
  obtain ⟨ε₀, r, hε₀, hr, hid⟩ := s103d_ident H hc₁ C₁
  obtain ⟨M, hM0, hM⟩ := s103d_div_lip H hK L hr.le
  refine ⟨ε₀, hε₀, fun εstar hεpos hεle ε ψ ρ ρ' hψ hres hder _ t ht ε' hε' => ?_⟩
  obtain ⟨v, hvc, hvr, -, hvd⟩ := hid εstar hεpos hεle ε ψ ρ hψ hres
  -- identification of `ρ'` with `div Y_{v_t}`
  have hid' : ∀ t : ℝ, 0 ≤ t → ∀ x, ρ' t x = movDiv (mneY d s a β ρβ (s103d_hm3 d) (v t)) x := fun t ht x =>
    ((hder t ht x).derivWithin (uniqueDiffWithinAt_Ici t)).symm.trans
      ((hvd t ht x).derivWithin (uniqueDiffWithinAt_Ici t))
  have hδ : 0 < ε' / (2 ^ L * (M + 1)) := by positivity
  obtain ⟨η, hη, hηv⟩ := Metric.continuousWithinAt_iff.1 (hvc t ht) _ hδ
  refine ⟨η, hη, fun σ hσ hσt => ?_⟩
  have hdist := hηv hσ (by rwa [Real.dist_eq])
  rw [dist_eq_norm] at hdist
  obtain ⟨hcd, hb⟩ := hM (v σ) (v t) (hvr σ hσ) (hvr t ht)
  have e : (fun y => ρ' σ y - ρ' t y) = fun x =>
      movDiv (mneY d s a β ρβ (s103d_hm3 d) (v σ)) x - movDiv (mneY d s a β ρβ (s103d_hm3 d) (v t)) x := by
    funext y
    rw [hid' σ hσ y, hid' t ht y]
  rw [e]
  refine s103d_u2dec_mono_A (s103n_u2dec_of_bracket hcd hb) ?_
  have h1 : M * ‖v σ - v t‖ ≤ M * (ε' / (2 ^ L * (M + 1))) := mul_le_mul_of_nonneg_left hdist.le hM0
  have h2 : M * (ε' / (2 ^ L * (M + 1))) ≤ ε' / 2 ^ L := by
    rw [mul_div_assoc', div_le_div_iff₀ (by positivity) (by positivity)]
    nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) L]
  calc 2 ^ L * (M * ‖v σ - v t‖) ≤ 2 ^ L * (ε' / 2 ^ L) :=
        mul_le_mul_of_nonneg_left (h1.trans h2) (by positivity)
    _ = ε' := by field_simp

/-- The helper premise of `s103d_tie`, unconditionally. -/
theorem s103d_rhoPrimeUCsmall (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) :
    S103cRhoPrimeUCsmall d s a β := by
  intro ρβ hρ c₁ C₁
  have H : Mov2dTh d s β a ρβ := ⟨hd, hs0, hs, hβ, ha, hρ⟩
  have hK : (((8 * d + 80 + 1 : ℕ)) : ℝ) + d / 2 + 4 < ((102 * d + 1020 : ℕ) : ℝ) := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    push_cast; linarith
  exact s103d_uc_small H c₁ C₁ (8 * d + 80 + 1) (s103dL d s) hK

end HRS.MS.R2WinOrbNL

end
