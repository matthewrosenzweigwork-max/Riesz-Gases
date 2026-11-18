import HRS.MS.R26T8AP06d11

/-!
# S8.2 local Newton layer, packet T8A.P06d (part 12): joint-jet bound of `midPair F` off the diagonal
`r26t8a_joint_bound_off`: for `z != 0`, `j <= k < -sigma`: `|D^j (midPair F) (X,z)| <= 2^j (2 + M(-sigma-k,b)) A pairWeight M (X+z/2) (X-z/2)`.
From `r26t8a_joint_le_nest` (P06b) applied to the cutoff `psiCut * midPair F` and the conormal bounds (all `q <= k` have a bounded envelope).
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_env_bound (b : ℕ) {σ : ℝ} {k q : ℕ} (hk : (k : ℝ) < -σ) (hq : q ≤ k) {s : ℝ} (hs : 0 < s) (hs1 : s ≤ 1) :
    1 + s ^ (-(σ + q)) * (1 + |Real.log s|) ^ b ≤ 2 + r26t8a_p06_M (-σ - k) b := by
  have hc : 0 < -σ - (k : ℝ) := by linarith
  have h1 : s ^ (-(σ + q)) ≤ s ^ (-σ - (k : ℝ)) :=
    Real.rpow_le_rpow_of_exponent_ge hs hs1 (by
      have : (q : ℝ) ≤ k := by exact_mod_cast hq
      linarith)
  have h2 := r26t8a_p06_slog b hc hs hs1
  have hlog : 0 ≤ (1 + |Real.log s|) ^ b := by positivity
  nlinarith [mul_le_mul_of_nonneg_right h1 hlog]

theorem r26t8a_joint_bound_off {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k b : ℕ) (M σ : ℝ)
    (hk : (k : ℝ) < -σ) {A : ℝ} (hA : 0 ≤ A) {F : Euc d → Euc d → ℝ} (hF : Conormal (k + 1) b M σ A F)
    (j : ℕ) (hj : j ≤ k) (X z : Euc d) (hz : z ≠ 0) :
    ‖iteratedFDeriv ℝ j (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) (X, z)‖ ≤
      2 ^ j * (2 + r26t8a_p06_M (-σ - k) b) * A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
  have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
  obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 * ‖z‖ := ⟨_, rfl⟩
  have hR : 0 < R := by rw [hRdef]; positivity
  have hl : R / 4 < ‖z‖ := by rw [hRdef]; linarith
  have hΨ : ContDiff ℝ (j : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) :=
    (r26t8a_gtilde_contDiff hchi hR hF.1).of_le (by exact_mod_cast (by omega : j ≤ k + 1))
  have hopen : IsOpen {w : Euc d × Euc d | R / 4 < ‖w.2‖} := isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
  have hev : (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) =ᶠ[𝓝 (X, z)]
      (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) := by
    filter_upwards [hopen.mem_nhds (show R / 4 < ‖(X, z).2‖ from hl)] with w hw
    simp only [r26t8a_psiCut_one hchi hR (le_of_lt hw), one_mul]
  rw [← (hev.iteratedFDeriv ℝ j).self_of_nhds]
  refine (r26t8a_joint_le_nest j _ X z hΨ).trans ?_
  have hpw0 : 0 ≤ pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) := by
    unfold pairWeight
    exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hterm : ∀ q ∈ Finset.range (j + 1), (j.choose q : ℝ) *
      ‖r26t8a_nest (j - q) q (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) X z‖ ≤
      (j.choose q : ℝ) * ((2 + r26t8a_p06_M (-σ - k) b) * A *
        pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z)) := by
    intro q hq
    have hq' : q ≤ j := Nat.lt_succ_iff.1 (Finset.mem_range.1 hq)
    refine mul_le_mul_of_nonneg_left ?_ (Nat.cast_nonneg _)
    rw [r26t8a_nest_gtilde hchi hR (F := F) (j - q) q X z hl]
    have hb := hF.2 (j - q) q (by omega) X z hz
    have henv := r26t8a_env_bound b hk (show q ≤ k by omega) (s := min 1 ‖z‖) (lt_min one_pos hn) (min_le_left _ _)
    calc ‖mixedJet (j - q) q F X z‖ ≤ A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) *
          (1 + (min 1 ‖z‖) ^ (-(σ + q)) * (1 + |Real.log (min 1 ‖z‖)|) ^ b) := hb
      _ ≤ A * pairWeight M (X + (1 / 2 : ℝ) • z) (X - (1 / 2 : ℝ) • z) * (2 + r26t8a_p06_M (-σ - k) b) :=
          mul_le_mul_of_nonneg_left henv (mul_nonneg hA hpw0)
      _ = _ := by ring
  refine (Finset.sum_le_sum hterm).trans (le_of_eq ?_)
  rw [← Finset.sum_mul]
  have : ∑ q ∈ Finset.range (j + 1), (j.choose q : ℝ) = 2 ^ j := by exact_mod_cast Nat.sum_range_choose j
  rw [this]; ring

end HRS.MS.R26T8A
