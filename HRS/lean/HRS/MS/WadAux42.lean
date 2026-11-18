import HRS.MS.WadAux41

/-!
# S8.3, packet D8 (Route A), part 1: density of `C_c^∞` in `C_M`

`s85_density`: every `f ∈ C_M` (`M ≥ 0`) is a limit of `C_c^∞` functions in the weighted sup norm
(cutoff, then Mathlib's smooth approximation `Continuous.exists_contDiff_approx`).
`S85Approx M f φ`: `φ n ∈ C_c^∞` with `|φ_n - f| ≤ ⟨x⟩^M/(n+1)`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s85_density {M : ℝ} (hM : 0 ≤ M) {f : Euc d → ℝ} (hf : MemCM M f) {ε : ℝ} (hε : 0 < ε) :
    ∃ φ : Euc d → ℝ, S85Cc φ ∧ Wt M ε (fun y => φ y - f y) := by
  have hpos4 : 0 < ε / 4 := by positivity
  have h0 : Tendsto (fun x : Euc d => |f x / jbracket x ^ M|) (cocompact (Euc d)) (𝓝 0) := by
    simpa using hf.2.abs
  have hev : ∀ᶠ x in cocompact (Euc d), |f x / jbracket x ^ M| < ε / 4 :=
    h0.eventually (gt_mem_nhds hpos4)
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 hev
  obtain ⟨R, hR⟩ := hK.isBounded.subset_closedBall (0 : Euc d)
  have hfar : ∀ x : Euc d, R < ‖x‖ → |f x| ≤ ε / 4 * jbracket x ^ M := by
    intro x hx
    have hxK : x ∉ K := fun h => by
      have := hR h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      linarith
    have := hKs hxK
    have hp : 0 < jbracket x ^ M := Real.rpow_pos_of_pos (s83_jb_pos x) _
    rw [Set.mem_setOf_eq, abs_div, abs_of_pos hp, div_lt_iff₀ hp] at this
    exact this.le
  -- cutoff
  set χ : Euc d → ℝ := fun x => max 0 (min 1 (R + 1 - ‖x‖)) with hχ
  have hχc : Continuous χ := by
    simp only [hχ]
    fun_prop
  have hχ0 : ∀ x, 0 ≤ χ x := fun x => le_max_left _ _
  have hχ1 : ∀ x, χ x ≤ 1 := fun x => max_le zero_le_one (min_le_left _ _)
  have hχin : ∀ x, ‖x‖ ≤ R → χ x = 1 := by
    intro x hx
    have : (1 : ℝ) ≤ R + 1 - ‖x‖ := by linarith
    simp only [hχ, min_eq_left this]
    exact max_eq_right zero_le_one
  have hχout : ∀ x, R + 1 ≤ ‖x‖ → χ x = 0 := by
    intro x hx
    have : R + 1 - ‖x‖ ≤ 0 := by linarith
    simp only [hχ]
    have h2 : min 1 (R + 1 - ‖x‖) ≤ 0 := (min_le_right _ _).trans this
    exact max_eq_left h2
  set f₁ : Euc d → ℝ := fun x => χ x * f x with hf₁
  have hf₁c : Continuous f₁ := hχc.mul hf.1
  have hf₁s : HasCompactSupport f₁ := by
    refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (R + 1)) fun x hx => ?_
    rw [Metric.mem_closedBall, dist_zero_right, not_le] at hx
    simp only [hf₁, hχout x hx.le, zero_mul]
  have hJ : ∀ x : Euc d, 1 ≤ jbracket x ^ M := fun x => Real.one_le_rpow (s83_one_le_jb x) hM
  have hf₁f : ∀ x, |f₁ x - f x| ≤ ε / 4 * jbracket x ^ M := by
    intro x
    by_cases hx : ‖x‖ ≤ R
    · simp only [hf₁, hχin x hx, one_mul, sub_self, abs_zero]
      have := hJ x
      positivity
    · push_neg at hx
      have e : f₁ x - f x = (χ x - 1) * f x := by simp only [hf₁]; ring
      rw [e, abs_mul]
      have h1 : |χ x - 1| ≤ 1 := by
        rw [abs_le]; constructor <;> linarith [hχ0 x, hχ1 x]
      calc |χ x - 1| * |f x| ≤ 1 * |f x| := mul_le_mul_of_nonneg_right h1 (abs_nonneg _)
        _ ≤ ε / 4 * jbracket x ^ M := by rw [one_mul]; exact hfar x hx
  obtain ⟨g, hgd, hga, hgs⟩ := hf₁c.exists_contDiff_approx (⊤ : ℕ∞) (ε := fun _ => ε / 2)
    continuous_const (fun _ => by positivity)
  refine ⟨g, ⟨hgd, hf₁s.mono hgs⟩, fun x => ?_⟩
  have hga' : |g x - f₁ x| < ε / 2 := by
    have := hga x
    rwa [Real.dist_eq] at this
  have hj := hJ x
  show ‖g x - f x‖ ≤ ε * jbracket x ^ M
  rw [Real.norm_eq_abs]
  have e : g x - f x = (g x - f₁ x) + (f₁ x - f x) := by ring
  rw [e]
  have h2 := hf₁f x
  have h3 := abs_add_le (g x - f₁ x) (f₁ x - f x)
  nlinarith [mul_nonneg hε.le (sub_nonneg.2 hj), abs_nonneg (g x - f₁ x), abs_nonneg (f₁ x - f x)]

/-- An approximating sequence of `C_c^∞` functions, with rate `C/(n+1)`. -/
def S85Approx (M : ℝ) (f : Euc d → ℝ) (φ : ℕ → Euc d → ℝ) : Prop :=
  (∀ n, S85Cc (φ n)) ∧ ∃ C : ℝ, 0 ≤ C ∧ ∀ n : ℕ, Wt M (C / ((n : ℝ) + 1)) (fun y => φ n y - f y)

theorem s85_exists_approx {M : ℝ} (hM : 0 ≤ M) {f : Euc d → ℝ} (hf : MemCM M f) :
    ∃ φ : ℕ → Euc d → ℝ, S85Approx M f φ := by
  have : ∀ n : ℕ, ∃ φ : Euc d → ℝ, S85Cc φ ∧ Wt M (1 / ((n : ℝ) + 1)) (fun y => φ y - f y) :=
    fun n => s85_density hM hf (by positivity)
  choose φ hφ using this
  exact ⟨φ, fun n => (hφ n).1, 1, zero_le_one, fun n => (hφ n).2⟩

end HRS.MS.Wad
