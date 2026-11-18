import HRS.MS.WadAux109

/-!
# S8.3, packet S8F-10: smooth cutoffs with derivative bounds uniform in the radius, and the cutoff error in the weighted jet norm

`s8f_cutoff k`: for every `R ≥ 1` a `C_c^∞` function `χ_R = χ(R⁻¹ ·)` with `χ_R = 1` on `‖x‖ < 2R`, `0 ≤ χ_R ≤ 1` and `‖D^iχ_R‖ ≤ B` for `i ≤ k`
(`B` independent of `R`).  `s8f_cutoff_error`: for `f ∈ C^k` with weighted decay of `D^i f`, `i ≤ k`, and `ε > 0` there is `R ≥ 1` such that
`‖D^i(χ_R f - f)(x)‖ ≤ ε ⟨x⟩^M` for `i ≤ k`, all `x`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

open HRS HRS.Whole

variable {d : ℕ}

theorem s8f_cutoff (k : ℕ) : ∃ B : ℝ, 0 ≤ B ∧ ∀ R : ℝ, 1 ≤ R → ∃ χ : Euc d → ℝ,
    ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧ (∀ x, ‖x‖ < 2 * R → χ x = 1) ∧
    (∀ x, 0 ≤ χ x ∧ χ x ≤ 1) ∧ (∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i χ x‖ ≤ B) := by
  let ψ : ContDiffBump (0 : Euc d) := ⟨2, 3, by norm_num, by norm_num⟩
  have hb : ∀ i : ℕ, ∃ C : ℝ, ∀ x, ‖iteratedFDeriv ℝ i (⇑ψ) x‖ ≤ C := fun i =>
    (ψ.contDiff.continuous_iteratedFDeriv (m := i) (by exact_mod_cast le_top)).bounded_above_of_compact_support
      (ψ.hasCompactSupport.iteratedFDeriv i)
  choose C hC using hb
  refine ⟨∑ i ∈ Finset.range (k + 1), |C i|, Finset.sum_nonneg fun i _ => abs_nonneg _, fun R hR => ?_⟩
  have hR0 : 0 < R := by linarith
  have hRi : 0 < R⁻¹ := inv_pos.2 hR0
  refine ⟨fun x => ψ (R⁻¹ • x), ψ.contDiff.comp (contDiff_const_smul _), ?_, fun x hx => ?_,
    fun x => ⟨ψ.nonneg, ψ.le_one⟩, fun i hi x => ?_⟩
  · refine HasCompactSupport.intro (isCompact_closedBall (0 : Euc d) (3 * R)) fun x hx => ?_
    rw [mem_closedBall, dist_zero_right, not_le] at hx
    refine ψ.zero_of_le_dist ?_
    show (3 : ℝ) ≤ dist (R⁻¹ • x) 0
    rw [dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hRi]
    rw [inv_mul_eq_div, le_div_iff₀ hR0]
    linarith
  · refine ψ.one_of_mem_closedBall ?_
    rw [mem_closedBall, dist_zero_right, norm_smul, Real.norm_eq_abs, abs_of_pos hRi]
    show R⁻¹ * ‖x‖ ≤ 2
    rw [inv_mul_eq_div, div_le_iff₀ hR0]
    linarith
  · rw [iteratedFDeriv_comp_const_smul R⁻¹ (ψ.contDiff (n := i)), norm_smul, Real.norm_eq_abs, abs_of_pos (pow_pos hRi i)]
    have h1 : R⁻¹ ^ i ≤ 1 := pow_le_one₀ hRi.le (inv_le_one_of_one_le₀ hR)
    have h2 : ‖iteratedFDeriv ℝ i (⇑ψ) (R⁻¹ • x)‖ ≤ ∑ j ∈ Finset.range (k + 1), |C j| :=
      (hC i _).trans ((le_abs_self _).trans (Finset.single_le_sum (f := fun j => |C j|)
        (fun j _ => abs_nonneg _) (Finset.mem_range.2 (by omega))))
    calc R⁻¹ ^ i * ‖iteratedFDeriv ℝ i (⇑ψ) (R⁻¹ • x)‖ ≤ 1 * ∑ j ∈ Finset.range (k + 1), |C j| :=
          mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
      _ = _ := one_mul _

theorem s8f_cutoff_error {M : ℝ} (hM : 0 ≤ M) {k : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ k f)
    (hdec : ∀ i ≤ k, Tendsto (fun x => ‖iteratedFDeriv ℝ i f x‖ / jbracket x ^ M) (cocompact (Euc d)) (𝓝 0))
    {ε : ℝ} (hε : 0 < ε) :
    ∃ χ : Euc d → ℝ, ContDiff ℝ ∞ χ ∧ HasCompactSupport χ ∧
      ∀ i ≤ k, ∀ x, ‖iteratedFDeriv ℝ i (fun y => χ y * f y - f y) x‖ ≤ ε * jbracket x ^ M := by
  obtain ⟨B, hB0, hχ⟩ := s8f_cutoff (d := d) k
  set Cχ : ℝ := (B + 1) * 2 ^ k with hCχ
  have hCχ0 : 0 < Cχ := by positivity
  set ε' : ℝ := ε / Cχ with hε'
  have hε'0 : 0 < ε' := by positivity
  -- the tail
  have hev : ∀ᶠ z in cocompact (Euc d), ∀ m ∈ Finset.range (k + 1),
      ‖iteratedFDeriv ℝ m f z‖ / jbracket z ^ M < ε' := by
    rw [Filter.eventually_all_finset]
    intro m hm
    exact (hdec m (by simpa [Nat.lt_succ_iff] using hm)).eventually (gt_mem_nhds hε'0)
  obtain ⟨K, hK, hKs⟩ := Filter.mem_cocompact.1 hev
  obtain ⟨R₀, hR₀⟩ := hK.isBounded.subset_closedBall (0 : Euc d)
  set R : ℝ := max R₀ 1 with hR
  have hR1 : 1 ≤ R := le_max_right _ _
  have hR0 : 0 < R := by linarith
  have hfar : ∀ m ≤ k, ∀ z : Euc d, R < ‖z‖ → ‖iteratedFDeriv ℝ m f z‖ ≤ ε' * jbracket z ^ M := by
    intro m hm z hz
    have hzK : z ∉ K := fun h => by
      have := hR₀ h
      rw [Metric.mem_closedBall, dist_zero_right] at this
      have := le_max_left R₀ 1
      linarith
    have := hKs hzK m (Finset.mem_range.2 (by omega))
    have hp : 0 < jbracket z ^ M := Real.rpow_pos_of_pos (s83_jb_pos z) _
    rw [div_lt_iff₀ hp] at this
    exact this.le
  obtain ⟨χ, hχd, hχc, hχ1, hχb, hχD⟩ := hχ R hR1
  refine ⟨χ, hχd, hχc, fun i hi x => ?_⟩
  by_cases hx : ‖x‖ ≤ R
  · -- near `x` the cutoff is `1`
    have hnhds : {y : Euc d | ‖y‖ < 2 * R} ∈ 𝓝 x := by
      refine IsOpen.mem_nhds (isOpen_lt continuous_norm continuous_const) ?_
      show ‖x‖ < 2 * R
      linarith
    have heq : (fun y => χ y * f y - f y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      filter_upwards [hnhds] with y hy
      rw [hχ1 y hy]; ring
    have := (Filter.EventuallyEq.iteratedFDeriv ℝ heq i).eq_of_nhds
    rw [this]
    have h0 : iteratedFDeriv ℝ i (fun _ : Euc d => (0 : ℝ)) x = 0 := by
      by_cases hi0 : i = 0
      · subst hi0
        simp [iteratedFDeriv_zero_eq_comp]
      · rw [iteratedFDeriv_const_of_ne hi0]; rfl
    rw [h0, norm_zero]
    have := Real.rpow_nonneg (s83_jb_pos x).le M
    positivity
  · push Not at hx
    have hcd : ContDiff ℝ (k : WithTop ℕ∞) (fun y => χ y - 1) :=
      ((hχd.of_le (by exact_mod_cast le_top)).sub contDiff_const)
    have hfk : ContDiff ℝ (k : WithTop ℕ∞) f := hf
    have e : (fun y => χ y * f y - f y) = fun y => (χ y - 1) * f y := by funext y; ring
    rw [e]
    have hLeib := norm_iteratedFDeriv_mul_le hcd hfk x (n := i) (by exact_mod_cast hi)
    refine hLeib.trans ?_
    have hbl : ∀ l ≤ i, ‖iteratedFDeriv ℝ l (fun y => χ y - 1) x‖ ≤ B + 1 := by
      intro l hl
      by_cases hl0 : l = 0
      · subst hl0
        rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs, abs_le]
        constructor <;> linarith [hχb x |>.1, hχb x |>.2]
      · have hcl : ContDiff ℝ l χ := hχd.of_le (by exact_mod_cast le_top)
        have e2 : iteratedFDeriv ℝ l (fun y => χ y - 1) x = iteratedFDeriv ℝ l χ x := by
          have := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := x) (i := l) (f := χ) (g := fun _ => (1 : ℝ))
            hcl.contDiffAt contDiff_const.contDiffAt
          simp only [Pi.sub_def] at this ⊢
          rw [this, iteratedFDeriv_const_of_ne hl0]
          simp
        rw [e2]
        exact (hχD l (hl.trans hi) x).trans (by linarith)
    calc ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ‖iteratedFDeriv ℝ l (fun y => χ y - 1) x‖ *
          ‖iteratedFDeriv ℝ (i - l) f x‖
        ≤ ∑ l ∈ Finset.range (i + 1), (i.choose l : ℝ) * ((B + 1) * (ε' * jbracket x ^ M)) := by
          refine Finset.sum_le_sum fun l hl => ?_
          have hl' : l ≤ i := by simpa [Nat.lt_succ_iff] using hl
          have h1 := hbl l hl'
          have h2 := hfar (i - l) (by omega) x hx
          have h3 : 0 ≤ (i.choose l : ℝ) := Nat.cast_nonneg _
          rw [mul_assoc]
          exact mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (by linarith)) h3
      _ = 2 ^ i * ((B + 1) * (ε' * jbracket x ^ M)) := by
          rw [← Finset.sum_mul]
          congr 1
          exact_mod_cast Nat.sum_range_choose i
      _ ≤ 2 ^ k * ((B + 1) * (ε' * jbracket x ^ M)) := by
          have hj := Real.rpow_nonneg (s83_jb_pos x).le M
          have : 0 ≤ (B + 1) * (ε' * jbracket x ^ M) := by positivity
          exact mul_le_mul_of_nonneg_right (pow_le_pow_right₀ (by norm_num) hi) this
      _ = ε * jbracket x ^ M := by
          rw [hε', hCχ]; field_simp

end HRS.MS.Wad
