import HRS.MC.S7FCBLp

/-!
# FC-B, part 7: approximate identity (uniform convergence on continuous functions)
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.FCB

open HRS HRS.KernelAux

variable {d : ℕ}

local instance fcb_borel_prod2' : BorelSpace (Torus d × Torus d) := Prod.borelSpace
local instance fcb_open_prod4' : OpensMeasurableSpace ((Torus d × Torus d) × Torus d × Torus d) :=
  Prod.opensMeasurableSpace

theorem fcbKap_integral_sub_left (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) (x : Torus d × Torus d) :
    ∫ q, fcbKap d n (x - q) ∂(volume.prod volume) = 1 := by
  have hmeas : AEStronglyMeasurable (fun q => fcbKap d n (x - q)) (volume.prod volume) :=
    ((fcbKap_continuous n).comp (continuous_const.sub continuous_id)).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun q => fcbKap_nonneg hd hn (x - q)) hmeas,
    fcbKap_lintegral_sub_left hd hn x]
  simp

theorem fcbKap_integrable_sub_left (n : ℕ) (x : Torus d × Torus d) :
    Integrable (fun q => fcbKap d n (x - q)) (volume.prod volume) :=
  ((fcbKap_continuous n).comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)

theorem fcbKap_le_tail (hd : 0 < d) {n : ℕ} (hn : 1 ≤ n) {δ : ℝ} (hδ : 0 ≤ δ) (u : Torus d × Torus d)
    (hu : δ ≤ ‖u‖) :
    fcbKap d n u ≤ (6 * Real.sqrt n) ^ (2 * d) * Real.exp (-(4 * n * δ ^ 2)) := by
  have hs : (0 : ℝ) ≤ 6 * Real.sqrt n := by positivity
  have hpow : (6 * Real.sqrt n) ^ (2 * d) = (6 * Real.sqrt n) ^ d * (6 * Real.sqrt n) ^ d := by
    rw [two_mul, pow_add]
  rw [hpow]
  have hmax : δ ≤ ‖u.1‖ ∨ δ ≤ ‖u.2‖ := by
    rw [Prod.norm_def] at hu
    rcases le_max_iff.mp hu with h | h
    · exact Or.inl h
    · exact Or.inr h
  have key : ∀ a : Torus d, δ ≤ ‖a‖ → fcbK d n a ≤ (6 * Real.sqrt n) ^ d * Real.exp (-(4 * n * δ ^ 2)) := by
    intro a ha
    refine (fcbK_le hd hn a).trans ?_
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have : δ ^ 2 ≤ ‖a‖ ^ 2 := pow_le_pow_left₀ hδ ha 2
    nlinarith [Nat.cast_nonneg (α := ℝ) n]
  unfold fcbKap
  rcases hmax with h | h
  · calc fcbK d n u.1 * fcbK d n u.2 ≤ ((6 * Real.sqrt n) ^ d * Real.exp (-(4 * n * δ ^ 2))) *
          (6 * Real.sqrt n) ^ d :=
        mul_le_mul (key _ h) (fcbK_le_sup hd hn _) (fcbK_nonneg hd hn _) (by positivity)
      _ = _ := by ring
  · calc fcbK d n u.1 * fcbK d n u.2 ≤ (6 * Real.sqrt n) ^ d *
          ((6 * Real.sqrt n) ^ d * Real.exp (-(4 * n * δ ^ 2))) :=
        mul_le_mul (fcbK_le_sup hd hn _) (key _ h) (fcbK_nonneg hd hn _) (by positivity)
      _ = _ := by ring

theorem fcbT_unif_conv (hd : 0 < d) {g : Torus d × Torus d → ℝ} (hg : Continuous g) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n : ℕ, N ≤ n → 1 ≤ n → ∀ x, |fcbT d n g x - g x| ≤ ε := by
  obtain ⟨C0, hC0⟩ := isCompact_univ.exists_bound_of_continuousOn hg.continuousOn
  set M : ℝ := max C0 0 with hMdef
  have hM0 : 0 ≤ M := le_max_right _ _
  have hMg : ∀ x, |g x| ≤ M := fun x => by
    have := hC0 x (mem_univ x); rw [Real.norm_eq_abs] at this; exact this.trans (le_max_left _ _)
  have huc := CompactSpace.uniformContinuous_of_continuous hg
  obtain ⟨δ, hδ, hδg⟩ := Metric.uniformContinuous_iff.1 huc (ε / 4) (by positivity)
  have htail := fcb_tail_tendsto (d := 2 * d) (by omega) hδ
  have hev := htail.eventually (gt_mem_nhds (show (0 : ℝ) < ε / (8 * (M + 1)) by positivity))
  obtain ⟨N, hN⟩ := eventually_atTop.1 hev
  refine ⟨N, fun n hnN hn x => ?_⟩
  set Tb : ℝ := (6 * Real.sqrt n) ^ (2 * d) * Real.exp (-(4 * n * δ ^ 2)) with hTb
  have hTb0 : 0 ≤ Tb := by positivity
  have hTbN : Tb < ε / (8 * (M + 1)) := hN n hnN
  have hint1 : Integrable (fun q => fcbKap d n (x - q) * g q) (volume.prod volume) := by
    exact (((fcbKap_continuous n).comp (continuous_const.sub continuous_id)).mul hg).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have hint2 : Integrable (fun q => fcbKap d n (x - q) * g x) (volume.prod volume) :=
    (fcbKap_integrable_sub_left n x).mul_const _
  have e1 : fcbT d n g x - g x = ∫ q, fcbKap d n (x - q) * (g q - g x) ∂(volume.prod volume) := by
    simp_rw [mul_sub]
    rw [integral_sub hint1 hint2, integral_mul_const, fcbKap_integral_sub_left hd hn x, one_mul]
    rfl
  have hbint : Integrable (fun q => fcbKap d n (x - q) * (ε / 4) + 2 * M * Tb) (volume.prod volume) :=
    ((fcbKap_integrable_sub_left n x).mul_const _).add (integrable_const _)
  have hpt : ∀ q, ‖fcbKap d n (x - q) * (g q - g x)‖ ≤ fcbKap d n (x - q) * (ε / 4) + 2 * M * Tb := by
    intro q
    have hk0 := fcbKap_nonneg hd hn (x - q)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg hk0]
    by_cases hq : ‖x - q‖ < δ
    · have hd1 : dist q x < δ := by rw [dist_eq_norm, norm_sub_rev]; exact hq
      have := hδg hd1
      rw [Real.dist_eq] at this
      have h2 : 0 ≤ 2 * M * Tb := by positivity
      nlinarith
    · push Not at hq
      have h1 := fcbKap_le_tail hd hn hδ.le (x - q) hq
      have h2 : |g q - g x| ≤ 2 * M := by
        calc |g q - g x| ≤ |g q| + |g x| := abs_sub _ _
          _ ≤ M + M := add_le_add (hMg q) (hMg x)
          _ = 2 * M := by ring
      have h3 : fcbKap d n (x - q) * |g q - g x| ≤ Tb * (2 * M) :=
        mul_le_mul h1 h2 (abs_nonneg _) hTb0
      have h4 : 0 ≤ fcbKap d n (x - q) * (ε / 4) := by positivity
      nlinarith
  have hnorm := norm_integral_le_of_norm_le hbint (Eventually.of_forall hpt)
  have hbval : ∫ q, (fcbKap d n (x - q) * (ε / 4) + 2 * M * Tb) ∂(volume.prod volume) = ε / 4 + 2 * M * Tb := by
    rw [integral_add ((fcbKap_integrable_sub_left n x).mul_const _) (integrable_const _),
      integral_mul_const, fcbKap_integral_sub_left hd hn x]
    simp
  rw [e1]
  have h5 : 2 * M * Tb ≤ ε / 4 := by
    have : 2 * M * Tb ≤ 2 * M * (ε / (8 * (M + 1))) := by gcongr
    have h6 : 2 * M * (ε / (8 * (M + 1))) = ε / 4 * (M / (M + 1)) := by field_simp; ring
    have h7 : M / (M + 1) ≤ 1 := by rw [div_le_one (by linarith)]; linarith
    calc 2 * M * Tb ≤ _ := this
      _ = ε / 4 * (M / (M + 1)) := h6
      _ ≤ ε / 4 * 1 := by gcongr
      _ = ε / 4 := mul_one _
  rw [← Real.norm_eq_abs]
  calc ‖∫ q, fcbKap d n (x - q) * (g q - g x) ∂(volume.prod volume)‖ ≤ _ := hnorm
    _ = ε / 4 + 2 * M * Tb := hbval
    _ ≤ ε := by linarith

end HRS.MC.Sec7.FCB
