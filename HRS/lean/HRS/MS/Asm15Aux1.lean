import HRS.MS.CzSymAux3

/-!
# ASM-15, part 1: the plain Bessel symbol `(1+4π²|ξ|²)^{-β/2}` is a Mikhlin multiplier

`asm15_isMikhlin_bessel`: for `β > 0` the symbol `ξ ↦ (1+4π²|ξ|²)^{-β/2}` (the symbol of the Bessel potential
`𝒥^{-β}`, in `mik1_IsMikhlin` form of order `d+1`) is Mikhlin with a constant depending on `d, β` only.

Route (same scaling method as `isMikhlin_fracBessel`): by `symlin_scale_up` it suffices to bound
`‖D^k (R(ρ ·)) η‖` on `|η| = 1`, uniformly in `ρ > 0`, where `R = symlin_R d β` is the symbol.  For `ρ ≤ 1` this is
compactness of the closed unit ball (`R` is globally smooth); for `ρ ≥ 1` write
`R(ρ y) = ρ^{-β} |y|^{-β} σ(ρ y)` with `σ = symlin_sigma d β` the (Mikhlin) fractional Bessel symbol and use Leibniz
with the merged `symlin_case_large`.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.Asm15

open HRS.CZ.Sym HRS.CZ.Mik

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma asm15_R_large (β : ℝ) {ρ : ℝ} (hρ : 0 < ρ) {y : 𝔼} (hy : y ≠ 0) :
    symlin_R d β (ρ • y) = ((ρ ^ (-β) : ℝ) : ℂ) • (symlin_P d (-β) y * symlin_sigma d β (ρ • y)) := by
  have hn : 0 < ‖y‖ := norm_pos_iff.2 hy
  unfold symlin_R symlin_P symlin_sigma
  rw [norm_smul, Real.norm_of_nonneg hρ.le, Real.mul_rpow hρ.le (norm_nonneg _)]
  have h1 : ρ ^ (-β) * ρ ^ β = 1 := by rw [← Real.rpow_add hρ]; simp
  have h2 : ‖y‖ ^ (-β) * ‖y‖ ^ β = 1 := by rw [← Real.rpow_add hn]; simp
  simp only [smul_eq_mul, ← Complex.ofReal_mul]
  congr 1
  set X : ℝ := (1 + 4 * Real.pi ^ 2 * (ρ * ‖y‖) ^ 2) ^ (-β / 2) with hX
  rw [show ρ ^ (-β) * (‖y‖ ^ (-β) * (ρ ^ β * ‖y‖ ^ β * X)) =
      (ρ ^ (-β) * ρ ^ β) * (‖y‖ ^ (-β) * ‖y‖ ^ β) * X by ring, h1, h2]
  ring

lemma asm15_case_small_R (β : ℝ) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : ℝ, 0 < ρ → ρ ≤ 1 → ∀ η : 𝔼, ‖η‖ = 1 →
      ‖iteratedFDeriv ℝ k (fun y : 𝔼 => symlin_R d β (ρ • y)) η‖ ≤ B := by
  have hc : Continuous (iteratedFDeriv ℝ k (symlin_R d β)) :=
    (symlin_R_contDiff β).continuous_iteratedFDeriv (by exact_mod_cast le_top)
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : 𝔼) 1).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨max M 0, le_max_right _ _, fun ρ hρ hρ1 η hη => ?_⟩
  have hb1 := symlin_iter_comp_smul_le (symlin_R_contDiff (d := d) β) hρ k η
  have hb3 := hM (ρ • η) (by
    rw [mem_closedBall_zero_iff, norm_smul, hη, Real.norm_of_nonneg hρ.le]; linarith)
  have hρp : ρ ^ k ≤ 1 := pow_le_one₀ hρ.le hρ1
  calc _ ≤ ρ ^ k * ‖iteratedFDeriv ℝ k (symlin_R d β) (ρ • η)‖ := hb1
    _ ≤ 1 * max M 0 := by
        gcongr
        exact hb3.trans (le_max_left _ _)
    _ = _ := one_mul _

lemma asm15_case_large_R {β : ℝ} (hβ : 0 ≤ β) (k : ℕ) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∀ η : 𝔼, ‖η‖ = 1 →
      ‖iteratedFDeriv ℝ k (fun y : 𝔼 => symlin_R d β (ρ • y)) η‖ ≤ B := by
  have hKex : ∀ j : ℕ, ∃ K : ℝ, 0 ≤ K ∧ ∀ x ∈ Metric.sphere (0 : 𝔼) 1,
      ‖iteratedFDeriv ℝ j (symlin_P d (-β)) x‖ ≤ K := fun j =>
    symlin_sph_bound (symlin_P_contDiffOn (-β)) j
  choose K hK0 hK using hKex
  have hMex : ∀ m : ℕ, ∃ M : ℝ, 0 ≤ M ∧ ∀ ρ : ℝ, 1 ≤ ρ → ∀ η : 𝔼, ‖η‖ = 1 →
      ‖iteratedFDeriv ℝ m (fun y : 𝔼 => symlin_sigma d β (ρ • y)) η‖ ≤ M := fun m =>
    symlin_case_large β m
  choose M hM0 hM using hMex
  refine ⟨∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * K j * M (k - j),
    Finset.sum_nonneg fun j _ => mul_nonneg (mul_nonneg (by positivity) (hK0 j)) (hM0 _), ?_⟩
  intro ρ hρ η hη
  have hρ0 : 0 < ρ := by linarith
  have hs : IsOpen ({0} : Set 𝔼)ᶜ := isOpen_compl_singleton
  have hη0 : η ≠ 0 := by
    intro h; rw [h] at hη; simp at hη
  have hηs : η ∈ ({0} : Set 𝔼)ᶜ := hη0
  have e : (fun y : 𝔼 => symlin_R d β (ρ • y)) =ᶠ[𝓝 η]
      fun y : 𝔼 => ((ρ ^ (-β) : ℝ) : ℂ) • (symlin_P d (-β) y * symlin_sigma d β (ρ • y)) := by
    filter_upwards [hs.mem_nhds hηs] with y hy
    exact asm15_R_large β hρ0 hy
  have hσρ : ∀ y : 𝔼, y ≠ 0 → ContDiffAt ℝ ∞ (fun y : 𝔼 => symlin_sigma d β (ρ • y)) y := by
    intro y hy
    have h0 : ρ • y ≠ 0 := by simpa [hρ0.ne'] using hy
    exact (symlin_sigma_contDiffAt β h0).comp y (contDiff_const_smul ρ).contDiffAt
  have hPat : ContDiffAt ℝ ∞ (symlin_P d (-β)) η :=
    (symlin_P_contDiffOn (-β)).contDiffAt (hs.mem_nhds hηs)
  have hFat : ContDiffAt ℝ ∞ (fun y : 𝔼 => symlin_P d (-β) y * symlin_sigma d β (ρ • y)) η :=
    hPat.mul (hσρ η hη0)
  rw [(e.iteratedFDeriv ℝ k).eq_of_nhds,
    iteratedFDeriv_const_smul_apply' (hFat.of_le (by exact_mod_cast le_top)), norm_smul]
  have hρr : ‖((ρ ^ (-β) : ℝ) : ℂ)‖ ≤ 1 := by
    rw [Complex.norm_real, Real.norm_of_nonneg (Real.rpow_nonneg hρ0.le _)]
    exact Real.rpow_le_one_of_one_le_of_nonpos hρ (by linarith)
  have hle : (k : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  have hPs := symlin_P_contDiffOn (d := d) (-β)
  have hRs : ContDiffOn ℝ ∞ (fun y : 𝔼 => symlin_sigma d β (ρ • y)) ({0} : Set 𝔼)ᶜ :=
    fun y hy => (hσρ y hy).contDiffWithinAt
  have h1 := norm_iteratedFDerivWithin_mul_le hPs hRs hs.uniqueDiffOn hηs hle (n := k)
  rw [iteratedFDerivWithin_of_isOpen k hs hηs] at h1
  have h2 : ∀ j ∈ Finset.range (k + 1), (k.choose j : ℝ) *
      ‖iteratedFDerivWithin ℝ j (symlin_P d (-β)) ({0} : Set 𝔼)ᶜ η‖ *
      ‖iteratedFDerivWithin ℝ (k - j) (fun y : 𝔼 => symlin_sigma d β (ρ • y)) ({0} : Set 𝔼)ᶜ η‖ ≤
      (k.choose j : ℝ) * K j * M (k - j) := by
    intro j hj
    rw [iteratedFDerivWithin_of_isOpen j hs hηs, iteratedFDerivWithin_of_isOpen (k - j) hs hηs]
    have hb1 := hK j η (by simpa using hη)
    have hb2 := hM (k - j) ρ hρ η hη
    have hKj := hK0 j
    gcongr
  calc ‖((ρ ^ (-β) : ℝ) : ℂ)‖ *
        ‖iteratedFDeriv ℝ k (fun y : 𝔼 => symlin_P d (-β) y * symlin_sigma d β (ρ • y)) η‖
      ≤ 1 * ∑ j ∈ Finset.range (k + 1), (k.choose j : ℝ) * K j * M (k - j) := by
        gcongr
        exact h1.trans (Finset.sum_le_sum h2)
    _ = _ := one_mul _

/-- **the plain Bessel symbol `(1+4π²|ξ|²)^{-β/2}`, `β > 0`, is Mikhlin** (constant depending on `d, β` only) -/
theorem asm15_isMikhlin_bessel (d : ℕ) {β : ℝ} (hβ : 0 < β) :
    ∃ A : ℝ, 0 ≤ A ∧ mik1_IsMikhlin d A
      (fun ξ : EuclideanSpace ℝ (Fin d) => (((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-β / 2) : ℝ) : ℂ)) := by
  have hex : ∀ i : ℕ, ∃ B : ℝ, 0 ≤ B ∧ ∀ ρ : ℝ, 0 < ρ → ∀ η : EuclideanSpace ℝ (Fin d), ‖η‖ = 1 →
      ‖iteratedFDeriv ℝ i (fun y : EuclideanSpace ℝ (Fin d) => symlin_R d β (ρ • y)) η‖ ≤ B := by
    intro i
    obtain ⟨B1, hB1, h1⟩ := asm15_case_small_R (d := d) β i
    obtain ⟨B2, hB2, h2⟩ := asm15_case_large_R (d := d) hβ.le i
    refine ⟨max B1 B2, le_max_of_le_left hB1, fun ρ hρ η hη => ?_⟩
    rcases le_total ρ 1 with h | h
    · exact (h1 ρ hρ h η hη).trans (le_max_left _ _)
    · exact (h2 ρ h η hη).trans (le_max_right _ _)
  choose B hB0 hB using hex
  refine ⟨∑ i ∈ Finset.range (d + 2), B i, Finset.sum_nonneg fun i _ => hB0 i, ?_, ?_⟩
  · intro ξ _
    exact (symlin_R_contDiff β).contDiffAt
  · intro i hi ξ hξ
    have hn : 0 < ‖ξ‖ := norm_pos_iff.2 hξ
    have hσ : ContDiffOn ℝ ∞ (symlin_R d β) ({0} : Set (EuclideanSpace ℝ (Fin d)))ᶜ :=
      (symlin_R_contDiff β).contDiffOn
    set w : EuclideanSpace ℝ (Fin d) := ‖ξ‖⁻¹ • ξ with hw
    have hwn : ‖w‖ = 1 := by
      rw [hw, norm_smul, norm_inv, norm_norm]; exact inv_mul_cancel₀ hn.ne'
    have hw0 : w ≠ 0 := by intro h; rw [h] at hwn; simp at hwn
    have hξw : ξ = ‖ξ‖ • w := by rw [hw, smul_smul, mul_inv_cancel₀ hn.ne', one_smul]
    have hs := symlin_scale_up hσ hn hw0 i
    rw [← hξw] at hs
    have hb := hB i ‖ξ‖ hn w hwn
    have hKA : B i ≤ ∑ j ∈ Finset.range (d + 2), B j :=
      Finset.single_le_sum (f := B) (fun j _ => hB0 j) (Finset.mem_range.2 (by omega))
    have hpow : ‖ξ‖ ^ (-(i : ℝ)) = (‖ξ‖⁻¹) ^ i := by
      rw [Real.rpow_neg hn.le, Real.rpow_natCast, inv_pow]
    rw [hpow]
    calc _ ≤ (‖ξ‖⁻¹) ^ i * ‖iteratedFDeriv ℝ i (fun y => symlin_R d β (‖ξ‖ • y)) w‖ := hs
      _ ≤ (‖ξ‖⁻¹) ^ i * B i := by gcongr
      _ ≤ (‖ξ‖⁻¹) ^ i * ∑ j ∈ Finset.range (d + 2), B j := by gcongr
      _ = _ := by ring

end HRS.CZ.Asm15
