import HRS.Commutator.Whole.XBBAux1

/-!
# MIK-1, part 1: the Mikhlin class and the dyadic symbol family `Θ_k(η) = m(2^k η) ρ(η)`

Packet MIK-1 (localised Mikhlin multiplier theorem, CZ development).  `HRS/CZ/Defs.lean` of `docs/CZ_PLAN.md`
does not exist in this branch, so the Mikhlin class is defined here as `mik1_IsMikhlin`; it is intended to
agree with the planned `HRS.CZ.IsMikhlin` (the single difference: smoothness is `ContDiffAt ℝ ∞`, ordinary
smoothness, instead of `ContDiffAt ℝ ⊤`, which in Mathlib means analytic; the `∞` version is the weaker
hypothesis and therefore the more general theorem).

* `mik1_IsMikhlin d A m`: `m : 𝔼 → ℂ` is smooth off `0` and `‖D^i m ξ‖ ≤ A ‖ξ‖^{-i}` for `i ≤ d+1`, `ξ ≠ 0`.
* `mik1_Th m k η := m (2^k • η) * rho η`.  If `m` is Mikhlin with constant `A`, then `(mik1_Th m)` is a
  `SymFam 2` with derivative bound `mik1_c0 * A`, `mik1_c0` depending only on `d` (scaling chain rule and
  Leibniz).
-/

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal FourierTransform ContDiff SchwartzMap LineDeriv Convolution

noncomputable section
namespace HRS.CZ.Mik
open HRS.Commutator.Whole HRS.Commutator.Whole.XLI HRS.Commutator.Whole.XNRS
variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- the Mikhlin class of order `d+1` with constant `A` -/
def mik1_IsMikhlin (d : ℕ) (A : ℝ) (m : EuclideanSpace ℝ (Fin d) → ℂ) : Prop :=
  (∀ ξ : EuclideanSpace ℝ (Fin d), ξ ≠ 0 → ContDiffAt ℝ ∞ m ξ) ∧
  ∀ i ≤ d + 1, ∀ ξ : EuclideanSpace ℝ (Fin d), ξ ≠ 0 →
    ‖iteratedFDeriv ℝ i m ξ‖ ≤ A * ‖ξ‖ ^ (-(i : ℝ))

/-- the dyadic symbol family -/
def mik1_Th (m : 𝔼 → ℂ) (k : ℤ) (η : 𝔼) : ℂ := m (((2 : ℝ) ^ k) • η) * rho η

/-- scaling chain rule: `‖D^i (m (c ·)) η‖ ≤ A ‖η‖^{-i}` -/
lemma mik1_scale_bound {A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) {c : ℝ} (hc : 0 < c)
    {i : ℕ} (hi : i ≤ d + 1) {η : 𝔼} (hη : η ≠ 0) :
    ‖iteratedFDeriv ℝ i (fun y : 𝔼 => m (c • y)) η‖ ≤ A * ‖η‖ ^ (-(i : ℝ)) := by
  set g : 𝔼 →L[ℝ] 𝔼 := c • ContinuousLinearMap.id ℝ 𝔼 with hg
  have hgy : ∀ y, g y = c • y := fun y => by simp [hg]
  have hs : IsOpen ({0}ᶜ : Set 𝔼) := isOpen_compl_singleton
  have hfm : ContDiffOn ℝ ∞ m ({0}ᶜ : Set 𝔼) := fun x hx => (hm.1 x hx).contDiffWithinAt
  have hsg : IsOpen (g ⁻¹' ({0}ᶜ : Set 𝔼)) := hs.preimage g.continuous
  have hgη : g η ∈ ({0}ᶜ : Set 𝔼) := by
    rw [hgy]; simpa [hc.ne'] using hη
  have hle : (i : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
  have h1 := g.iteratedFDerivWithin_comp_right hfm hs.uniqueDiffOn hsg.uniqueDiffOn hgη hle
  have hcomp : (m ∘ ⇑g) = fun y : 𝔼 => m (c • y) := by funext y; simp [hgy]
  rw [hcomp, iteratedFDerivWithin_of_isOpen i hsg (show η ∈ g ⁻¹' ({0}ᶜ : Set 𝔼) from hgη),
    iteratedFDerivWithin_of_isOpen i hs hgη] at h1
  rw [h1]
  have hgn : ‖g‖ ≤ c := by
    calc ‖g‖ = ‖c‖ * ‖ContinuousLinearMap.id ℝ 𝔼‖ := norm_smul _ _
      _ ≤ ‖c‖ * 1 := by gcongr; exact ContinuousLinearMap.norm_id_le
      _ = c := by rw [mul_one, Real.norm_of_nonneg hc.le]
  have h2 := ContinuousMultilinearMap.norm_compContinuousLinearMap_le
    (iteratedFDeriv ℝ i m (g η)) (fun _ : Fin i => g)
  have h3 : ∏ _j : Fin i, ‖g‖ ≤ c ^ i := by
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
    exact pow_le_pow_left₀ (norm_nonneg _) hgn _
  have hne : g η ≠ 0 := hgη
  have h4 := hm.2 i hi (g η) hne
  have hn : ‖g η‖ = c * ‖η‖ := by
    rw [hgy, norm_smul, Real.norm_of_nonneg hc.le]
  rw [hn] at h4
  calc ‖(iteratedFDeriv ℝ i m (g η)).compContinuousLinearMap fun _ => g‖
      ≤ ‖iteratedFDeriv ℝ i m (g η)‖ * ∏ _j : Fin i, ‖g‖ := h2
    _ ≤ ‖iteratedFDeriv ℝ i m (g η)‖ * c ^ i := mul_le_mul_of_nonneg_left h3 (norm_nonneg _)
    _ ≤ (A * (c * ‖η‖) ^ (-(i : ℝ))) * c ^ i := mul_le_mul_of_nonneg_right h4 (pow_nonneg hc.le _)
    _ = A * ‖η‖ ^ (-(i : ℝ)) := by
        rw [Real.mul_rpow hc.le (norm_nonneg _), Real.rpow_neg hc.le, Real.rpow_natCast]
        have : c ^ i ≠ 0 := pow_ne_zero _ hc.ne'
        field_simp

lemma mik1_Th_contDiff {m : 𝔼 → ℂ} (hm : ∀ ξ : 𝔼, ξ ≠ 0 → ContDiffAt ℝ ∞ m ξ) (k : ℤ) :
    ContDiff ℝ ∞ (mik1_Th m k) := by
  refine cmxMY_contDiff_of_away_real (r := 1 / 2) (by norm_num) (fun η hη => ?_) (fun η hη => ?_)
  · have hc : (2 : ℝ) ^ k ≠ 0 := zpow_ne_zero _ (by norm_num)
    have h1 : ContDiffAt ℝ ∞ (fun y : 𝔼 => m (((2 : ℝ) ^ k) • y)) η := by
      have h0 : ((2 : ℝ) ^ k) • η ≠ 0 := by simpa [hc] using hη
      exact (hm _ h0).comp η ((contDiff_const_smul ((2 : ℝ) ^ k)).contDiffAt)
    exact h1.mul rho_contDiff.contDiffAt
  · simp [mik1_Th, rho_eq_zero_of_le hη.le]

lemma mik1_Th_supp (m : 𝔼 → ℂ) (k : ℤ) {η : 𝔼} (h : (2 : ℝ) < ‖η‖) : mik1_Th m k η = 0 := by
  simp [mik1_Th, rho_eq_zero_of_ge h.le]

lemma mik1_Th_zero_near (m : 𝔼 → ℂ) (k : ℤ) {η : 𝔼} (h : ‖η‖ < 1 / 2) (i : ℕ) :
    iteratedFDeriv ℝ i (mik1_Th m k) η = 0 := by
  have hnhds : {y : 𝔼 | ‖y‖ < 1 / 2} ∈ 𝓝 η :=
    (isOpen_lt (f := fun y : 𝔼 => ‖y‖) continuous_norm continuous_const).mem_nhds h
  have hev : mik1_Th m k =ᶠ[𝓝 η] fun _ => (0 : ℂ) := by
    filter_upwards [hnhds] with y hy
    simp [mik1_Th, rho_eq_zero_of_le (le_of_lt (show ‖y‖ < 1 / 2 from hy))]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · have h0 : mik1_Th m k η = 0 := hev.eq_of_nhds
    ext x
    simp [h0]
  · have hev' : mik1_Th m k =ᶠ[𝓝[Set.univ] η] fun _ => (0 : ℂ) := by rwa [nhdsWithin_univ]
    have := Filter.EventuallyEq.iteratedFDerivWithin_eq (𝕜 := ℝ) hev' hev.eq_of_nhds i
    rw [iteratedFDerivWithin_univ, iteratedFDerivWithin_univ] at this
    rw [this]
    simp [iteratedFDeriv_const_of_ne hi.ne']

/-- the derivative bound of the symbol family, with a constant depending only on `d` -/
lemma mik1_Th_bound : ∃ c0 : ℝ, 0 ≤ c0 ∧ ∀ (A : ℝ) (m : 𝔼 → ℂ), 0 ≤ A → mik1_IsMikhlin d A m →
    ∀ (k : ℤ) (i : ℕ), i ≤ d + 1 → ∀ η : 𝔼, ‖iteratedFDeriv ℝ i (mik1_Th m k) η‖ ≤ c0 * A := by
  obtain ⟨M, hM0, hM⟩ := (symFam_rho (d := d)).bdd
  refine ⟨3 ^ (d + 1) * M, by positivity, ?_⟩
  intro A m hA hm k i hi η
  by_cases hη : ‖η‖ < 1 / 2
  · rw [mik1_Th_zero_near m k hη i, norm_zero]
    positivity
  · push Not at hη
    have hη0 : η ≠ 0 := by
      intro h; subst h; norm_num at hη
    have hc : 0 < (2 : ℝ) ^ k := zpow_pos (by norm_num) k
    have hs : IsOpen ({0}ᶜ : Set 𝔼) := isOpen_compl_singleton
    have hf : ContDiffOn ℝ ∞ (fun y : 𝔼 => m (((2 : ℝ) ^ k) • y)) ({0}ᶜ : Set 𝔼) := by
      intro y hy
      have h0 : ((2 : ℝ) ^ k) • y ≠ 0 := by simpa [hc.ne'] using hy
      exact ((hm.1 _ h0).comp y ((contDiff_const_smul ((2 : ℝ) ^ k)).contDiffAt)).contDiffWithinAt
    have hg : ContDiffOn ℝ ∞ (rho : 𝔼 → ℂ) ({0}ᶜ : Set 𝔼) := rho_contDiff.contDiffOn
    have hle : (i : ℕ∞ω) ≤ (∞ : ℕ∞ω) := by exact_mod_cast le_top
    have h1 := norm_iteratedFDerivWithin_mul_le hf hg hs.uniqueDiffOn hη0 hle
    have e : (mik1_Th m k) = fun y : 𝔼 => m (((2 : ℝ) ^ k) • y) * rho y := rfl
    rw [iteratedFDerivWithin_of_isOpen i hs hη0, ← e] at h1
    have h2 : ∀ j ∈ Finset.range (i + 1), (i.choose j : ℝ) *
        ‖iteratedFDerivWithin ℝ j (fun y : 𝔼 => m (((2 : ℝ) ^ k) • y)) ({0}ᶜ : Set 𝔼) η‖ *
        ‖iteratedFDerivWithin ℝ (i - j) (rho : 𝔼 → ℂ) ({0}ᶜ : Set 𝔼) η‖ ≤
        (i.choose j : ℝ) * (A * 2 ^ j) * M := by
      intro j hj
      have hj' : j ≤ i := Nat.lt_succ_iff.1 (Finset.mem_range.1 hj)
      rw [iteratedFDerivWithin_of_isOpen j hs hη0, iteratedFDerivWithin_of_isOpen (i - j) hs hη0]
      have hb1 := mik1_scale_bound hm hc (i := j) (by omega) hη0
      have hb2 : A * ‖η‖ ^ (-(j : ℝ)) ≤ A * 2 ^ j := by
        gcongr
        rw [Real.rpow_neg (norm_nonneg _), Real.rpow_natCast]
        have hp : (0 : ℝ) < (1 / 2) ^ j := by positivity
        calc (‖η‖ ^ j)⁻¹ ≤ ((1 / 2 : ℝ) ^ j)⁻¹ := by
              exact inv_anti₀ hp (pow_le_pow_left₀ (by norm_num) hη _)
          _ = 2 ^ j := by rw [one_div, inv_pow, inv_inv]
      have hb3 := hM 0 (i - j) (by omega) η
      gcongr
      exact hb1.trans hb2
    calc ‖iteratedFDeriv ℝ i (mik1_Th m k) η‖
        ≤ ∑ j ∈ Finset.range (i + 1), (i.choose j : ℝ) * (A * 2 ^ j) * M :=
          h1.trans (Finset.sum_le_sum h2)
      _ = A * M * ∑ j ∈ Finset.range (i + 1), (2 : ℝ) ^ j * (i.choose j : ℝ) := by
          rw [Finset.mul_sum]
          exact Finset.sum_congr rfl fun j _ => by ring
      _ = A * M * 3 ^ i := by
          have := add_pow (2 : ℝ) 1 i
          simp only [one_pow, mul_one] at this
          rw [show (3 : ℝ) = 2 + 1 by norm_num, this]
      _ ≤ A * M * 3 ^ (d + 1) := by
          gcongr
          norm_num
      _ = 3 ^ (d + 1) * M * A := by ring

/-- the symbol family of a Mikhlin symbol is a `SymFam 2`, with the derivative bound `c0 * A` -/
lemma mik1_symFam {c0 A : ℝ} {m : 𝔼 → ℂ} (hm : mik1_IsMikhlin d A m) (hA : 0 ≤ A) (hc0 : 0 ≤ c0)
    (hb : ∀ (k : ℤ) (i : ℕ), i ≤ d + 1 → ∀ η : 𝔼, ‖iteratedFDeriv ℝ i (mik1_Th m k) η‖ ≤ c0 * A) :
    SymFam 2 (mik1_Th m) :=
  { smooth := mik1_Th_contDiff hm.1
    supp := fun k _ h => mik1_Th_supp m k h
    bdd := ⟨c0 * A, mul_nonneg hc0 hA, fun k i hi η => hb k i hi η⟩ }

end HRS.CZ.Mik
