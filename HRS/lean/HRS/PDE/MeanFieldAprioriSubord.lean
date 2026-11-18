import HRS.PDE.MeanFieldDefs
import HRS.PDE.MeanFieldAprioriClassical
import HRS.PDE.MeanFieldAprioriHeat
import Mathlib.Analysis.SpecialFunctions.Gamma.Basic

/-!
# A priori bounds for the mean-field equation, packet AP2b: subordination, the three regimes
of `∫ φ Δ(g⋆f) ≤ A ∫ φ`, Nash's inequality, `L^p → L^∞`, and an ODE comparison

Package MF-01, plan `MeanFieldAprioriPlan.md`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ComplexConjugate

namespace HRS.PDE.MFApriori

variable {d : ℕ}

/-! ### Subordination formulas -/

/-- Subordination for `θ < 0`: `λ^{-a} = Γ(a)⁻¹ ∫_0^∞ e^{-λt} t^{a-1} dt` (`λ > 0`). -/
theorem rpow_neg_eq_integral_exp (a : ℝ) (ha : 0 < a) {lam : ℝ} (hlam : 0 < lam) :
    lam ^ (-a) = (Real.Gamma a)⁻¹ * ∫ t in Set.Ioi (0 : ℝ), Real.exp (-lam * t) * t ^ (a - 1) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hlam
  have e : ∀ t : ℝ, Real.exp (-lam * t) * t ^ (a - 1) = t ^ (a - 1) * Real.exp (-(lam * t)) := by
    intro t; rw [mul_comm, neg_mul]
  simp_rw [e]
  rw [h, one_div, Real.inv_rpow hlam.le, ← Real.rpow_neg hlam.le]
  have := (Real.Gamma_pos_of_pos ha).ne'
  field_simp

/-- Integrability of `(1 - e^{-u}) u^{-1-θ/2}` on `(0,∞)` for `0 < θ < 2`. -/
theorem integrableOn_one_sub_exp_rpow (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2) :
    IntegrableOn (fun u : ℝ => (1 - Real.exp (-u)) * u ^ (-1 - θ / 2)) (Ioi 0) := by
  have hmeas : Measurable fun u : ℝ => (1 - Real.exp (-u)) * u ^ (-1 - θ / 2) := by fun_prop
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun u : ℝ => u ^ (-θ / 2)) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (r := -θ / 2) (a := 0) (b := 1)
        (by linarith))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
    refine h1.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioc] with u hu
    have hu0 : 0 < u := hu.1
    have h2 : 0 ≤ 1 - Real.exp (-u) := by
      have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu0.le); linarith
    have h3 : 1 - Real.exp (-u) ≤ u := by
      have := Real.add_one_le_exp (-u); linarith
    have e : u ^ (-θ / 2) = u * u ^ (-1 - θ / 2) := by
      conv_lhs => rw [show -θ / 2 = 1 + (-1 - θ / 2) by ring]
      rw [Real.rpow_add hu0, Real.rpow_one]
    rw [Real.norm_of_nonneg (mul_nonneg h2 (Real.rpow_nonneg hu0.le _)), e]
    exact mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hu0.le _)
  · have h1 : IntegrableOn (fun u : ℝ => u ^ (-1 - θ / 2)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) one_pos
    refine h1.mono' hmeas.aestronglyMeasurable ?_
    filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
    have hu0 : 0 < u := lt_trans one_pos hu
    have h2 : 0 ≤ 1 - Real.exp (-u) := by
      have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu0.le); linarith
    have h3 : 1 - Real.exp (-u) ≤ 1 := by
      have := Real.exp_pos (-u); linarith
    rw [Real.norm_of_nonneg (mul_nonneg h2 (Real.rpow_nonneg hu0.le _))]
    calc (1 - Real.exp (-u)) * u ^ (-1 - θ / 2) ≤ 1 * u ^ (-1 - θ / 2) :=
          mul_le_mul_of_nonneg_right h3 (Real.rpow_nonneg hu0.le _)
      _ = _ := one_mul _

/-- Subordination for `0 < θ < 2`: `λ^{θ/2} = C_θ⁻¹ ∫_0^∞ (1 - e^{-λt}) t^{-1-θ/2} dt`. -/
theorem rpow_eq_integral_one_sub_exp (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2) :
    ∃ Cθ : ℝ, 0 < Cθ ∧ ∀ lam : ℝ, 0 ≤ lam →
      lam ^ (θ / 2) = Cθ⁻¹ * ∫ t in Set.Ioi (0 : ℝ), (1 - Real.exp (-lam * t)) * t ^ (-1 - θ / 2) := by
  set g : ℝ → ℝ := fun u => (1 - Real.exp (-u)) * u ^ (-1 - θ / 2) with hg
  have hint := integrableOn_one_sub_exp_rpow θ hθ0 hθ2
  have hpos : 0 < ∫ u in Ioi (0 : ℝ), g u := by
    rw [setIntegral_pos_iff_support_of_nonneg_ae]
    · have : Function.support g ∩ Ioi 0 = Ioi 0 := by
        ext u
        simp only [Set.mem_inter_iff, Function.mem_support, Set.mem_Ioi, and_iff_right_iff_imp]
        intro hu
        have h2 : 0 < 1 - Real.exp (-u) := by
          have := Real.exp_lt_one_iff.mpr (neg_neg_of_pos hu); linarith
        simp only [hg]
        exact (mul_pos h2 (Real.rpow_pos_of_pos hu _)).ne'
      rw [this]; simp
    · filter_upwards [ae_restrict_mem measurableSet_Ioi] with u hu
      have hu0 : (0 : ℝ) < u := hu
      have h2 : 0 ≤ 1 - Real.exp (-u) := by
        have := Real.exp_le_one_iff.mpr (neg_nonpos.mpr hu0.le); linarith
      exact mul_nonneg h2 (Real.rpow_nonneg hu0.le _)
    · exact hint
  refine ⟨∫ u in Ioi (0 : ℝ), g u, hpos, fun lam hlam => ?_⟩
  rcases hlam.eq_or_lt with h0 | hl
  · subst h0
    simp [Real.zero_rpow (by linarith : θ / 2 ≠ 0)]
  · have hsub := integral_comp_mul_left_Ioi g 0 hl
    simp only [mul_zero] at hsub
    have e : ∀ t : ℝ, 0 < t → g (lam * t) = lam ^ (-1 - θ / 2) *
        ((1 - Real.exp (-lam * t)) * t ^ (-1 - θ / 2)) := by
      intro t ht
      simp only [hg]
      rw [Real.mul_rpow hl.le ht.le, neg_mul]
      ring
    have h1 : ∫ t in Ioi (0 : ℝ), g (lam * t) = lam ^ (-1 - θ / 2) *
        ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-lam * t)) * t ^ (-1 - θ / 2) := by
      rw [← integral_const_mul]
      exact setIntegral_congr_fun measurableSet_Ioi fun t ht => e t ht
    rw [h1] at hsub
    simp only [smul_eq_mul] at hsub
    have hne : lam ^ (-1 - θ / 2) ≠ 0 := (Real.rpow_pos_of_pos hl _).ne'
    have hC : (∫ u in Ioi (0 : ℝ), g u) ≠ 0 := hpos.ne'
    have key : lam ^ (θ / 2) * lam ^ (-1 - θ / 2) = lam⁻¹ := by
      rw [← Real.rpow_add hl, ← Real.rpow_neg_one]; congr 1; ring
    have hI : ∫ t in Ioi (0 : ℝ), (1 - Real.exp (-lam * t)) * t ^ (-1 - θ / 2) =
        (∫ u in Ioi (0 : ℝ), g u) * lam ^ (θ / 2) := by
      apply mul_left_cancel₀ hne
      rw [hsub]
      calc lam⁻¹ * ∫ x in Ioi (0 : ℝ), g x
          = (∫ u in Ioi (0 : ℝ), g u) * (lam ^ (θ / 2) * lam ^ (-1 - θ / 2)) := by rw [key]; ring
        _ = _ := by ring
    rw [hI]
    field_simp

/-! ### ODE comparison for the Alikakos iteration -/

/-- ODE comparison for the Alikakos iteration: `X' ≤ -α X^{1+2/d} + γ X + δ` on `(0,T)` with
`X ≥ 0` continuous on `[0,T]` gives `X ≤ max (X 0) (max (2γ/α)^{d/2} (2δ/α)^{d/(d+2)})`.

**Statement note.**  The plan statement has no hypothesis `1 ≤ d`; for `d = 0` it is false
(`2 / (0 : ℝ) = 0`; take `α = 1, γ = 2, δ = 0, X = 2 eᵗ`).  Per the coordinator's amendment the
hypothesis `hd : 1 ≤ d` is the first explicit argument. -/
theorem le_of_deriv_le_logistic (hd : 1 ≤ d) (X : ℝ → ℝ) (T α γ δ : ℝ) (hα : 0 < α)
    (hγ : 0 ≤ γ) (hδ : 0 ≤ δ)
    (hcont : ContinuousOn X (Set.Icc 0 T)) (hX0 : ∀ t ∈ Set.Icc 0 T, 0 ≤ X t)
    (hder : ∀ t ∈ Set.Ioo 0 T, ∃ X' : ℝ, HasDerivAt X X' t ∧
      X' ≤ -α * X t ^ (1 + 2 / (d : ℝ)) + γ * X t + δ) :
    ∀ t ∈ Set.Icc 0 T, X t ≤ max (X 0) (max ((2 * γ / α) ^ ((d : ℝ) / 2))
      ((2 * δ / α) ^ ((d : ℝ) / ((d : ℝ) + 2)))) := by
  intro t₁ ht₁
  set M := max (X 0) (max ((2 * γ / α) ^ ((d : ℝ) / 2))
      ((2 * δ / α) ^ ((d : ℝ) / ((d : ℝ) + 2)))) with hM
  by_contra hlt
  rw [not_le] at hlt
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd
  have hγα : 0 ≤ 2 * γ / α := by positivity
  have hδα : 0 ≤ 2 * δ / α := by positivity
  have hM1 : (2 * γ / α) ^ ((d : ℝ) / 2) ≤ M :=
    (le_max_left _ _).trans ((le_max_right _ _).trans (le_refl M))
  have hM2 : (2 * δ / α) ^ ((d : ℝ) / ((d : ℝ) + 2)) ≤ M :=
    (le_max_right _ _).trans ((le_max_right _ _).trans (le_refl M))
  have hM0 : X 0 ≤ M := le_max_left _ _
  -- the key inequality: where `X ≥ M`, the right-hand side is nonpositive
  have key : ∀ y : ℝ, M ≤ y → -α * y ^ (1 + 2 / (d : ℝ)) + γ * y + δ ≤ 0 := by
    intro y hy
    have hy0 : 0 ≤ y := le_trans (le_trans (Real.rpow_nonneg hγα _) hM1) hy
    have h1 : 2 * γ / α ≤ y ^ (2 / (d : ℝ)) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hγα _) (hM1.trans hy)
        (show 0 ≤ 2 / (d : ℝ) by positivity)
      rwa [← Real.rpow_mul hγα, show (d : ℝ) / 2 * (2 / (d : ℝ)) = 1 by field_simp,
        Real.rpow_one] at this
    have h2 : 2 * δ / α ≤ y ^ (1 + 2 / (d : ℝ)) := by
      have := Real.rpow_le_rpow (Real.rpow_nonneg hδα _) (hM2.trans hy)
        (show 0 ≤ 1 + 2 / (d : ℝ) by positivity)
      rwa [← Real.rpow_mul hδα, show (d : ℝ) / ((d : ℝ) + 2) * (1 + 2 / (d : ℝ)) = 1 by
        field_simp, Real.rpow_one] at this
    have h3 : y ^ (1 + 2 / (d : ℝ)) = y * y ^ (2 / (d : ℝ)) := by
      rw [Real.rpow_add' hy0 (by positivity), Real.rpow_one]
    have h4 : γ * y ≤ α / 2 * y ^ (1 + 2 / (d : ℝ)) := by
      rw [h3]
      have : γ ≤ α / 2 * y ^ (2 / (d : ℝ)) := by
        rw [div_le_iff₀ hα] at h1; linarith
      nlinarith
    have h5 : δ ≤ α / 2 * y ^ (1 + 2 / (d : ℝ)) := by
      rw [div_le_iff₀ hα] at h2; linarith
    nlinarith
  have hcl : IsClosed (Set.Icc 0 t₁ ∩ X ⁻¹' Set.Iic M) :=
    (hcont.mono (Set.Icc_subset_Icc le_rfl ht₁.2)).preimage_isClosed_of_isClosed isClosed_Icc
      isClosed_Iic
  have hne : (Set.Icc 0 t₁ ∩ X ⁻¹' Set.Iic M).Nonempty :=
    ⟨0, ⟨le_rfl, ht₁.1⟩, hM0⟩
  have hbdd : BddAbove (Set.Icc 0 t₁ ∩ X ⁻¹' Set.Iic M) := ⟨t₁, fun t ht => ht.1.2⟩
  set t₀ := sSup (Set.Icc 0 t₁ ∩ X ⁻¹' Set.Iic M) with ht₀
  have ht₀mem : t₀ ∈ Set.Icc 0 t₁ ∩ X ⁻¹' Set.Iic M := hcl.csSup_mem hne hbdd
  have ht₀lt : t₀ < t₁ := by
    refine lt_of_le_of_ne ht₀mem.1.2 fun h => ?_
    have := ht₀mem.2
    simp only [Set.mem_preimage, Set.mem_Iic] at this
    rw [h] at this
    linarith
  have hgt : ∀ t ∈ Set.Ioc t₀ t₁, M < X t := by
    intro t ht
    by_contra hle
    rw [not_lt] at hle
    have : t ∈ Set.Icc 0 t₁ ∩ X ⁻¹' Set.Iic M := ⟨⟨ht₀mem.1.1.trans ht.1.le, ht.2⟩, hle⟩
    exact absurd (le_csSup hbdd this) (not_le.mpr ht.1)
  have hanti : AntitoneOn X (Set.Icc t₀ t₁) := by
    refine antitoneOn_of_deriv_nonpos (convex_Icc t₀ t₁) ?_ ?_ ?_
    · exact hcont.mono (Set.Icc_subset_Icc ht₀mem.1.1 ht₁.2)
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨X', hX', _⟩ := hder t ⟨ht₀mem.1.1.trans_lt ht.1, ht.2.trans_le ht₁.2⟩
      exact hX'.differentiableAt.differentiableWithinAt
    · intro t ht
      rw [interior_Icc] at ht
      obtain ⟨X', hX', hle⟩ := hder t ⟨ht₀mem.1.1.trans_lt ht.1, ht.2.trans_le ht₁.2⟩
      rw [hX'.deriv]
      exact hle.trans (key _ (hgt t ⟨ht.1, ht.2.le⟩).le)
  have := hanti ⟨le_rfl, ht₀lt.le⟩ ⟨ht₀lt.le, le_rfl⟩ ht₀lt.le
  have h6 := ht₀mem.2
  simp only [Set.mem_preimage, Set.mem_Iic] at h6
  linarith

/-! ### `L^p` norms control the sup norm -/

/-- `L^p` norms of a continuous function control its sup norm:
if `∫ |u|^p ≤ M Λ^p` for all large `p` (with `M` independent of `p`) then `|u| ≤ Λ`. -/
theorem abs_le_of_integral_pow_le {u : Torus d → ℝ} (hu : Continuous u) (Λ M : ℝ) (hΛ : 0 ≤ Λ)
    (hM : 0 ≤ M) (p₀ : ℕ) (h : ∀ p : ℕ, p₀ ≤ p → ∫ x, |u x| ^ p ≤ M * Λ ^ p) :
    ∀ x, |u x| ≤ Λ := by
  intro x₀
  by_contra hlt
  rw [not_le] at hlt
  set a := (|u x₀| + Λ) / 2 with ha
  have haΛ : Λ < a := by rw [ha]; linarith
  have hax : a < |u x₀| := by rw [ha]; linarith
  have ha0 : 0 < a := lt_of_le_of_lt hΛ haΛ
  set U : Set (Torus d) := {x | a < |u x|} with hU
  have hUo : IsOpen U := isOpen_lt continuous_const hu.abs
  have hUne : U.Nonempty := ⟨x₀, hax⟩
  have hμ : 0 < (volume U).toReal := by
    have h1 : 0 < volume U := hUo.measure_pos volume hUne
    exact ENNReal.toReal_pos h1.ne' (measure_ne_top _ _)
  set μ₀ := (volume U).toReal with hμ₀
  have hlow : ∀ p : ℕ, μ₀ * a ^ p ≤ ∫ x, |u x| ^ p := by
    intro p
    have hint : Integrable (fun x : Torus d => |u x| ^ p) :=
      (hu.abs.pow p).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hind : Integrable (U.indicator fun _ => a ^ p) :=
      (integrable_const _).indicator hUo.measurableSet
    have h1 : ∫ x, U.indicator (fun _ => a ^ p) x ≤ ∫ x, |u x| ^ p := by
      refine integral_mono hind hint fun x => ?_
      by_cases hx : x ∈ U
      · rw [Set.indicator_of_mem hx]
        exact pow_le_pow_left₀ ha0.le (le_of_lt hx) p
      · rw [Set.indicator_of_notMem hx]; positivity
    rw [integral_indicator_const _ hUo.measurableSet] at h1
    simpa [mul_comm, hμ₀, Measure.real] using h1
  rcases hΛ.eq_or_lt with h0 | hΛpos
  · subst h0
    have := (hlow (max p₀ 1)).trans (h (max p₀ 1) (le_max_left _ _))
    rw [zero_pow (by omega), mul_zero] at this
    have : 0 < μ₀ * a ^ (max p₀ 1) := by positivity
    linarith
  · have hr : 1 < a / Λ := by rw [lt_div_iff₀ hΛpos]; linarith
    have ht := tendsto_pow_atTop_atTop_of_one_lt hr
    have hev : ∀ᶠ p : ℕ in atTop, M / μ₀ + 1 ≤ (a / Λ) ^ p := ht.eventually_ge_atTop _
    obtain ⟨p, hp1, hp2⟩ := ((hev.and (eventually_ge_atTop p₀))).exists
    have h1 := (hlow p).trans (h p hp2)
    have h2 : μ₀ * (a / Λ) ^ p * Λ ^ p ≤ M * Λ ^ p := by
      rw [div_pow]
      have : μ₀ * (a ^ p / Λ ^ p) * Λ ^ p = μ₀ * a ^ p := by
        field_simp
      rw [this]; exact h1
    have h3 : μ₀ * (a / Λ) ^ p ≤ M := le_of_mul_le_mul_right h2 (by positivity)
    have h4 : M ≤ μ₀ * (M / μ₀) := by rw [mul_div_cancel₀ _ hμ.ne']
    nlinarith

/-! ### Nash's inequality in Fourier form -/

theorem abs_coord_le_enorm (k : Lattice d) (i : Fin d) : |(k i : ℝ)| ≤ Lattice.enorm k := by
  have := PiLp.norm_apply_le (Lattice.toEuc k) i
  simpa [Lattice.toEuc, Lattice.enorm] using this

/-- The box `[-m,m]^d ⊂ ℤ^d`. -/
def latBox (d m : ℕ) : Finset (Lattice d) :=
  Fintype.piFinset fun _ : Fin d => Finset.Icc (-(m : ℤ)) m

theorem card_latBox (m : ℕ) : (latBox d m).card = (2 * m + 1) ^ d := by
  unfold latBox
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  congr 1
  omega

theorem enorm_gt_of_not_mem_latBox {m : ℕ} {k : Lattice d} (hk : k ∉ latBox d m) :
    (m : ℝ) + 1 ≤ Lattice.enorm k := by
  unfold latBox at hk
  rw [Fintype.mem_piFinset] at hk
  push Not at hk
  obtain ⟨i, hi⟩ := hk
  rw [Finset.mem_Icc, not_and_or] at hi
  have h1 : (m : ℝ) + 1 ≤ |(k i : ℝ)| := by
    rcases hi with h | h
    · have : k i ≤ -(m : ℤ) - 1 := by omega
      have h2 : ((k i : ℤ) : ℝ) ≤ -(m : ℝ) - 1 := by exact_mod_cast this
      rw [abs_of_neg (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])]
      linarith
    · have : (m : ℤ) + 1 ≤ k i := by omega
      have h2 : (m : ℝ) + 1 ≤ ((k i : ℤ) : ℝ) := by exact_mod_cast this
      rw [abs_of_pos (by linarith [(Nat.cast_nonneg m : (0 : ℝ) ≤ m)])]
      exact h2
  exact h1.trans (abs_coord_le_enorm k i)

/-- The basic splitting: for `R ≥ 1`, `‖c‖₂² ≤ (3R)^d M² + (4π²R²)⁻¹ ∑ (2π|k|)²|c_k|²`. -/
theorem sum_sq_le_split (c : Coeff d) (hs1 : Summable fun k => ‖c k‖ ^ 2)
    (hs2 : Summable fun k => (2 * Real.pi * Lattice.enorm k) ^ 2 * ‖c k‖ ^ 2)
    (M : ℝ) (hM : 0 ≤ M) (hc : ∀ k, ‖c k‖ ≤ M) (R : ℝ) (hR : 1 ≤ R) :
    ∑' k, ‖c k‖ ^ 2 ≤ (3 * R) ^ d * M ^ 2 +
      (4 * Real.pi ^ 2 * R ^ 2)⁻¹ * ∑' k, (2 * Real.pi * Lattice.enorm k) ^ 2 * ‖c k‖ ^ 2 := by
  set m := ⌊R⌋₊ with hm
  have hmR : (m : ℝ) ≤ R := Nat.floor_le (by linarith)
  have hRm : R < m + 1 := Nat.lt_floor_add_one R
  have hm1 : (1 : ℝ) ≤ m := by
    have : 1 ≤ m := Nat.le_floor (by simpa using hR)
    exact_mod_cast this
  have hpi : 0 < 4 * Real.pi ^ 2 * R ^ 2 := by positivity
  set S := latBox d m with hS
  have hpt : ∀ k, ‖c k‖ ^ 2 ≤ (if k ∈ S then M ^ 2 else 0) +
      (4 * Real.pi ^ 2 * R ^ 2)⁻¹ * ((2 * Real.pi * Lattice.enorm k) ^ 2 * ‖c k‖ ^ 2) := by
    intro k
    have hnn : 0 ≤ (4 * Real.pi ^ 2 * R ^ 2)⁻¹ * ((2 * Real.pi * Lattice.enorm k) ^ 2 * ‖c k‖ ^ 2) := by
      positivity
    by_cases hk : k ∈ S
    · rw [if_pos hk]
      have : ‖c k‖ ^ 2 ≤ M ^ 2 := pow_le_pow_left₀ (norm_nonneg _) (hc k) 2
      linarith
    · rw [if_neg hk, zero_add]
      have h1 : R ≤ Lattice.enorm k := by
        have := enorm_gt_of_not_mem_latBox hk
        linarith
      have h2 : 4 * Real.pi ^ 2 * R ^ 2 ≤ (2 * Real.pi * Lattice.enorm k) ^ 2 := by
        have : (2 * Real.pi * R) ^ 2 ≤ (2 * Real.pi * Lattice.enorm k) ^ 2 :=
          pow_le_pow_left₀ (by positivity) (by gcongr) 2
        nlinarith
      rw [← div_eq_inv_mul, le_div_iff₀ hpi]
      nlinarith [sq_nonneg ‖c k‖]
  have hfin : Summable fun k : Lattice d => (if k ∈ S then M ^ 2 else 0) :=
    (hasSum_sum_of_ne_finset_zero (s := S) (f := fun k : Lattice d => (if k ∈ S then M ^ 2 else 0))
      (fun k hk => by simp [hk])).summable
  calc ∑' k, ‖c k‖ ^ 2 ≤ ∑' k, ((if k ∈ S then M ^ 2 else 0) +
        (4 * Real.pi ^ 2 * R ^ 2)⁻¹ * ((2 * Real.pi * Lattice.enorm k) ^ 2 * ‖c k‖ ^ 2)) :=
        hs1.tsum_le_tsum hpt (hfin.add (hs2.mul_left _))
    _ = (∑' k : Lattice d, (if k ∈ S then M ^ 2 else 0)) +
        (4 * Real.pi ^ 2 * R ^ 2)⁻¹ * ∑' k, (2 * Real.pi * Lattice.enorm k) ^ 2 * ‖c k‖ ^ 2 := by
        rw [Summable.tsum_add hfin (hs2.mul_left _), tsum_mul_left]
    _ ≤ _ := by
        have h1 : ∑' k : Lattice d, (if k ∈ S then M ^ 2 else 0) = (2 * m + 1) ^ d * M ^ 2 := by
          rw [tsum_eq_sum (s := S) (fun k hk => by simp [hk])]
          rw [Finset.sum_congr rfl (fun k hk => if_pos hk), Finset.sum_const, hS, card_latBox,
            nsmul_eq_mul]
          push_cast
          ring
        rw [h1]
        gcongr
        have : (2 * (m : ℝ) + 1) ≤ 3 * R := by linarith
        exact this

/-- Nash's inequality in Fourier form (`M ≥ sup_k |ĉ(k)|`, e.g. `M = ‖f‖_{L¹}`):
`‖c‖₂^{2(d+2)} ≤ C M⁴ (‖∇c‖₂² + M²)^d`. -/
theorem nash_fourier (hd : 1 ≤ d) : ∃ C : ℝ, 0 < C ∧ ∀ c : Coeff d, MemHs 1 c →
    ∀ M : ℝ, 0 ≤ M → (∀ k, ‖c k‖ ≤ M) →
      hsNormSq 0 c ^ (d + 2) ≤ C * M ^ 4 *
        (hsNormSq 0 (fun k => ((2 * Real.pi * Lattice.enorm k : ℝ) : ℂ) * c k) + M ^ 2) ^ d := by
  refine ⟨(3 ^ d + 1) ^ (d + 2), by positivity, fun c hc M hM hcM => ?_⟩
  have hw : ∀ k : Lattice d, 1 ≤ sobWeight 1 k := by
    intro k
    unfold sobWeight
    rw [Real.rpow_one]
    nlinarith [sq_nonneg (Real.pi * Lattice.enorm k)]
  have hs1 : Summable fun k => ‖c k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => by simpa using mul_le_mul_of_nonneg_right (hw k) (sq_nonneg ‖c k‖)) hc
  have hs2 : Summable fun k => (2 * Real.pi * Lattice.enorm k) ^ 2 * ‖c k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => by positivity)
      (fun k => by
        have : (2 * Real.pi * Lattice.enorm k) ^ 2 ≤ sobWeight 1 k := by
          unfold sobWeight; rw [Real.rpow_one]; nlinarith
        exact mul_le_mul_of_nonneg_right this (sq_nonneg _)) hc
  have e1 : hsNormSq 0 c = ∑' k, ‖c k‖ ^ 2 := by
    unfold hsNormSq; simp [sobWeight_zero]
  have e2 : hsNormSq 0 (fun k => ((2 * Real.pi * Lattice.enorm k : ℝ) : ℂ) * c k) =
      ∑' k, (2 * Real.pi * Lattice.enorm k) ^ 2 * ‖c k‖ ^ 2 := by
    unfold hsNormSq
    refine tsum_congr fun k => ?_
    rw [sobWeight_zero, one_mul, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs, sq_abs]
  rw [e1, e2]
  set A := ∑' k, ‖c k‖ ^ 2 with hA
  set B := ∑' k, (2 * Real.pi * Lattice.enorm k) ^ 2 * ‖c k‖ ^ 2 with hB
  have hA0 : 0 ≤ A := tsum_nonneg fun k => by positivity
  have hB0 : 0 ≤ B := tsum_nonneg fun k => by positivity
  rcases hM.eq_or_lt with h0 | hMpos
  · subst h0
    have : A = 0 := by
      have h : ∀ k, ‖c k‖ ^ 2 = 0 := fun k => by
        have := hcM k
        rw [le_antisymm this (norm_nonneg _)]; simp
      simp [hA, h]
    rw [this, zero_pow (by omega)]
    positivity
  · set X := B + M ^ 2 with hX
    have hM2 : 0 < M ^ 2 := by positivity
    have hX1 : M ^ 2 ≤ X := by linarith
    have hq : 1 ≤ X / M ^ 2 := by rw [le_div_iff₀ hM2]; linarith
    set R := (X / M ^ 2) ^ ((1 : ℝ) / ((d : ℝ) + 2)) with hR
    have hR1 : 1 ≤ R := Real.one_le_rpow hq (by positivity)
    have hRpos : 0 < R := by linarith
    have hRp : R ^ (d + 2) = X / M ^ 2 := by
      rw [hR, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
      have : (1 : ℝ) / ((d : ℝ) + 2) * ((d + 2 : ℕ) : ℝ) = 1 := by
        push_cast; field_simp
      rw [this, Real.rpow_one]
    have hsplit := sum_sq_le_split c hs1 hs2 M hM hcM R hR1
    have h4 : (4 * Real.pi ^ 2 * R ^ 2)⁻¹ * B ≤ M ^ 2 * R ^ d := by
      have h1 : (4 * Real.pi ^ 2 * R ^ 2)⁻¹ ≤ (R ^ 2)⁻¹ := by
        apply inv_anti₀ (by positivity)
        have hp : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
        nlinarith [mul_le_mul_of_nonneg_right hp (sq_nonneg R)]
      calc (4 * Real.pi ^ 2 * R ^ 2)⁻¹ * B ≤ (R ^ 2)⁻¹ * X :=
            mul_le_mul h1 (by linarith) hB0 (by positivity)
        _ = M ^ 2 * R ^ d := by
            have : X = M ^ 2 * R ^ (d + 2) := by rw [hRp]; field_simp
            rw [this]; field_simp; ring
    have hA' : A ≤ (3 ^ d + 1) * (M ^ 2 * R ^ d) := by
      calc A ≤ _ := hsplit
        _ ≤ (3 * R) ^ d * M ^ 2 + M ^ 2 * R ^ d := by gcongr
        _ = _ := by rw [mul_pow]; ring
    calc A ^ (d + 2) ≤ ((3 ^ d + 1) * (M ^ 2 * R ^ d)) ^ (d + 2) := pow_le_pow_left₀ hA0 hA' _
      _ = (3 ^ d + 1) ^ (d + 2) * M ^ 4 * X ^ d := by
          have : ((3 ^ d + 1) * (M ^ 2 * R ^ d)) ^ (d + 2) =
              (3 ^ d + 1) ^ (d + 2) * ((M ^ 2) ^ (d + 2) * (R ^ (d + 2)) ^ d) := by
            rw [mul_pow, mul_pow, ← pow_mul, ← pow_mul, ← pow_mul, mul_comm d (d + 2)]
          rw [this, hRp, div_pow]
          field_simp
          ring

/-! ### Fourier-side tools for the pairing bound -/

/-- `λ_k = 4π²|k|²`. -/
def lamK (k : Lattice d) : ℝ := 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2

theorem lamK_nonneg (k : Lattice d) : 0 ≤ lamK k := by unfold lamK; positivity

theorem enorm_nonneg' (k : Lattice d) : 0 ≤ Lattice.enorm k := norm_nonneg _

theorem lamK_zero : lamK (0 : Lattice d) = 0 := by
  have h : Lattice.toEuc (0 : Lattice d) = 0 := by
    ext i; simp [Lattice.toEuc]
  have : Lattice.enorm (0 : Lattice d) = 0 := by
    unfold Lattice.enorm; rw [h]; simp
  unfold lamK; rw [this]; simp

theorem four_pi_sq_le_lamK {k : Lattice d} (hk : k ≠ 0) : 4 * Real.pi ^ 2 ≤ lamK k := by
  have h1 := one_le_enorm k hk
  unfold lamK
  nlinarith [sq_nonneg Real.pi, mul_nonneg (sq_nonneg Real.pi) (sub_nonneg.mpr h1)]

theorem heatMult_eq_exp (t : ℝ) (k : Lattice d) : heatMult t k = Real.exp (-lamK k * t) := rfl

theorem heatMult_zero (t : ℝ) : heatMult t (0 : Lattice d) = 1 := by
  rw [heatMult_eq_exp, lamK_zero]; simp

theorem heatMult_le_one {t : ℝ} (ht : 0 ≤ t) (k : Lattice d) : heatMult t k ≤ 1 := by
  rw [heatMult_eq_exp, Real.exp_le_one_iff]
  nlinarith [lamK_nonneg k]

/-- The multiplier `λ_k ĝ(k)` of `Δ(g ⋆ ·)`. -/
def mK (d : ℕ) (s : ℝ) (k : Lattice d) : ℝ := lamK k * rieszCoeff d s k

theorem laplaceRieszCoeff_apply (s : ℝ) (c : Coeff d) (k : Lattice d) :
    laplaceRieszCoeff d s c k = -((mK d s k : ℝ) : ℂ) * c k := by
  unfold laplaceRieszCoeff laplaceCoeff rieszMult mK lamK
  push_cast
  ring

theorem norm_laplaceRieszCoeff (s : ℝ) (hr : ∀ k, 0 ≤ rieszCoeff d s k) (c : Coeff d)
    (k : Lattice d) : ‖laplaceRieszCoeff d s c k‖ = mK d s k * ‖c k‖ := by
  rw [laplaceRieszCoeff_apply, norm_mul, norm_neg, Complex.norm_real, Real.norm_of_nonneg]
  unfold mK
  exact mul_nonneg (lamK_nonneg k) (hr k)

theorem mK_nonneg {s : ℝ} (hr : ∀ k, 0 ≤ rieszCoeff d s k) (k : Lattice d) : 0 ≤ mK d s k :=
  mul_nonneg (lamK_nonneg k) (hr k)

theorem mK_zero (s : ℝ) : mK d s (0 : Lattice d) = 0 := by
  unfold mK; rw [lamK_zero]; simp

/-- For `k ≠ 0`: `λ_k ĝ(k) = c_{d,s} λ_k^{θ/2}` with `θ = s + 2 - d`. -/
theorem mK_eq_rpow (s : ℝ) {k : Lattice d} (hk : k ≠ 0) :
    mK d s k = rieszConst d s * lamK k ^ ((s + 2 - (d : ℝ)) / 2) := by
  have h1 : 0 < Lattice.enorm k := lt_of_lt_of_le one_pos (one_le_enorm k hk)
  have hx : 0 < 2 * Real.pi * Lattice.enorm k := by positivity
  have hl : lamK k = (2 * Real.pi * Lattice.enorm k) ^ (2 : ℝ) := by
    unfold lamK; rw [Real.rpow_two]; ring
  unfold mK rieszCoeff
  rw [if_neg hk, hl, ← Real.rpow_mul hx.le]
  rw [show (2 : ℝ) * ((s + 2 - (d : ℝ)) / 2) = (s - d) + 2 by ring, Real.rpow_add hx,
    ← hl]
  ring

theorem rieszConst_pos (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) : 0 < rieszConst d s := by
  have hd' : (0 : ℝ) < d := by exact_mod_cast hd
  unfold rieszConst
  split_ifs with h
  · exact mul_pos (mul_pos (by positivity) (by positivity)) (Real.Gamma_pos_of_pos (by positivity))
  · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
    refine div_pos (mul_pos (mul_pos (by positivity) (by positivity))
      (Real.Gamma_pos_of_pos (by linarith))) (Real.Gamma_pos_of_pos (by linarith))

theorem rieszCoeff_nonneg' (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (k : Lattice d) :
    0 ≤ rieszCoeff d s k := by
  unfold rieszCoeff
  split_ifs
  · exact le_rfl
  · exact mul_nonneg (rieszConst_pos hd s hs0 hsd).le
      (Real.rpow_nonneg (by have := enorm_nonneg' k; positivity) _)

theorem norm_coeffOf_le {φ : Torus d → ℝ} (k : Lattice d) :
    ‖coeffOf φ k‖ ≤ ∫ x, |φ x| := by
  unfold coeffOf
  rw [funFourierCoeff_eq_int]
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  show ‖Torus.mode (-k) x * (φ x : ℂ)‖ = |φ x|
  rw [norm_mul, Torus.norm_mode, one_mul, Complex.norm_real, Real.norm_eq_abs]

theorem summable_mul_coeffOf {c : Coeff d} (hs : Summable fun k => ‖c k‖) (φ : Torus d → ℝ) :
    Summable fun k => c k * coeffOf φ (-k) := by
  refine Summable.of_norm ?_
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hs.mul_right (∫ x, |φ x|))
  rw [norm_mul]
  exact mul_le_mul_of_nonneg_left (norm_coeffOf_le _) (norm_nonneg _)

/-- `∫ φ · toFun c = Re ∑ c_k φ̂(-k)` for absolutely summable `c`. -/
theorem integral_mul_toFun (c : Coeff d) (hs : Summable fun k => ‖c k‖) {φ : Torus d → ℝ}
    (hφ : Continuous φ) :
    ∫ x, φ x * toFun c x = (∑' k, c k * coeffOf φ (-k)).re := by
  set F : Lattice d → Torus d → ℝ := fun k x => φ x * (c k * Torus.mode k x).re with hF
  have hFc : ∀ k, Continuous (F k) := fun k =>
    hφ.mul (Complex.continuous_re.comp (continuous_const.mul (Torus.continuous_mode k)))
  have hFi : ∀ k, Integrable (F k) := fun k =>
    (hFc k).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hφi : Integrable (fun x => |φ x|) :=
    hφ.abs.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hbd : ∀ k, ∫ x, ‖F k x‖ ≤ ‖c k‖ * ∫ x, |φ x| := by
    intro k
    rw [← integral_const_mul]
    refine integral_mono (hFi k).norm (hφi.const_mul _) fun x => ?_
    simp only [hF, Real.norm_eq_abs, abs_mul]
    have h1 : |(c k * Torus.mode k x).re| ≤ ‖c k‖ := by
      refine (Complex.abs_re_le_norm _).trans ?_
      rw [norm_mul, Torus.norm_mode, mul_one]
    nlinarith [abs_nonneg (φ x)]
  have hsum : Summable fun k => ∫ x, ‖F k x‖ :=
    Summable.of_nonneg_of_le (fun k => integral_nonneg fun x => norm_nonneg _) hbd
      (hs.mul_right _)
  have hsw := hasSum_integral_of_summable_integral_norm hFi hsum
  have h1 : ∀ x, ∑' k, F k x = φ x * toFun c x := by
    intro x
    simp only [hF]
    rw [tsum_mul_left]
    congr 1
    unfold toFun series
    rw [Complex.re_tsum (summable_series_terms c hs x)]
  have h2 : ∀ k, ∫ x, F k x = (c k * coeffOf φ (-k)).re := by
    intro k
    simp only [hF]
    have : ∀ x, φ x * (c k * Torus.mode k x).re = (c k * (φ x * Torus.mode k x)).re := by
      intro x
      rw [show c k * ((φ x : ℂ) * Torus.mode k x) = (φ x : ℂ) * (c k * Torus.mode k x) by ring,
        Complex.re_ofReal_mul]
    simp_rw [this]
    have hint : Integrable (fun x : Torus d => c k * ((φ x : ℂ) * Torus.mode k x)) := by
      refine (continuous_const.mul ((Complex.continuous_ofReal.comp hφ).mul
        (Torus.continuous_mode k))).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have h := integral_re hint
    simp only [RCLike.re_to_complex] at h
    rw [h, integral_const_mul]
    congr 2
    unfold coeffOf
    rw [funFourierCoeff_eq_int]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [neg_neg]
    rw [mul_comm]
    rfl
  have h3 := hsw.tsum_eq
  simp_rw [h1, h2] at h3
  rw [← h3, Complex.re_tsum (summable_mul_coeffOf hs φ)]

/-- Interchange of a series and a subordination integral. -/
theorem tsum_mul_eq_integral {ι : Type*} [Countable ι] (κ : ι → ℝ → ℝ) (w : ℝ → ℝ)
    (γ m : ι → ℝ) (hint : ∀ i, IntegrableOn (fun t => κ i t * w t) (Ioi 0))
    (hnn : ∀ i, ∀ t, 0 < t → 0 ≤ κ i t * w t)
    (hm : ∀ i, m i = ∫ t in Ioi (0 : ℝ), κ i t * w t)
    (hsum : Summable fun i => m i * |γ i|) :
    ∑' i, m i * γ i = ∫ t in Ioi (0 : ℝ), ∑' i, κ i t * w t * γ i := by
  have hFi : ∀ i, Integrable (fun t => κ i t * w t * γ i) (volume.restrict (Ioi (0 : ℝ))) :=
    fun i => (hint i).mul_const _
  have hnorm : ∀ i, ∫ t in Ioi (0 : ℝ), ‖κ i t * w t * γ i‖ = m i * |γ i| := by
    intro i
    have : ∫ t in Ioi (0 : ℝ), ‖κ i t * w t * γ i‖ = ∫ t in Ioi (0 : ℝ), (κ i t * w t) * |γ i| := by
      refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hnn i t ht)]
    rw [this, integral_mul_const, ← hm]
  have hsw := integral_tsum_of_summable_integral_norm hFi (by simpa only [hnorm] using hsum)
  rw [← hsw]
  refine tsum_congr fun i => ?_
  rw [integral_mul_const, ← hm]

/-! ### Facts about the coefficients of a probability density -/

theorem coeffOf_zero_eq (f : Torus d → ℝ) : coeffOf f 0 = ((∫ x, f x : ℝ) : ℂ) := by
  unfold coeffOf
  rw [funFourierCoeff_eq_int, ← integral_complex_ofReal]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [neg_zero]
  show Torus.mode 0 x * (f x : ℂ) = _
  rw [Torus.mode_zero, one_mul]

theorem norm_coeffOf_le_one {f : Torus d → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∫ x, f x = 1)
    (k : Lattice d) : ‖coeffOf f k‖ ≤ 1 := by
  refine (norm_coeffOf_le k).trans (le_of_eq ?_)
  calc ∫ x, |f x| = ∫ x, f x :=
        integral_congr_ae (Filter.Eventually.of_forall fun x => abs_of_nonneg (hf0 x))
    _ = 1 := hf1

theorem abs_re_coeff_mode_le_one {f : Torus d → ℝ} (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∫ x, f x = 1)
    (k : Lattice d) (x : Torus d) : |(coeffOf f k * Torus.mode k x).re| ≤ 1 := by
  refine (Complex.abs_re_le_norm _).trans ?_
  rw [norm_mul, Torus.norm_mode, mul_one]
  exact norm_coeffOf_le_one hf0 hf1 k

theorem integrableOn_exp_rpow (a : ℝ) (ha : 0 < a) {lam : ℝ} (hlam : 0 < lam) :
    IntegrableOn (fun t : ℝ => Real.exp (-lam * t) * t ^ (a - 1)) (Ioi 0) := by
  have h := Real.integral_rpow_mul_exp_neg_mul_Ioi ha hlam
  have hint : IntegrableOn (fun t : ℝ => t ^ (a - 1) * Real.exp (-(lam * t))) (Ioi 0) :=
    .of_integral_ne_zero (by rw [h]; have := Real.Gamma_pos_of_pos ha; positivity)
  refine hint.congr_fun (fun t _ => ?_) measurableSet_Ioi
  simp only
  rw [mul_comm, neg_mul]

theorem integrableOn_one_sub_exp_scaled (θ : ℝ) (hθ0 : 0 < θ) (hθ2 : θ < 2) {lam : ℝ}
    (hlam : 0 ≤ lam) :
    IntegrableOn (fun t : ℝ => (1 - Real.exp (-lam * t)) * t ^ (-1 - θ / 2)) (Ioi 0) := by
  rcases hlam.eq_or_lt with h0 | hl
  · subst h0; simp
  · have h := integrableOn_one_sub_exp_rpow θ hθ0 hθ2
    have h2 := (integrableOn_Ioi_comp_mul_left_iff
      (fun u : ℝ => (1 - Real.exp (-u)) * u ^ (-1 - θ / 2)) 0 hl).mpr (by simpa using h)
    refine IntegrableOn.congr_fun (h2.const_mul ((lam ^ (-1 - θ / 2))⁻¹)) (fun t ht => ?_) measurableSet_Ioi
    have ht0 : (0 : ℝ) < t := ht
    rw [Real.mul_rpow hl.le ht0.le, neg_mul]
    have : lam ^ (-1 - θ / 2) ≠ 0 := (Real.rpow_pos_of_pos hl _).ne'
    field_simp

theorem one_sub_exp_rpow_nonneg {lam t : ℝ} (hlam : 0 ≤ lam) (ht : 0 < t) (θ : ℝ) :
    0 ≤ (1 - Real.exp (-lam * t)) * t ^ (-1 - θ / 2) := by
  have : 0 ≤ 1 - Real.exp (-lam * t) := by
    have := Real.exp_le_one_iff.mpr (show -lam * t ≤ 0 by nlinarith)
    linarith
  exact mul_nonneg this (Real.rpow_nonneg ht.le _)

theorem summable_norm_coeffOf_convFun_heatKer {f : Torus d → ℝ} (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∫ x, f x = 1) {t : ℝ} (ht : 0 < t) (hf : Continuous f) :
    Summable fun k => ‖coeffOf (convFun (heatKer t) f) k‖ := by
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (heatMult_summable ht)
  rw [coeffOf_convFun_heatKer ht hf, norm_mul, Complex.norm_real,
    Real.norm_of_nonneg (heatMult_pos t k).le]
  calc heatMult t k * ‖coeffOf f k‖ ≤ heatMult t k * 1 :=
        mul_le_mul_of_nonneg_left (norm_coeffOf_le_one hf0 hf1 k) (heatMult_pos t k).le
    _ = _ := mul_one _

theorem convFun_heatKer_eq_tsum {f : Torus d → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∫ x, f x = 1) {t : ℝ} (ht : 0 < t) (x : Torus d) :
    convFun (heatKer t) f x = ∑' k, heatMult t k * (coeffOf f k * Torus.mode k x).re := by
  have hc : Continuous (convFun (heatKer t) f) :=
    MFAux.continuous_convFun (integrable_heatKer ht) hf
  have hs := summable_norm_coeffOf_convFun_heatKer hf0 hf1 ht hf
  have h := congrFun (toFun_coeffOf _ hc hs) x
  rw [← h]
  unfold toFun series
  rw [Complex.re_tsum (summable_series_terms _ hs x)]
  refine tsum_congr fun k => ?_
  rw [coeffOf_convFun_heatKer ht hf, mul_assoc, Complex.re_ofReal_mul]

theorem convFun_heatKer_eq_one_add {f : Torus d → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∫ x, f x = 1) {t : ℝ} (ht : 0 < t) (x : Torus d) :
    convFun (heatKer t) f x = 1 +
      ∑' k : NonzeroLattice d, heatMult t k.1 * (coeffOf f k.1 * Torus.mode k.1 x).re := by
  have hsum : Summable fun k : Lattice d => heatMult t k * (coeffOf f k * Torus.mode k x).re := by
    refine Summable.of_norm_bounded (heatMult_summable ht) fun k => ?_
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatMult_pos t k).le]
    calc heatMult t k * |(coeffOf f k * Torus.mode k x).re| ≤ heatMult t k * 1 :=
          mul_le_mul_of_nonneg_left (abs_re_coeff_mode_le_one hf0 hf1 k x) (heatMult_pos t k).le
      _ = _ := mul_one _
  rw [convFun_heatKer_eq_tsum hf hf0 hf1 ht, Torus.tsum_lattice _ hsum, heatMult_zero,
    Torus.mode_zero, mul_one, coeffOf_zero_eq, hf1]
  simp

/-- `1 - H_t ⋆ f ≤ min (1, heatTail)`. -/
theorem one_sub_convFun_heatKer_le {f : Torus d → ℝ} (hd : 1 ≤ d) (hf : Continuous f)
    (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∫ x, f x = 1) {t : ℝ} (ht : 0 < t) (x : Torus d) :
    1 - convFun (heatKer t) f x ≤ 1 ∧ 1 - convFun (heatKer t) f x ≤ heatTail d t := by
  refine ⟨?_, ?_⟩
  · have := convFun_heatKer_nonneg hd ht hf hf0 x
    linarith
  · rw [convFun_heatKer_eq_one_add hf hf0 hf1 ht, sub_add_cancel_left, ← tsum_neg]
    unfold heatTail
    have hs := heatTail_summable hd ht
    refine Summable.tsum_le_tsum (fun k => ?_) ?_ hs
    · have := abs_re_coeff_mode_le_one hf0 hf1 k.1 x
      have h1 := (abs_le.mp this).1
      have h2 := (heatMult_pos t k.1)
      nlinarith
    · refine Summable.neg ?_
      refine Summable.of_norm_bounded hs fun k => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatMult_pos t k.1).le]
      calc heatMult t k.1 * |(coeffOf f k.1 * Torus.mode k.1 x).re| ≤ heatMult t k.1 * 1 :=
            mul_le_mul_of_nonneg_left (abs_re_coeff_mode_le_one hf0 hf1 k.1 x)
              (heatMult_pos t k.1).le
        _ = _ := mul_one _

/-! ### The regime `θ < 0` -/

/-- The envelope `1` on `(0,1]`, `T₁ e^{-4π²(t-1)}` on `(1,∞)`. -/
def tailPsi (T1 t : ℝ) : ℝ := if t ≤ 1 then 1 else T1 * Real.exp (-(4 * Real.pi ^ 2) * (t - 1))

theorem integrableOn_rpow_tailPsi (a : ℝ) (ha : 0 < a) (T1 : ℝ) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * tailPsi T1 t) (Ioi 0) := by
  rw [show Ioi (0 : ℝ) = Ioc 0 1 ∪ Ioi 1 from (Ioc_union_Ioi_eq_Ioi zero_le_one).symm]
  refine IntegrableOn.union ?_ ?_
  · have h1 : IntegrableOn (fun u : ℝ => u ^ (a - 1)) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (r := a - 1) (a := 0) (b := 1)
        (by linarith))
      exact (intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one).mp this
    refine h1.congr_fun (fun t ht => ?_) measurableSet_Ioc
    simp only [tailPsi, if_pos ht.2, mul_one]
  · have hpi : 0 < 4 * Real.pi ^ 2 := by positivity
    have h1 := (integrableOn_exp_rpow a ha hpi).mono_set (Ioi_subset_Ioi zero_le_one)
    refine IntegrableOn.congr_fun (h1.const_mul (T1 * Real.exp (4 * Real.pi ^ 2)))
      (fun t ht => ?_) measurableSet_Ioi
    have ht1 : ¬ t ≤ 1 := not_le.mpr ht
    simp only [tailPsi, if_neg ht1]
    have : Real.exp (-(4 * Real.pi ^ 2) * (t - 1)) =
        Real.exp (4 * Real.pi ^ 2) * Real.exp (-(4 * Real.pi ^ 2) * t) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring

/-- Pointwise formula for `Δ(g⋆f)` when `θ = s + 2 - d < 0`. -/
theorem toFun_laplaceRiesz_of_neg (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hθ : s + 2 - (d : ℝ) < 0) {f : Torus d → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∫ x, f x = 1)
    (hS : Summable fun k => ‖laplaceRieszCoeff d s (coeffOf f) k‖) (x : Torus d) :
    toFun (laplaceRieszCoeff d s (coeffOf f)) x =
      ∫ t in Ioi (0 : ℝ), (rieszConst d s / Real.Gamma (-(s + 2 - (d : ℝ)) / 2)) * t ^ (-(s + 2 - (d : ℝ)) / 2 - 1) *
        (1 - convFun (heatKer t) f x) := by
  set a : ℝ := -(s + 2 - (d : ℝ)) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hΓ : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hrc := rieszConst_pos hd s hs0 hsd
  have hg := rieszCoeff_nonneg' hd s hs0 hsd
  set β : Lattice d → ℝ := fun k => (coeffOf f k * Torus.mode k x).re with hβ
  set w : ℝ → ℝ := fun t => (rieszConst d s / Real.Gamma a) * t ^ (a - 1) with hw
  -- Step 1: toFun as a real series
  have hsumL : Summable fun k : Lattice d => mK d s k * β k := by
    refine Summable.of_norm_bounded hS fun k => ?_
    rw [norm_laplaceRieszCoeff s hg, Real.norm_eq_abs, abs_mul,
      abs_of_nonneg (mK_nonneg hg k)]
    exact mul_le_mul_of_nonneg_left
      ((Complex.abs_re_le_norm _).trans (by rw [norm_mul, Torus.norm_mode, mul_one]))
      (mK_nonneg hg k)
  have h1 : toFun (laplaceRieszCoeff d s (coeffOf f)) x = -∑' k, mK d s k * β k := by
    unfold toFun series
    rw [Complex.re_tsum (summable_series_terms _ hS x), ← tsum_neg]
    refine tsum_congr fun k => ?_
    rw [laplaceRieszCoeff_apply, neg_mul, neg_mul, Complex.neg_re, mul_assoc, Complex.re_ofReal_mul]
  have h2 : ∑' k, mK d s k * β k = ∑' k : NonzeroLattice d, mK d s k.1 * β k.1 := by
    rw [Torus.tsum_lattice _ hsumL, mK_zero, zero_mul, zero_add]
  -- Step 2: the Fubini step
  have hsumNZ : Summable fun k : NonzeroLattice d => mK d s k.1 * |β k.1| := by
    have := (Torus.summable_lattice_iff _).mp hS
    refine Summable.of_nonneg_of_le (fun k => mul_nonneg (mK_nonneg hg _)
      (abs_nonneg _)) (fun k => ?_) this
    rw [norm_laplaceRieszCoeff s hg]
    exact mul_le_mul_of_nonneg_left
      ((Complex.abs_re_le_norm _).trans (by rw [norm_mul, Torus.norm_mode, mul_one]))
      (mK_nonneg hg _)
  have hlam : ∀ k : NonzeroLattice d, 0 < lamK k.1 := fun k =>
    lt_of_lt_of_le (by positivity) (four_pi_sq_le_lamK k.2)
  have hswap := tsum_mul_eq_integral (fun (k : NonzeroLattice d) t => heatMult t k.1) w
    (fun k => β k.1) (fun k => mK d s k.1)
    (fun k => by
      refine IntegrableOn.congr_fun ((integrableOn_exp_rpow a ha (hlam k)).const_mul
        (rieszConst d s / Real.Gamma a)) (fun t ht => ?_) measurableSet_Ioi
      simp only [hw, heatMult_eq_exp]
      ring)
    (fun k t ht => by
      simp only [hw]
      have := heatMult_pos t k.1
      have := Real.rpow_nonneg ht.le (a - 1)
      positivity)
    (fun k => by
      have e := rpow_neg_eq_integral_exp a ha (hlam k)
      have e2 := mK_eq_rpow s k.2
      have e3 : (s + 2 - (d : ℝ)) / 2 = -a := by rw [ha_def]; ring
      rw [e3, e] at e2
      rw [e2]
      simp only [hw, heatMult_eq_exp]
      have : ∀ t : ℝ, Real.exp (-lamK k.1 * t) * (rieszConst d s / Real.Gamma a * t ^ (a - 1)) =
          rieszConst d s / Real.Gamma a * (Real.exp (-lamK k.1 * t) * t ^ (a - 1)) := fun t => by ring
      simp_rw [this]
      rw [integral_const_mul]
      field_simp)
    hsumNZ
  -- Step 3: identify the integrand
  have h3 : ∫ t in Ioi (0 : ℝ), ∑' k : NonzeroLattice d, heatMult t k.1 * w t * β k.1 =
      ∫ t in Ioi (0 : ℝ), -(w t * (1 - convFun (heatKer t) f x)) := by
    refine setIntegral_congr_fun measurableSet_Ioi fun t ht => ?_
    have e : ∀ k : NonzeroLattice d, heatMult t k.1 * w t * β k.1 = w t * (heatMult t k.1 * β k.1) :=
      fun k => by ring
    simp_rw [e]
    rw [tsum_mul_left, convFun_heatKer_eq_one_add hf hf0 hf1 ht x]
    simp only [hβ]
    ring
  rw [h1, h2, hswap, h3, integral_neg, neg_neg]

theorem toFun_eq_zero_of_not_summable (c : Coeff d) (h : ¬ Summable fun k => ‖c k‖)
    (x : Torus d) : toFun c x = 0 := by
  unfold toFun series
  have : ¬ Summable fun k => c k * Torus.mode k x := fun hs => h (by
    simpa [norm_mul, Torus.norm_mode] using summable_norm_iff.mpr hs)
  rw [tsum_eq_zero_of_not_summable this]; simp

/-- The pairing bound in the regime `θ < 0`. -/
theorem laplaceRiesz_pairing_bound_neg (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hθ : s + 2 - (d : ℝ) < 0) :
    ∃ A : ℝ, 0 ≤ A ∧
      ∀ f φ : Torus d → ℝ, Continuous f → MemHs 2 (coeffOf f) → (∀ x, 0 ≤ f x) →
        (∫ x, f x) = 1 → Continuous φ → (∀ x, 0 ≤ φ x) →
        ∫ x, φ x * toFun (laplaceRieszCoeff d s (coeffOf f)) x ≤ A * ∫ x, φ x := by
  set a : ℝ := -(s + 2 - (d : ℝ)) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  have hΓ : 0 < Real.Gamma a := Real.Gamma_pos_of_pos ha
  have hrc := rieszConst_pos hd s hs0 hsd
  set T1 := heatTail d 1 with hT1
  set c0 : ℝ := rieszConst d s / Real.Gamma a with hc0
  have hc0pos : 0 < c0 := div_pos hrc hΓ
  set A : ℝ := ∫ t in Ioi (0 : ℝ), c0 * t ^ (a - 1) * tailPsi T1 t with hA
  have hGb : IntegrableOn (fun t : ℝ => c0 * t ^ (a - 1) * tailPsi T1 t) (Ioi 0) := by
    have := (integrableOn_rpow_tailPsi a ha T1).const_mul c0
    have e : (fun t : ℝ => c0 * t ^ (a - 1) * tailPsi T1 t) =
        fun t => c0 * (t ^ (a - 1) * tailPsi T1 t) := by funext t; ring
    rw [e]; exact this
  have hA0 : 0 ≤ A := by
    refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
    have ht0 : (0 : ℝ) < t := ht
    have hpsi : 0 ≤ tailPsi T1 t := by
      unfold tailPsi
      split_ifs with h
      · exact zero_le_one
      · refine mul_nonneg ?_ (Real.exp_pos _).le
        exact tsum_nonneg fun k => (heatMult_pos _ _).le
    have := Real.rpow_nonneg ht0.le (a - 1)
    positivity
  refine ⟨A, hA0, fun f φ hf hfH hf0 hf1 hφ hφ0 => ?_⟩
  have hg := rieszCoeff_nonneg' hd s hs0 hsd
  by_cases hS : Summable fun k => ‖laplaceRieszCoeff d s (coeffOf f) k‖
  · have hpt : ∀ x, toFun (laplaceRieszCoeff d s (coeffOf f)) x ≤ A := by
      intro x
      rw [toFun_laplaceRiesz_of_neg hd s hs0 hsd hθ hf hf0 hf1 hS x]
      by_cases hG : IntegrableOn (fun t : ℝ => c0 * t ^ (a - 1) * (1 - convFun (heatKer t) f x))
          (Ioi 0)
      · refine setIntegral_mono_on hG hGb measurableSet_Ioi fun t ht => ?_
        have ht0 : (0 : ℝ) < t := ht
        have hr := Real.rpow_nonneg ht0.le (a - 1)
        have hb := one_sub_convFun_heatKer_le hd hf hf0 hf1 ht0 x
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        unfold tailPsi
        split_ifs with h
        · exact hb.1
        · have h1 : 1 ≤ t := (not_le.mp h).le
          exact hb.2.trans (heatTail_le hd h1)
      · rw [integral_undef hG]; exact hA0
    have hc : Continuous (toFun (laplaceRieszCoeff d s (coeffOf f))) := continuous_toFun _ hS
    calc ∫ x, φ x * toFun (laplaceRieszCoeff d s (coeffOf f)) x ≤ ∫ x, φ x * A := by
          refine integral_mono (by
            exact (hφ.mul hc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _))
            ((hφ.mul continuous_const).integrable_of_hasCompactSupport
              (HasCompactSupport.of_compactSpace _)) fun x => ?_
          exact mul_le_mul_of_nonneg_left (hpt x) (hφ0 x)
      _ = A * ∫ x, φ x := by rw [integral_mul_const, mul_comm]
  · have h0 : ∀ x, toFun (laplaceRieszCoeff d s (coeffOf f)) x = 0 :=
      toFun_eq_zero_of_not_summable _ hS
    simp_rw [h0, mul_zero, integral_zero]
    exact mul_nonneg hA0 (integral_nonneg hφ0)

/-! ### The regimes `θ ≥ 0` -/

theorem coeffOf_sub (f g : Torus d → ℝ) (hf : Continuous f) (hg : Continuous g) (k : Lattice d) :
    coeffOf (fun x => f x - g x) k = coeffOf f k - coeffOf g k := by
  have e : (fun x => f x - g x) = fun x => f x + (-1 : ℝ) * g x := by funext x; ring
  rw [e, coeffOf_add f (fun x => (-1 : ℝ) * g x) hf (continuous_const.mul hg), coeffOf_const_mul]
  push_cast; ring

/-- For `θ ≥ 0` and summable `Δ(g⋆f)`-coefficients, the coefficients of `f` are summable. -/
theorem summable_norm_coeffOf_of_nonneg (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hθ : 0 ≤ s + 2 - (d : ℝ)) {c : Coeff d}
    (hS : Summable fun k => ‖laplaceRieszCoeff d s c k‖) : Summable fun k => ‖c k‖ := by
  have hg := rieszCoeff_nonneg' hd s hs0 hsd
  have hrc := rieszConst_pos hd s hs0 hsd
  set m1 : ℝ := rieszConst d s * (4 * Real.pi ^ 2) ^ ((s + 2 - (d : ℝ)) / 2) with hm1
  have hm1pos : 0 < m1 := by rw [hm1]; positivity
  refine (Torus.summable_lattice_iff (fun k => ‖c k‖)).mpr ?_
  have hS' := (Torus.summable_lattice_iff _).mp hS
  refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) (hS'.mul_left m1⁻¹)
  rw [norm_laplaceRieszCoeff s hg, mK_eq_rpow s k.2]
  have h1 : m1 ≤ rieszConst d s * lamK k.1 ^ ((s + 2 - (d : ℝ)) / 2) :=
    mul_le_mul_of_nonneg_left (Real.rpow_le_rpow (by positivity) (four_pi_sq_le_lamK k.2)
      (by linarith)) hrc.le
  rw [inv_mul_eq_div, le_div_iff₀ hm1pos]
  nlinarith [norm_nonneg (c k.1)]

/-- Pairing formula `∫ φ Δ(g⋆f) = -∑ λ_k ĝ(k) Re(f̂_k φ̂(-k))`. -/
theorem integral_mul_toFun_laplaceRiesz (s : ℝ) {c : Coeff d} {φ : Torus d → ℝ}
    (hφ : Continuous φ) (hS : Summable fun k => ‖laplaceRieszCoeff d s c k‖) :
    ∫ x, φ x * toFun (laplaceRieszCoeff d s c) x =
      -∑' k, mK d s k * (c k * coeffOf φ (-k)).re := by
  rw [integral_mul_toFun _ hS hφ, Complex.re_tsum (summable_mul_coeffOf hS φ), ← tsum_neg]
  refine tsum_congr fun k => ?_
  rw [laplaceRieszCoeff_apply, neg_mul, neg_mul, Complex.neg_re, mul_assoc,
    Complex.re_ofReal_mul]

theorem abs_re_mul_coeffOf_le (c : Coeff d) (φ : Torus d → ℝ) (k : Lattice d) :
    |(c k * coeffOf φ (-k)).re| ≤ ‖c k‖ * ∫ x, |φ x| :=
  (Complex.abs_re_le_norm _).trans (by
    rw [norm_mul]; exact mul_le_mul_of_nonneg_left (norm_coeffOf_le _) (norm_nonneg _))

theorem summable_mK_mul_abs (s : ℝ) (hg : ∀ k, 0 ≤ rieszCoeff d s k) (c : Coeff d) (φ : Torus d → ℝ)
    (hS : Summable fun k => ‖laplaceRieszCoeff d s c k‖) :
    Summable fun k => mK d s k * |(c k * coeffOf φ (-k)).re| := by
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (mK_nonneg hg k) (abs_nonneg _))
    (fun k => ?_) (hS.mul_right (∫ x, |φ x|))
  rw [norm_laplaceRieszCoeff s hg, mul_assoc]
  exact mul_le_mul_of_nonneg_left (abs_re_mul_coeffOf_le c φ k) (mK_nonneg hg k)

/-- The regime `θ = 0`. -/
theorem laplaceRiesz_pairing_bound_zero (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hθ : s + 2 - (d : ℝ) = 0) {f φ : Torus d → ℝ} (hf : Continuous f) (hf1 : ∫ x, f x = 1)
    (hφ : Continuous φ) (hmono : ∀ x y, 0 ≤ (φ x - φ y) * (f x - f y))
    (hS : Summable fun k => ‖laplaceRieszCoeff d s (coeffOf f) k‖) :
    ∫ x, φ x * toFun (laplaceRieszCoeff d s (coeffOf f)) x ≤ 0 := by
  have hg := rieszCoeff_nonneg' hd s hs0 hsd
  have hrc := rieszConst_pos hd s hs0 hsd
  have ha := summable_norm_coeffOf_of_nonneg hd s hs0 hsd hθ.ge hS
  set γ : Lattice d → ℝ := fun k => (coeffOf f k * coeffOf φ (-k)).re with hγ
  have hγs : Summable γ := by
    refine Summable.of_norm_bounded (ha.mul_right (∫ x, |φ x|)) fun k => ?_
    rw [Real.norm_eq_abs]; exact abs_re_mul_coeffOf_le _ _ k
  have h1 := integral_mul_toFun_laplaceRiesz s hφ hS
  have hmK : ∀ k : Lattice d, k ≠ 0 → mK d s k = rieszConst d s := by
    intro k hk
    rw [mK_eq_rpow s hk, hθ, zero_div, Real.rpow_zero, mul_one]
  have h2 : ∑' k, mK d s k * γ k = rieszConst d s * (∑' k, γ k - γ 0) := by
    have hsm : Summable fun k => mK d s k * γ k := by
      refine Summable.of_norm_bounded (hS.mul_right (∫ x, |φ x|)) fun k => ?_
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (mK_nonneg hg k), norm_laplaceRieszCoeff s hg,
        mul_assoc]
      exact mul_le_mul_of_nonneg_left (abs_re_mul_coeffOf_le _ _ k) (mK_nonneg hg k)
    rw [Torus.tsum_lattice _ hsm, mK_zero, zero_mul, zero_add, Torus.tsum_lattice _ hγs]
    rw [add_sub_cancel_left, ← tsum_mul_left]
    exact tsum_congr fun k => by rw [hmK k.1 k.2]
  have h3 : ∑' k, γ k = ∫ x, φ x * f x := by
    have := integral_mul_toFun (coeffOf f) ha hφ
    rw [toFun_coeffOf f hf ha, Complex.re_tsum (summable_mul_coeffOf ha φ)] at this
    exact this.symm
  have h4 : γ 0 = ∫ x, φ x := by
    simp only [hγ, neg_zero, coeffOf_zero_eq, hf1]
    rw [← Complex.ofReal_mul, Complex.ofReal_re]
    ring
  rw [h1, h2, h3, h4]
  have := integral_mul_ge_mul_integral hf hφ hmono
  rw [hf1] at this
  have h5 : ∫ x, φ x * f x = ∫ x, φ x * f x := rfl
  nlinarith

theorem mK_eq_rpow_all (s : ℝ) (hθ : 0 < s + 2 - (d : ℝ)) (k : Lattice d) :
    mK d s k = rieszConst d s * lamK k ^ ((s + 2 - (d : ℝ)) / 2) := by
  by_cases hk : k = 0
  · subst hk
    rw [mK_zero, lamK_zero, Real.zero_rpow (by linarith)]; simp
  · exact mK_eq_rpow s hk

/-- Heat-kernel positivity: `0 ≤ ∑_k (1 - e^{-λ_k t}) Re(f̂_k φ̂(-k))`. -/
theorem sum_one_sub_heat_nonneg (hd : 1 ≤ d) {f φ : Torus d → ℝ} (hf : Continuous f)
    (hφ : Continuous φ) (hmono : ∀ x y, 0 ≤ (φ x - φ y) * (f x - f y))
    (ha : Summable fun k => ‖coeffOf f k‖) (hf0 : ∀ x, 0 ≤ f x) (hf1 : ∫ x, f x = 1)
    {t : ℝ} (ht : 0 < t) :
    0 ≤ ∑' k, (1 - heatMult t k) * (coeffOf f k * coeffOf φ (-k)).re := by
  set c' : Coeff d := fun k => ((1 - heatMult t k : ℝ) : ℂ) * coeffOf f k with hc'
  have hc : Continuous (convFun (heatKer t) f) :=
    MFAux.continuous_convFun (integrable_heatKer ht) hf
  have hs' : Summable fun k => ‖c' k‖ := by
    refine Summable.of_nonneg_of_le (fun k => norm_nonneg _) (fun k => ?_) ha
    rw [hc', norm_mul, Complex.norm_real, Real.norm_eq_abs,
      abs_of_nonneg (sub_nonneg.mpr (heatMult_le_one ht.le k))]
    have := heatMult_pos t k
    exact mul_le_of_le_one_left (norm_nonneg _) (by linarith)
  have hcoef : coeffOf (fun x => f x - convFun (heatKer t) f x) = c' := by
    funext k
    rw [coeffOf_sub f _ hf hc, coeffOf_convFun_heatKer ht hf, hc']
    push_cast; ring
  have hg : toFun c' = fun x => f x - convFun (heatKer t) f x := by
    rw [← hcoef]
    exact toFun_coeffOf _ (hf.sub hc) (by rw [hcoef]; exact hs')
  have h1 := integral_mul_toFun c' hs' hφ
  rw [hg, Complex.re_tsum (summable_mul_coeffOf hs' φ)] at h1
  have h2 : 0 ≤ ∫ x, φ x * (f x - convFun (heatKer t) f x) :=
    integral_mul_sub_conv_nonneg (heatKer_continuous ht) (heatKer_nonneg hd ht)
      (fun x => by rw [heatKer_neg]) (integral_heatKer ht) hf hφ hmono
  rw [h1] at h2
  refine h2.trans (le_of_eq (tsum_congr fun k => ?_))
  rw [hc', mul_assoc, Complex.re_ofReal_mul]

/-- The regime `θ > 0`. -/
theorem laplaceRiesz_pairing_bound_pos (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (hθ : 0 < s + 2 - (d : ℝ)) {f φ : Torus d → ℝ} (hf : Continuous f) (hf0 : ∀ x, 0 ≤ f x)
    (hf1 : ∫ x, f x = 1) (hφ : Continuous φ) (hmono : ∀ x y, 0 ≤ (φ x - φ y) * (f x - f y))
    (hS : Summable fun k => ‖laplaceRieszCoeff d s (coeffOf f) k‖) :
    ∫ x, φ x * toFun (laplaceRieszCoeff d s (coeffOf f)) x ≤ 0 := by
  have hθ2 : s + 2 - (d : ℝ) < 2 := by linarith
  obtain ⟨Cθ, hC, hsub⟩ := rpow_eq_integral_one_sub_exp (s + 2 - (d : ℝ)) hθ hθ2
  have hg := rieszCoeff_nonneg' hd s hs0 hsd
  have hrc := rieszConst_pos hd s hs0 hsd
  have ha := summable_norm_coeffOf_of_nonneg hd s hs0 hsd hθ.le hS
  rw [integral_mul_toFun_laplaceRiesz s hφ hS, neg_nonpos]
  set w : ℝ → ℝ := fun t => (rieszConst d s / Cθ) * t ^ (-1 - (s + 2 - (d : ℝ)) / 2) with hw
  have hswap := tsum_mul_eq_integral (fun (k : Lattice d) t => 1 - heatMult t k) w
    (fun k => (coeffOf f k * coeffOf φ (-k)).re) (fun k => mK d s k)
    (fun k => by
      refine IntegrableOn.congr_fun ((integrableOn_one_sub_exp_scaled _ hθ hθ2
        (lamK_nonneg k)).const_mul (rieszConst d s / Cθ)) (fun t ht => ?_) measurableSet_Ioi
      simp only [hw, heatMult_eq_exp]
      ring)
    (fun k t ht => by
      simp only [hw]
      have h1 : 0 ≤ 1 - heatMult t k := sub_nonneg.mpr (heatMult_le_one ht.le k)
      have := Real.rpow_nonneg ht.le (-1 - (s + 2 - (d : ℝ)) / 2)
      positivity)
    (fun k => by
      rw [mK_eq_rpow_all s hθ k, hsub (lamK k) (lamK_nonneg k)]
      simp only [hw, heatMult_eq_exp]
      have : ∀ t : ℝ, (1 - Real.exp (-lamK k * t)) * (rieszConst d s / Cθ *
          t ^ (-1 - (s + 2 - (d : ℝ)) / 2)) = rieszConst d s / Cθ *
          ((1 - Real.exp (-lamK k * t)) * t ^ (-1 - (s + 2 - (d : ℝ)) / 2)) := fun t => by ring
      simp_rw [this]
      rw [integral_const_mul]
      field_simp)
    (summable_mK_mul_abs s hg (coeffOf f) φ hS)
  rw [hswap]
  refine setIntegral_nonneg measurableSet_Ioi fun t ht => ?_
  have e : ∀ k : Lattice d, (1 - heatMult t k) * w t * (coeffOf f k * coeffOf φ (-k)).re =
      w t * ((1 - heatMult t k) * (coeffOf f k * coeffOf φ (-k)).re) := fun k => by ring
  simp_rw [e]
  rw [tsum_mul_left]
  have hwn : 0 ≤ w t := by
    simp only [hw]
    have := Real.rpow_nonneg (le_of_lt (show (0 : ℝ) < t from ht)) (-1 - (s + 2 - (d : ℝ)) / 2)
    positivity
  exact mul_nonneg hwn (sum_one_sub_heat_nonneg hd hf hφ hmono ha hf0 hf1 ht)

/-- The three regimes at once: `∫ φ Δ(g⋆f) ≤ A ∫ φ` for `f ≥ 0` of mass one and `φ ≥ 0`
monotonically coupled to `f`; `A = 0` when `θ = s + 2 - d ≥ 0`. -/
theorem exists_laplaceRiesz_pairing_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ A : ℝ, 0 ≤ A ∧ ((d : ℝ) - 2 ≤ s → A = 0) ∧
      ∀ f φ : Torus d → ℝ, Continuous f → MemHs 2 (coeffOf f) → (∀ x, 0 ≤ f x) →
        (∫ x, f x) = 1 → Continuous φ → (∀ x, 0 ≤ φ x) →
        (∀ x y, 0 ≤ (φ x - φ y) * (f x - f y)) →
        ∫ x, φ x * toFun (laplaceRieszCoeff d s (coeffOf f)) x ≤ A * ∫ x, φ x := by
  by_cases hs : (d : ℝ) - 2 ≤ s
  · refine ⟨0, le_rfl, fun _ => rfl, fun f φ hf _ hf0 hf1 hφ hφ0 hmono => ?_⟩
    rw [zero_mul]
    by_cases hS : Summable fun k => ‖laplaceRieszCoeff d s (coeffOf f) k‖
    · rcases (show 0 ≤ s + 2 - (d : ℝ) by linarith).eq_or_lt with h0 | hpos
      · exact laplaceRiesz_pairing_bound_zero hd s hs0 hsd h0.symm hf hf1 hφ hmono hS
      · exact laplaceRiesz_pairing_bound_pos hd s hs0 hsd hpos hf hf0 hf1 hφ hmono hS
    · simp_rw [toFun_eq_zero_of_not_summable _ hS, mul_zero, integral_zero]
      exact le_rfl
  · obtain ⟨A, hA0, hA⟩ := laplaceRiesz_pairing_bound_neg hd s hs0 hsd (by linarith)
    exact ⟨A, hA0, fun h => absurd h hs, fun f φ hf hH hf0 hf1 hφ hφ0 _ =>
      hA f φ hf hH hf0 hf1 hφ hφ0⟩

end HRS.PDE.MFApriori
