import HRS.MS.ToriConvAux4

/-!
# MS-TORI-DRIFTCONV, helper file 5: the coefficient side

* `tcv_cube_tail`, `tcv_euc_tail`: tails (`|z| > R`) of the `L¹` norms of `D^j μ_L(x - ·)` on the cube and of
  `D^j ρ(x - ·)` on `ℝ^d`, from the decay `⟨w⟩^{-(d+3)}`.
* `tcv_Z_close`: `|Z_L - 1| ≤ B ε`; `tcv_mu_near`: `D^n μ_L = c D^n ρ` on `|y| < L/4`.
* `tcv_lvl_mu`: the level hypothesis `tcv_Lvl j (μ_L) (ρ^t)` for `j ≤ m + 1`.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.ToriConv

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.ToriCoefA HRS.MS.ToriCoefB

variable {d : ℕ}

theorem tcv_norm_ge_of_sub (x z : Euc d) : ‖z‖ - ‖x‖ ≤ ‖x - z‖ := by
  have := norm_sub_le x (x - z)
  rw [sub_sub_cancel] at this
  linarith

theorem tcv_cube_tail {L : ℝ} (hL : 0 < L) (f : Euc d → ℝ)
    (hv : ∀ y : Euc d, L / 3 ≤ ‖y‖ → f y = 0) (j : ℕ) (B : ℝ)
    (hB : ∀ w : Euc d, ‖iteratedFDeriv ℝ j f w‖ ≤ B * tca_g w) (x : Euc d) (R : ℝ)
    (hR : R ≤ L / 2) :
    ∫ z in tcb_Q d L ∩ {z : Euc d | R < ‖z‖}, ‖iteratedFDeriv ℝ j (perL L f) (x - z)‖ ≤
      2 ^ d * B * ∫ u in {u : Euc d | R - ‖x‖ ≤ ‖u‖}, tca_g u := by
  classical
  have hB0 : 0 ≤ B := by
    have h := (norm_nonneg _).trans (hB 0)
    exact nonneg_of_mul_nonneg_left h (tcb_g_pos 0)
  set K : Finset (Fin d → ℤ) :=
    Fintype.piFinset (fun i => ({⌊x i / L⌋, ⌊x i / L⌋ + 1} : Finset ℤ)) with hK
  have hKcard : K.card = 2 ^ d := by
    rw [hK, Fintype.card_piFinset]
    have : ∀ i : Fin d, (({⌊x i / L⌋, ⌊x i / L⌋ + 1} : Finset ℤ)).card = 2 := fun i =>
      Finset.card_pair (by omega)
    simp [this]
  set A : Set (Euc d) := {u : Euc d | R - ‖x‖ ≤ ‖u‖} with hA
  have hmA : MeasurableSet A := measurableSet_le measurable_const measurable_norm
  have hpt : ∀ z ∈ tcb_Q d L, ‖iteratedFDeriv ℝ j (perL L f) (x - z)‖ ≤
      ∑ k ∈ K, B * tca_g (x - z - L • latticePt k) := by
    intro z hz
    set y : Euc d := x - z with hy
    set k₀ : Fin d → ℤ := fun i => ⌊y i / L + 1 / 2⌋ with hk₀def
    have hk₀ : k₀ ∈ K := by
      rw [hK, Fintype.mem_piFinset]
      intro i
      simp only [Finset.mem_insert, Finset.mem_singleton]
      have hzi := hz i
      have hyi : y i = x i - z i := by simp [hy]
      have e1 : x i / L < y i / L + 1 / 2 := by
        rw [hyi, sub_div]
        have hz2 : z i / L < 1 / 2 := by
          rw [div_lt_iff₀ hL]
          have := hzi.2
          linarith
        linarith
      have e2 : y i / L + 1 / 2 ≤ x i / L + 1 := by
        rw [hyi, sub_div]
        have : -(z i / L) ≤ 1 / 2 := by
          rw [neg_le, ← neg_div, le_div_iff₀ hL]
          have := hzi.1
          linarith
        linarith
      have f1 : ⌊x i / L⌋ ≤ ⌊y i / L + 1 / 2⌋ := Int.floor_mono e1.le
      have f2 : ⌊y i / L + 1 / 2⌋ ≤ ⌊x i / L + 1⌋ := Int.floor_mono e2
      rw [Int.floor_add_one] at f2
      show ⌊y i / L + 1 / 2⌋ = ⌊x i / L⌋ ∨ ⌊y i / L + 1 / 2⌋ = ⌊x i / L⌋ + 1
      omega
    rw [tca_perL_iter_norm L hL f hv k₀ y (tcb_mem_U hL y) j]
    refine (hB _).trans ?_
    exact Finset.single_le_sum (f := fun k => B * tca_g (x - z - L • latticePt k))
      (fun k _ => mul_nonneg hB0 (tcb_g_pos _).le) hk₀
  -- the far region
  have hAmem : ∀ z ∈ tcb_Q d L ∩ {z : Euc d | R < ‖z‖}, ∀ k : Fin d → ℤ,
      x - z - L • latticePt k ∈ A := by
    intro z hz k
    obtain ⟨hzQ, hzR⟩ := hz
    have hzR' : R < ‖z‖ := hzR
    show R - ‖x‖ ≤ ‖x - z - L • latticePt k‖
    by_cases hk : k = 0
    · subst hk
      rw [tca_latticePt_zero, smul_zero, sub_zero]
      have := tcv_norm_ge_of_sub x z
      linarith
    · obtain ⟨i, hi⟩ : ∃ i, k i ≠ 0 := by
        by_contra h
        push_neg at h
        exact hk (funext h)
      have h1 : (1 : ℝ) ≤ |(k i : ℝ)| := by
        have : (1 : ℤ) ≤ |k i| := Int.one_le_abs hi
        have h2 : ((1 : ℤ) : ℝ) ≤ ((|k i| : ℤ) : ℝ) := by exact_mod_cast this
        simpa [Int.cast_abs] using h2
      have hxi : |x i| ≤ ‖x‖ := tcv_coord_le x i
      have hzi : |z i| ≤ L / 2 := by
        have := hzQ i
        rw [abs_le]
        constructor <;> linarith [this.1, this.2]
      have hcomp : (x - z - L • latticePt k) i = x i - z i - L * (k i : ℝ) := by
        simp [latticePt]
      have h3 : |(x - z - L • latticePt k) i| ≥ L * |(k i : ℝ)| - |x i| - |z i| := by
        rw [hcomp]
        have h4 := abs_sub (x i - z i) (x i - z i - L * (k i : ℝ))
        have e : (x i - z i) - (x i - z i - L * (k i : ℝ)) = L * (k i : ℝ) := by ring
        rw [e, abs_mul, abs_of_pos hL] at h4
        have h5 : |x i - z i| ≤ |x i| + |z i| := abs_sub _ _
        linarith
      have h6 : L * |(k i : ℝ)| ≥ L := by nlinarith
      have h7 := tcv_coord_le (x - z - L • latticePt k) i
      linarith
  have hint1 : ∀ k : Fin d → ℤ, Integrable (fun z : Euc d => B * A.indicator tca_g (x - z - L • latticePt k))
      volume := by
    intro k
    have e : (fun z : Euc d => B * A.indicator tca_g (x - z - L • latticePt k)) =
        fun z => B * A.indicator tca_g ((x - L • latticePt k) - z) := by
      funext z; rw [sub_right_comm]
    rw [e]
    exact ((tca_g_integrable.indicator hmA).comp_sub_left (x - L • latticePt k)).const_mul B
  have hint : Integrable (fun z : Euc d => ∑ k ∈ K, B * A.indicator tca_g (x - z - L • latticePt k))
      volume := integrable_finsetSum _ fun k _ => hint1 k
  have hnn : 0 ≤ᵐ[volume] fun z : Euc d => ∑ k ∈ K, B * A.indicator tca_g (x - z - L • latticePt k) :=
    Filter.Eventually.of_forall fun z => Finset.sum_nonneg fun k _ =>
      mul_nonneg hB0 (Set.indicator_nonneg (fun u _ => (tca_g_nonneg u)) _)
  have hmS : MeasurableSet (tcb_Q d L ∩ {z : Euc d | R < ‖z‖}) :=
    (tcb_measurableSet_Q L).inter (measurableSet_lt measurable_const measurable_norm)
  calc ∫ z in tcb_Q d L ∩ {z : Euc d | R < ‖z‖}, ‖iteratedFDeriv ℝ j (perL L f) (x - z)‖
      ≤ ∫ z in tcb_Q d L ∩ {z : Euc d | R < ‖z‖},
          ∑ k ∈ K, B * A.indicator tca_g (x - z - L • latticePt k) := by
        refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun z => norm_nonneg _)
          hint.integrableOn ?_
        filter_upwards [ae_restrict_mem hmS] with z hz
        refine (hpt z hz.1).trans (Finset.sum_le_sum fun k _ => le_of_eq ?_)
        rw [Set.indicator_of_mem (hAmem z hz k)]
    _ ≤ ∫ z, ∑ k ∈ K, B * A.indicator tca_g (x - z - L • latticePt k) :=
        setIntegral_le_integral hint hnn
    _ = ∑ k ∈ K, ∫ z, B * A.indicator tca_g (x - z - L • latticePt k) :=
        integral_finsetSum _ fun k _ => hint1 k
    _ = ∑ k ∈ K, B * ∫ u in A, tca_g u := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [integral_const_mul]
        congr 1
        have e : (fun z : Euc d => A.indicator tca_g (x - z - L • latticePt k)) =
            fun z => A.indicator tca_g ((x - L • latticePt k) - z) := by
          funext z; rw [sub_right_comm]
        rw [e, integral_sub_left_eq_self (fun w => A.indicator tca_g w) volume (x - L • latticePt k),
          integral_indicator hmA]
    _ = 2 ^ d * B * ∫ u in A, tca_g u := by
        rw [Finset.sum_const, hKcard, nsmul_eq_mul]
        push_cast
        ring

theorem tcv_euc_tail (G : Euc d → ℝ) (B : ℝ) (hB0 : 0 ≤ B) (hG : ∀ w, G w ≤ B * tca_g w)
    (hGnn : ∀ w, 0 ≤ G w) (hGc : Continuous G) (x : Euc d) (R : ℝ) :
    ∫ z in {z : Euc d | R < ‖z‖}, G (x - z) ≤ B * ∫ u in {u : Euc d | R - ‖x‖ ≤ ‖u‖}, tca_g u := by
  set A : Set (Euc d) := {u : Euc d | R - ‖x‖ ≤ ‖u‖} with hA
  have hmA : MeasurableSet A := measurableSet_le measurable_const measurable_norm
  have hmS : MeasurableSet {z : Euc d | R < ‖z‖} := measurableSet_lt measurable_const measurable_norm
  have hint1 : Integrable (fun z : Euc d => B * A.indicator tca_g (x - z)) volume :=
    ((tca_g_integrable.indicator hmA).comp_sub_left x).const_mul B
  have hint2 : Integrable (fun z : Euc d => G (x - z)) volume := by
    have h3 : Integrable (fun z : Euc d => B * tca_g (x - z)) volume :=
      (tca_g_integrable.comp_sub_left x).const_mul B
    refine Integrable.mono' h3 ((hGc.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (hGnn _)]
    exact hG _
  have hnn : 0 ≤ᵐ[volume] fun z : Euc d => B * A.indicator tca_g (x - z) :=
    Filter.Eventually.of_forall fun z =>
      mul_nonneg hB0 (Set.indicator_nonneg (fun u _ => (tca_g_nonneg u)) _)
  calc ∫ z in {z : Euc d | R < ‖z‖}, G (x - z)
      ≤ ∫ z in {z : Euc d | R < ‖z‖}, B * A.indicator tca_g (x - z) := by
        refine setIntegral_mono_on hint2.integrableOn hint1.integrableOn hmS fun z hz => ?_
        have hzR : R < ‖z‖ := hz
        have hmem : x - z ∈ A := by
          show R - ‖x‖ ≤ ‖x - z‖
          have := tcv_norm_ge_of_sub x z
          linarith
        rw [Set.indicator_of_mem hmem]
        exact hG _
    _ ≤ ∫ z, B * A.indicator tca_g (x - z) := setIntegral_le_integral hint1 hnn
    _ = B * ∫ u in A, tca_g u := by
        rw [integral_const_mul]
        congr 1
        rw [integral_sub_left_eq_self (fun w => A.indicator tca_g w) volume x, integral_indicator hmA]

end HRS.MS.ToriConv
