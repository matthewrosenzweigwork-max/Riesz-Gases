import HRS.Stochastic.Ito

/-!
# Moment bounds of Burkholder–Davis–Gundy type (`p = 2`, `p = 4`)

Package SI-01, part 6.  For `M = ∫ Φ · dW` in the `L²` class, with the pathwise supremum
`sup_{t ≤ T} |M_t|` (an `ℝ≥0∞`-valued `⨆`, never a junk value):

* `p = 2`: `E sup_{t ≤ T} |M_t|² ≤ 4 E ∫_0^T |Φ|²` (Doob + isometry; constant `4`).
* `p = 4`: `E sup_{t ≤ T} |M_t|⁴ ≤ (512/27)² E (∫_0^T |Φ|²)²`.  Route: Itô's formula for `x⁴`
  (after localisation at `τ_R = inf {t : |M_t| ≥ R or ∫_0^t |Φ|² ≥ R}`) gives
  `E M_T⁴ = 6 E ∫_0^T M_s² |Φ_s|² ds ≤ 6 (E sup M⁴)^{1/2} (E (∫|Φ|²)²)^{1/2}`; Doob's `L⁴`
  inequality `E sup M⁴ ≤ (4/3)⁴ E M_T⁴`; solving the resulting inequality
  `S ≤ (4/3)⁴ · 6 · S^{1/2} Q^{1/2}` gives `S ≤ ((4/3)⁴ · 6)² Q = (512/27)² Q`.
  The constant is explicit and not optimal.
* Increment versions (`∫_s^t`), used for Kolmogorov-type modulus estimates: S L10848, L10858
  ("Burkholder–Davis–Gundy gives its fourth moment bounded by `C|t-s|²`"), S L3825.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {ι : Type*} [Fintype ι]
variable {P : Measure Ω} {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ} {Φ : ℝ → Ω → ι → ℝ}

/-- The explicit `p = 4` constant `(512/27)²`. -/
def bdgConstFour : ℝ≥0∞ := ENNReal.ofReal ((512 / 27 : ℝ) ^ 2)

/-! ### Doob's `L⁴` inequality (generic) -/

theorem layer_bound_four {μ : Measure Ω} {Y f : Ω → ℝ} (hY : Measurable Y) (hf : Measurable f)
    (hY0 : 0 ≤ Y)
    (hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {ω | t ≤ Y ω} ≤
      ∫⁻ ω in {ω | t ≤ Y ω}, ENNReal.ofReal (f ω) ∂μ) :
    ∫⁻ ω, ENNReal.ofReal (Y ω ^ 4) ∂μ ≤
      ENNReal.ofReal (4 / 3) * ∫⁻ ω, ENNReal.ofReal (f ω) * ENNReal.ofReal (Y ω ^ 3) ∂μ := by
  have h1 := lintegral_rpow_eq_lintegral_meas_le_mul μ (Eventually.of_forall hY0)
    hY.aemeasurable (p := 4) (by norm_num)
  have e4 : ∀ x : ℝ, x ^ (4:ℝ) = x ^ 4 := fun x => by
    rw [show (4:ℝ) = ((4:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  have e3 : ∀ x : ℝ, x ^ ((4:ℝ) - 1) = x ^ 3 := fun x => by
    rw [show (4:ℝ) - 1 = ((3:ℕ):ℝ) by norm_num, Real.rpow_natCast]
  simp only [e4, e3] at h1
  rw [h1]
  -- weak-type bound
  set ν : Measure Ω := μ.withDensity (fun ω => ENNReal.ofReal (f ω)) with hν
  have h2 : ∫⁻ t in Set.Ioi (0:ℝ), μ {a | t ≤ Y a} * ENNReal.ofReal (t ^ 3) ≤
      ∫⁻ t in Set.Ioi (0:ℝ), ν {a | t ≤ Y a} * ENNReal.ofReal (t ^ 2) := by
    refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
    have ht' : (0:ℝ) < t := ht
    have hmeas : MeasurableSet {a | t ≤ Y a} := measurableSet_le measurable_const hY
    have := hweak t ht'
    calc μ {a | t ≤ Y a} * ENNReal.ofReal (t ^ 3)
        = (ENNReal.ofReal t * μ {a | t ≤ Y a}) * ENNReal.ofReal (t ^ 2) := by
          rw [show t ^ 3 = t * t ^ 2 by ring, ENNReal.ofReal_mul ht'.le]; ring
      _ ≤ ν {a | t ≤ Y a} * ENNReal.ofReal (t ^ 2) := by
          gcongr
          rw [hν, withDensity_apply _ hmeas]; exact this
  have h3 : ∫⁻ t in Set.Ioi (0:ℝ), ν {a | t ≤ Y a} * ENNReal.ofReal (t ^ 2) =
      ∫⁻ ω, ENNReal.ofReal (Y ω ^ 3 / 3) ∂ν := by
    have := lintegral_comp_eq_lintegral_meas_le_mul ν (Eventually.of_forall hY0)
      hY.aemeasurable (g := fun t : ℝ => t ^ 2)
      (fun t _ => (continuous_pow 2).intervalIntegrable _ _)
      (Filter.Eventually.of_forall fun t => sq_nonneg t)
    rw [← this]
    refine lintegral_congr fun ω => ?_
    simp [integral_pow]
    norm_num
  rw [h3] at h2
  have h4 : ∫⁻ ω, ENNReal.ofReal (Y ω ^ 3 / 3) ∂ν =
      ENNReal.ofReal (1 / 3) * ∫⁻ ω, ENNReal.ofReal (f ω) * ENNReal.ofReal (Y ω ^ 3) ∂μ := by
    rw [hν, lintegral_withDensity_eq_lintegral_mul _ hf.ennreal_ofReal
      ((hY.pow_const 3).div_const 3).ennreal_ofReal]
    rw [← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
    refine lintegral_congr fun ω => ?_
    simp only [Pi.mul_apply]
    rw [show Y ω ^ 3 / 3 = (1/3) * Y ω ^ 3 by ring, ENNReal.ofReal_mul (by norm_num)]
    ring
  calc ENNReal.ofReal 4 * ∫⁻ t in Set.Ioi (0:ℝ), μ {a | t ≤ Y a} * ENNReal.ofReal (t ^ 3)
      ≤ ENNReal.ofReal 4 * (ENNReal.ofReal (1 / 3) *
        ∫⁻ ω, ENNReal.ofReal (f ω) * ENNReal.ofReal (Y ω ^ 3) ∂μ) := by
        gcongr
        exact h2.trans h4.le
    _ = _ := by
        rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num)]; norm_num

theorem amgm_four (a b : ℝ) :
    a * b ^ 3 ≤ 16 / 27 * a ^ 4 + 9 / 16 * b ^ 4 := by
  nlinarith [mul_nonneg (sq_nonneg (a - 3 / 4 * b)) (add_nonneg (sq_nonneg (a + 3 / 4 * b)) (sq_nonneg b))]

open Finset in
theorem doob_four_discrete {μ : Measure Ω} [IsProbabilityMeasure μ] {𝒢 : Filtration ℕ mΩ}
    {f : ℕ → Ω → ℝ} (hsub : Submartingale f 𝒢 μ) (hnn : 0 ≤ f) (N : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (((range (N + 1)).sup' nonempty_range_add_one fun k => f k ω) ^ 4) ∂μ ≤
      ENNReal.ofReal ((4 / 3 : ℝ) ^ 4) * ∫⁻ ω, ENNReal.ofReal (f N ω ^ 4) ∂μ := by
  set X : Ω → ℝ := fun ω => (range (N + 1)).sup' nonempty_range_add_one fun k => f k ω with hX
  have hfm : ∀ k, Measurable (f k) := fun k => (hsub.stronglyMeasurable k).measurable.le (𝒢.le k)
  have hXm : Measurable X := measurable_range_sup'' fun n _ => hfm n
  have hX0 : 0 ≤ X := fun ω => le_trans (hnn 0 ω) (le_sup' (fun k => f k ω) (by simp))
  set A := ∫⁻ ω, ENNReal.ofReal (f N ω ^ 4) ∂μ with hA
  by_cases hAtop : A = ∞
  · rw [hAtop, ENNReal.mul_top (by simp)]; exact le_top
  have key : ∀ c : ℕ, ∫⁻ ω, ENNReal.ofReal (min (X ω) c ^ 4) ∂μ ≤
      ENNReal.ofReal ((4 / 3 : ℝ) ^ 4) * A := by
    intro c
    set Y : Ω → ℝ := fun ω => min (X ω) c with hY
    have hYm : Measurable Y := hXm.min measurable_const
    have hY0 : 0 ≤ Y := fun ω => le_min (hX0 ω) (Nat.cast_nonneg c)
    have hYc : ∀ ω, Y ω ≤ c := fun ω => min_le_right _ _
    have hweak : ∀ t : ℝ, 0 < t → ENNReal.ofReal t * μ {ω | t ≤ Y ω} ≤
        ∫⁻ ω in {ω | t ≤ Y ω}, ENNReal.ofReal (f N ω) ∂μ := by
      intro t ht
      by_cases htc : t ≤ c
      · have hset : {ω | t ≤ Y ω} = {ω | t ≤ X ω} := by
          ext ω; simp [hY, htc]
        rw [hset]
        have := maximal_ineq hsub hnn (ε := t.toNNReal) N
        have hcoe : ((t.toNNReal : ℝ≥0) : ℝ) = t := Real.coe_toNNReal t ht.le
        simp only [hcoe] at this
        rw [show ENNReal.ofReal t = ((t.toNNReal : ℝ≥0) : ℝ≥0∞) from rfl]
        refine this.trans (le_of_eq ?_)
        rw [ofReal_integral_eq_lintegral_ofReal]
        · exact (hsub.integrable N).integrableOn
        · exact Eventually.of_forall (hnn N)
      · push Not at htc
        have : {ω | t ≤ Y ω} = ∅ := by
          ext ω; simp only [Set.mem_ofPred_eq, Set.mem_empty_iff_false, iff_false, not_le]
          exact lt_of_le_of_lt (hYc ω) htc
        rw [this]; simp
    have h1 := layer_bound_four (μ := μ) hYm (hfm N) hY0 hweak
    have h2 : ∫⁻ ω, ENNReal.ofReal (f N ω) * ENNReal.ofReal (Y ω ^ 3) ∂μ ≤
        ENNReal.ofReal (16 / 27) * A + ENNReal.ofReal (9 / 16) * ∫⁻ ω, ENNReal.ofReal (Y ω ^ 4) ∂μ := by
      rw [hA, ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_const_mul' _ _ ENNReal.ofReal_ne_top,
        ← lintegral_add_left (((hfm N).pow_const 4).ennreal_ofReal.const_mul (ENNReal.ofReal (16 / 27)))]
      refine lintegral_mono fun ω => ?_
      have e1 : (0:ℝ) ≤ 16 / 27 * f N ω ^ 4 := by positivity
      have e2 : (0:ℝ) ≤ 9 / 16 * Y ω ^ 4 := by positivity
      rw [← ENNReal.ofReal_mul (hnn N ω), ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 16 / 27),
        ← ENNReal.ofReal_mul (by norm_num : (0:ℝ) ≤ 9 / 16), ← ENNReal.ofReal_add e1 e2]
      exact ENNReal.ofReal_le_ofReal (amgm_four _ _)
    set B := ∫⁻ ω, ENNReal.ofReal (Y ω ^ 4) ∂μ with hB
    have hBtop : B ≠ ∞ := by
      have : B ≤ ∫⁻ _ω, ENNReal.ofReal ((c : ℝ) ^ 4) ∂μ :=
        lintegral_mono fun ω => ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (hY0 ω) (hYc ω) 4)
      exact ne_top_of_le_ne_top (by simp) this
    have h3 : B ≤ ENNReal.ofReal (64 / 81) * A + ENNReal.ofReal (3 / 4) * B := by
      calc B ≤ ENNReal.ofReal (4 / 3) * (ENNReal.ofReal (16 / 27) * A + ENNReal.ofReal (9 / 16) * B) :=
            h1.trans (by gcongr)
        _ = _ := by
          rw [mul_add, ← mul_assoc, ← mul_assoc, ← ENNReal.ofReal_mul (by norm_num),
            ← ENNReal.ofReal_mul (by norm_num)]
          norm_num
    have h4 : B.toReal ≤ 64 / 81 * A.toReal + 3 / 4 * B.toReal := by
      have := ENNReal.toReal_mono (by finiteness) h3
      rwa [ENNReal.toReal_add (by finiteness) (by finiteness), ENNReal.toReal_mul,
        ENNReal.toReal_mul, ENNReal.toReal_ofReal (by norm_num),
        ENNReal.toReal_ofReal (by norm_num)] at this
    have h5 : B.toReal ≤ (4 / 3) ^ 4 * A.toReal := by nlinarith
    rw [← ENNReal.ofReal_toReal hBtop]
    calc ENNReal.ofReal B.toReal ≤ ENNReal.ofReal ((4 / 3 : ℝ) ^ 4 * A.toReal) :=
          ENNReal.ofReal_le_ofReal h5
      _ = _ := by rw [ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_toReal hAtop]
  have hmono : Monotone fun (c : ℕ) ω => ENNReal.ofReal (min (X ω) c ^ 4) := by
    intro c d hcd ω
    refine ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (le_min (hX0 ω) (Nat.cast_nonneg c)) ?_ 4)
    exact min_le_min le_rfl (by exact_mod_cast hcd)
  have hsup : ∀ ω, ENNReal.ofReal (X ω ^ 4) = ⨆ c : ℕ, ENNReal.ofReal (min (X ω) c ^ 4) := by
    intro ω
    refine le_antisymm ?_ (iSup_le fun c => ENNReal.ofReal_le_ofReal
      (pow_le_pow_left₀ (le_min (hX0 ω) (Nat.cast_nonneg c)) (min_le_left _ _) 4))
    obtain ⟨c, hc⟩ := exists_nat_ge (X ω)
    exact le_iSup_of_le c (by rw [min_eq_left hc])
  calc ∫⁻ ω, ENNReal.ofReal (X ω ^ 4) ∂μ
      = ∫⁻ ω, ⨆ c : ℕ, ENNReal.ofReal (min (X ω) c ^ 4) ∂μ := lintegral_congr hsup
    _ = ⨆ c : ℕ, ∫⁻ ω, ENNReal.ofReal (min (X ω) c ^ 4) ∂μ := by
        refine lintegral_iSup (fun c => ?_) hmono
        exact ((hXm.min measurable_const).pow_const 4).ennreal_ofReal
    _ ≤ _ := iSup_le key

theorem exists_dyadic_grid {T t : ℝ} (hpos : 0 < T) (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∃ k : ℕ → ℕ, (∀ n, k n ≤ 2 ^ n) ∧ (∀ n, T * (k n : ℝ) / 2 ^ n ≤ t) ∧
      Tendsto (fun n => T * (k n : ℝ) / 2 ^ n) atTop (𝓝 t) := by
  have h2 : ∀ n : ℕ, (0 : ℝ) < 2 ^ n := fun n => by positivity
  have hr : ∀ n : ℕ, 0 ≤ t * 2 ^ n / T := fun n => by have := ht.1; positivity
  refine ⟨fun n => ⌊t * 2 ^ n / T⌋₊, fun n => ?_, fun n => ?_, ?_⟩
  · refine Nat.floor_le_of_le ?_
    push_cast
    rw [div_le_iff₀ hpos]
    nlinarith [ht.2, h2 n]
  · have := Nat.floor_le (hr n)
    rw [le_div_iff₀ hpos] at this
    rw [div_le_iff₀ (h2 n)]
    nlinarith [this]
  · have hlt : ∀ n : ℕ, t - T / 2 ^ n < T * (⌊t * 2 ^ n / T⌋₊ : ℝ) / 2 ^ n := fun n => by
      have := Nat.lt_floor_add_one (t * 2 ^ n / T)
      rw [div_lt_iff₀ hpos] at this
      rw [lt_div_iff₀ (h2 n)]
      have e : (t - T / 2 ^ n) * 2 ^ n = t * 2 ^ n - T := by field_simp
      rw [e]
      nlinarith [this]
    have hup : ∀ n : ℕ, T * (⌊t * 2 ^ n / T⌋₊ : ℝ) / 2 ^ n ≤ t := fun n => by
      have := Nat.floor_le (hr n)
      rw [le_div_iff₀ hpos] at this
      rw [div_le_iff₀ (h2 n)]
      nlinarith [this]
    have hT0 : Tendsto (fun n : ℕ => T / 2 ^ n) atTop (𝓝 0) := by
      simpa [div_eq_mul_inv] using
        (tendsto_const_nhds (x := T)).mul (tendsto_pow_atTop_nhds_zero_of_lt_one
          (by norm_num : (0:ℝ) ≤ 1/2) (by norm_num : (1:ℝ)/2 < 1) |>.congr fun n => by simp)
    have hlow : Tendsto (fun n : ℕ => t - T / 2 ^ n) atTop (𝓝 t) := by
      simpa using (tendsto_const_nhds (x := t)).sub hT0
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le hlow tendsto_const_nhds
      (fun n => (hlt n).le) hup

/-- Doob's `L⁴` maximal inequality for a continuous martingale. -/
theorem doob_four_cont {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℝ mΩ}
    {M : ℝ → Ω → ℝ} (hM : Martingale M ℱ μ) (hc : ∀ ω, Continuous fun t => M t ω)
    {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ 4 ∂μ ≤
      ENNReal.ofReal ((4 / 3 : ℝ) ^ 4) * ∫⁻ ω, ‖M T ω‖ₑ ^ 4 ∂μ := by
  -- the dyadic grids
  let τ : ℕ → ℕ → ℝ := fun n k => T * k / 2 ^ n
  have hτmono : ∀ n, Monotone (τ n) := fun n i j hij => by
    simp only [τ]; gcongr
  let 𝒢 : ℕ → Filtration ℕ mΩ := fun n =>
    ⟨fun k => ℱ (τ n k), fun i j hij => ℱ.mono (hτmono n hij), fun k => ℱ.le _⟩
  let F : ℕ → ℕ → Ω → ℝ := fun n k ω => ‖M (τ n k) ω‖
  have hsub : ∀ n, Submartingale (F n) (𝒢 n) μ := by
    intro n
    refine ⟨fun k => ((hM.stronglyMeasurable _).norm : _), fun i j hij => ?_, fun k => (hM.integrable _).norm⟩
    have h1 := norm_condExp_le (μ := μ) (m := ℱ (τ n i)) (M (τ n j))
    have h2 := hM.condExp_ae_eq (hτmono n hij)
    filter_upwards [h1, h2] with ω hω1 hω2
    simp only [F]
    rw [← hω2]
    exact hω1
  have hnn : ∀ n, 0 ≤ F n := fun n k ω => norm_nonneg _
  have hdoob := fun n => doob_four_discrete (hsub n) (hnn n) (2 ^ n)
  let g : ℕ → Ω → ℝ≥0∞ := fun n ω => ENNReal.ofReal
    (((Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one fun k => F n k ω) ^ 4)
  have hFm : ∀ n k, Measurable (F n k) := fun n k =>
    ((hM.stronglyMeasurable (τ n k)).measurable.le (ℱ.le _)).norm
  have hgm : ∀ n, Measurable (g n) := fun n =>
    ((Finset.measurable_range_sup'' fun k _ => hFm n k).pow_const 4).ennreal_ofReal
  have hgle : ∀ n, ∫⁻ ω, g n ω ∂μ ≤ ENNReal.ofReal ((4 / 3 : ℝ) ^ 4) * ∫⁻ ω, ‖M T ω‖ₑ ^ 4 ∂μ := by
    intro n
    refine (hdoob n).trans (le_of_eq ?_)
    congr 1
    refine lintegral_congr fun ω => ?_
    have : τ n (2 ^ n) = T := by simp only [τ]; push_cast; field_simp
    simp only [F, this]
    rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
  -- pointwise bound
  have hpt : ∀ ω, ∀ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ ^ 4 ≤ liminf (fun n => g n ω) atTop := by
    intro ω t ht
    -- approximating grid points
    obtain ⟨k, hk0, hkle, hkT⟩ : ∃ k : ℕ → ℕ, (∀ n, k n ≤ 2 ^ n) ∧ (∀ n, τ n (k n) ≤ t) ∧
        Tendsto (fun n => τ n (k n)) atTop (𝓝 t) := by
      rcases hT.eq_or_lt with h0 | hpos
      · subst h0
        have ht0 : t = 0 := le_antisymm ht.2 ht.1
        subst ht0
        refine ⟨fun _ => 0, fun n => Nat.zero_le _, fun n => by simp [τ], ?_⟩
        simp [τ]
      · exact exists_dyadic_grid hpos ht
    have hk : Tendsto (fun n => ‖M (τ n (k n)) ω‖ₑ ^ 4) atTop (𝓝 (‖M t ω‖ₑ ^ 4)) :=
      ((ENNReal.continuous_pow 4).tendsto _).comp
        ((continuous_enorm.tendsto _).comp ((hc ω).tendsto t |>.comp hkT))
    rw [← hk.liminf_eq]
    refine liminf_le_liminf (Eventually.of_forall fun n => ?_)
    simp only [g]
    have hle : ‖M (τ n (k n)) ω‖ ≤ (Finset.range (2 ^ n + 1)).sup' Finset.nonempty_range_add_one
        fun j => F n j ω :=
      Finset.le_sup' (fun j => F n j ω) (Finset.mem_range.2 (Nat.lt_succ_of_le (hk0 n)))
    calc ‖M (τ n (k n)) ω‖ₑ ^ 4 = ENNReal.ofReal (‖M (τ n (k n)) ω‖ ^ 4) := by
          rw [ENNReal.ofReal_pow (norm_nonneg _), ofReal_norm]
      _ ≤ _ := ENNReal.ofReal_le_ofReal (pow_le_pow_left₀ (norm_nonneg _) hle 4)
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) ^ 4 ∂μ
      ≤ ∫⁻ ω, liminf (fun n => g n ω) atTop ∂μ := by
        refine lintegral_mono fun ω => ?_
        rw [ENNReal.iSup_pow_of_ne_zero (by norm_num)]
        refine iSup_le fun t => ?_
        rw [ENNReal.iSup_pow_of_ne_zero (by norm_num)]
        exact iSup_le fun ht => hpt ω t ht
    _ ≤ liminf (fun n => ∫⁻ ω, g n ω ∂μ) atTop := lintegral_liminf_le hgm
    _ ≤ _ := by
        refine (liminf_le_limsup).trans (limsup_le_of_le (by isBoundedDefault) ?_)
        exact Eventually.of_forall hgle

/-! ### Auxiliary lemmas for the fourth-moment bound -/


/-- A progressive process, frozen at time `T`, is jointly measurable. -/
theorem isProgressive_measurable_uncurry_min {β : Type*} [MeasurableSpace β] {ℱ : Filtration ℝ mΩ}
    {u : ℝ → Ω → β} (hu : IsProgressive ℱ u) (T : ℝ) :
    Measurable fun p : ℝ × Ω => u (min p.1 T) p.2 := by
  let mm : MeasurableSpace (ℝ × Ω) := (inferInstance : MeasurableSpace ℝ).prod (ℱ T)
  have hfst : @Measurable (ℝ × Ω) ℝ mm _ Prod.fst := @measurable_fst ℝ Ω _ (ℱ T)
  have hsnd : @Measurable (ℝ × Ω) Ω mm (ℱ T) Prod.snd := @measurable_snd ℝ Ω _ (ℱ T)
  have h1 : @Measurable (ℝ × Ω) (Set.Iic T × Ω) mm
      (Subtype.instMeasurableSpace.prod (ℱ T))
      (fun p : ℝ × Ω => ((⟨min p.1 T, Set.mem_Iic.2 (min_le_right _ _)⟩ : Set.Iic T), p.2)) := by
    refine Measurable.prodMk (m := mm) ?_ hsnd
    exact (hfst.min measurable_const).subtype_mk
  have h2 := (hu T).comp h1
  refine h2.mono ?_ le_rfl
  exact sup_le_sup le_rfl (MeasurableSpace.comap_mono (ℱ.le T))

theorem measurable_lintegral_Icc {G : ℝ × Ω → ℝ≥0∞} (hG : Measurable G) (T : ℝ) :
    Measurable fun ω => ∫⁻ s in Set.Icc 0 T, G (s, ω) := by
  have : Measurable fun p : Ω × ℝ => G (p.2, p.1) := hG.comp measurable_swap
  exact this.lintegral_prod_right' (ν := volume.restrict (Set.Icc 0 T))

theorem measurable_lintegral_prog {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ mΩ}
    {Ψ : ℝ → Ω → ι → ℝ} (hΨ : IsProgressive ℱ Ψ) {N : ℝ → Ω → ℝ}
    (hNc : ∀ ω, Continuous fun t => N t ω) (hNm : ∀ t, Measurable (N t)) (T : ℝ) :
    Measurable fun ω => ∫⁻ s in Set.Icc 0 T, ‖N s ω‖ₑ ^ 2 * ∑ k, ‖Ψ s ω k‖ₑ ^ 2 := by
  have hN : Measurable (Function.uncurry N) := measurable_uncurry_of_continuous_of_measurable hNc hNm
  have hΨm := isProgressive_measurable_uncurry_min hΨ T
  have hG : Measurable fun p : ℝ × Ω => ‖N p.1 p.2‖ₑ ^ 2 * ∑ k, ‖Ψ (min p.1 T) p.2 k‖ₑ ^ 2 := by
    refine Measurable.mul ((hN.enorm).pow_const 2) ?_
    exact Finset.measurable_sum _ fun k _ => (((measurable_pi_apply k).comp hΨm).enorm).pow_const 2
  have := measurable_lintegral_Icc hG T
  convert this using 2 with ω
  refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
  simp only [min_eq_left hs.2]


theorem measurable_iSup_enorm_Icc {M : ℝ → Ω → ℝ} (hmeas : ∀ t, Measurable (M t))
    (hc : ∀ ω, Continuous fun t => M t ω) {T : ℝ} (hT : 0 ≤ T) :
    Measurable fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ := by
  rcases hT.eq_or_lt with h0 | hpos
  · subst h0
    have : (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) 0, ‖M t ω‖ₑ) = fun ω => ‖M 0 ω‖ₑ := by
      funext ω; simp
    rw [this]; exact (hmeas 0).enorm
  · have key : (fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ) =
        fun ω => ⨆ n : ℕ, ⨆ k : ℕ, ⨆ (_ : k ≤ 2 ^ n), ‖M (T * k / 2 ^ n) ω‖ₑ := by
      funext ω
      refine le_antisymm (iSup₂_le fun t ht => ?_) (iSup_le fun n => iSup_le fun k => iSup_le fun hk => ?_)
      · obtain ⟨k, hk0, hkle, hkT⟩ := exists_dyadic_grid hpos ht
        refine le_of_tendsto' ((continuous_enorm.tendsto _).comp ((hc ω).tendsto t |>.comp hkT)) fun n => ?_
        exact le_iSup_of_le n (le_iSup_of_le (k n) (le_iSup_of_le (hk0 n) le_rfl))
      · refine le_iSup₂_of_le (T * k / 2 ^ n) ⟨by positivity, ?_⟩ le_rfl
        rw [div_le_iff₀ (by positivity)]
        have : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk
        nlinarith
    rw [key]
    refine Measurable.iSup fun n => Measurable.iSup fun k => Measurable.iSup_Prop _ ?_
    exact (hmeas _).enorm



theorem enorm_sq_eq (x : ℝ) : ‖x‖ₑ ^ 2 = ENNReal.ofReal (x ^ 2) := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg x), sq_abs]

theorem ofReal_six_mul_sq_sum (a : ℝ) (b : ι → ℝ) :
    ENNReal.ofReal (6 * a ^ 2 * ∑ k, b k ^ 2) = 6 * (‖a‖ₑ ^ 2 * ∑ k, ‖b k‖ₑ ^ 2) := by
  rw [mul_assoc, ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (sq_nonneg a),
    ENNReal.ofReal_sum_of_nonneg (fun k _ => sq_nonneg _), enorm_sq_eq]
  simp only [enorm_sq_eq]
  norm_num

theorem IsProgressiveL2.of_ae_le [IsProbabilityMeasure P] {Ψ I : ℝ → Ω → ι → ℝ}
    (hΨ : IsProgressiveL2 P ℱ Ψ) (hI : IsProgressive ℱ I) {C : ℝ≥0∞} (hC : C ≠ ∞)
    (hle : ∀ᵐ ω ∂P, ∀ s k, ‖I s ω k‖ₑ ≤ C * ‖Ψ s ω k‖ₑ) : IsProgressiveL2 P ℱ I := by
  refine ⟨hI, fun T => ?_⟩
  have : sqIntegralOn P I T ≤ C ^ 2 * sqIntegralOn P Ψ T := by
    unfold sqIntegralOn
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top hC)]
    refine lintegral_mono_ae ?_
    filter_upwards [hle] with ω hω
    rw [← lintegral_const_mul' _ _ (ENNReal.pow_ne_top hC)]
    refine lintegral_mono fun s => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun k _ => ?_
    calc ‖I s ω k‖ₑ ^ 2 ≤ (C * ‖Ψ s ω k‖ₑ) ^ 2 := by gcongr; exact hω s k
      _ = _ := by rw [mul_pow]
  exact lt_of_le_of_lt this (ENNReal.mul_lt_top (ENNReal.pow_lt_top hC.lt_top) (hΨ.sq T))

theorem fderiv_pow_four (x : ℝ) :
    fderiv ℝ (fun y : ℝ => y ^ 4) x = (4 * x ^ 3) • (ContinuousLinearMap.id ℝ ℝ) := by
  have := (hasDerivAt_pow 4 x).hasFDerivAt
  rw [this.fderiv]
  ext; simp

theorem fderiv_fderiv_pow_four (x u v : ℝ) :
    fderiv ℝ (fderiv ℝ (fun y : ℝ => y ^ 4)) x u v = 12 * x ^ 2 * u * v := by
  have h : fderiv ℝ (fun y : ℝ => y ^ 4) = fun x => (4 * x ^ 3) • (ContinuousLinearMap.id ℝ ℝ) :=
    funext fderiv_pow_four
  rw [h]
  have h2 : HasDerivAt (fun x : ℝ => 4 * x ^ 3) (4 * (3 * x ^ 2)) x := by
    simpa using ((hasDerivAt_pow 3 x).const_mul 4)
  have h3 := (h2.hasFDerivAt.smul_const (ContinuousLinearMap.id ℝ ℝ))
  rw [h3.fderiv]
  simp only [ContinuousLinearMap.smulRight_apply, ContinuousLinearMap.toSpanSingleton_apply,
    smul_eq_mul]
  simp only [smul_apply, ContinuousLinearMap.id_apply, smul_eq_mul]
  ring

theorem itoDrift_pow_four (T : ℝ) (X : ℝ → Ω → ℝ) (Ψ : ℝ → Ω → ι → ℝ) (s : ℝ) (ω : Ω) :
    itoDrift T (fun _ x => x ^ 4) X (fun _ _ => (0 : ℝ)) Ψ s ω =
      6 * X s ω ^ 2 * ∑ k, Ψ s ω k ^ 2 := by
  unfold itoDrift
  have h0 : derivWithin (fun r : ℝ => (fun (_ : ℝ) (x : ℝ) => x ^ 4) r (X s ω)) (Set.Icc 0 T) s
      = 0 := by simp [derivWithin_fun_const]
  rw [h0]
  simp only [map_zero, zero_add]
  simp only [fderiv_fderiv_pow_four]
  rw [Finset.mul_sum, Finset.mul_sum]
  exact Finset.sum_congr rfl fun k _ => by ring

theorem fourth_identity_bdd [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    {Ψ : ℝ → Ω → ι → ℝ} (hΨ : IsProgressiveL2 P ℱ Ψ) {T : ℝ} (hT : 0 ≤ T) {R : ℝ}
    (hR : ∀ᵐ ω ∂P, ∀ t, |itoIntegral P ℱ W Ψ t ω| ≤ R) :
    ∫⁻ ω, ‖itoIntegral P ℱ W Ψ T ω‖ₑ ^ 4 ∂P =
      6 * ∫⁻ ω, (∫⁻ s in Set.Icc 0 T,
        ‖itoIntegral P ℱ W Ψ s ω‖ₑ ^ 2 * ∑ k, ‖Ψ s ω k‖ₑ ^ 2) ∂P := by
  set N := itoIntegral P ℱ W Ψ with hN
  let X₀ : Ω → ℝ := fun _ => 0
  let b : ℝ → Ω → ℝ := fun _ _ => 0
  have hΨE : IsProgressiveLocL2E P ℱ Ψ := ⟨hΨ.prog, hΨ.locL2.sq⟩
  have hb : IsProgressiveLocL1 P ℱ b :=
    ⟨isProgressive_const _ _, fun T' => Eventually.of_forall fun ω => integrableOn_const (by simp) (by simp)⟩
  have hf : IsC12On T Set.univ (fun (_ : ℝ) (x : ℝ) => x ^ 4) :=
    isC12On_of_contDiff T _ (fun x : ℝ => x ^ 4) (contDiff_id.pow 4)
  have hito := ito_formula hW hT (fun (_ : ℝ) (x : ℝ) => x ^ 4) hf X₀ (fun t => measurable_const) b hb Ψ hΨE
  set X := itoProcess P ℱ W X₀ b Ψ with hX
  have hXN : ∀ᵐ ω ∂P, ∀ t, X t ω = N t ω := by
    have h1 := localItoIntegralE_apply hW hΨE (ContinuousLinearMap.id ℝ ℝ)
    have h2 := localItoIntegral_eq_itoIntegral hW hΨ
    filter_upwards [h1, h2] with ω hω1 hω2 t
    have e1 := hω1 t
    simp only [ContinuousLinearMap.id_apply] at e1
    simp only [hX, itoProcess, X₀, b, integral_zero, add_zero, zero_add]
    rw [e1, hω2 t]
  have hXad : Adapted ℱ X := adapted_itoProcess X₀ (fun t => measurable_const) b hb.prog Ψ
  have hXc : ∀ᵐ ω ∂P, Continuous fun t => X t ω := continuous_itoProcess X₀ b hb Ψ
  have hIprog := isProgressiveLocL2_itoIntegrand Set.univ isClosed_univ Set.univ
    (Set.Subset.refl _) (fun (_ : ℝ) (x : ℝ) => x ^ 4) hf X
    (isProgressive_itoProcess X₀ (fun t => measurable_const) b hb.prog Ψ) hXc Ψ hΨE
  set I := itoIntegrand T Set.univ (fun (_ : ℝ) (x : ℝ) => x ^ 4) X Ψ with hI
  have hIle : ∀ᵐ ω ∂P, ∀ s k, ‖I s ω k‖ₑ ≤ ENNReal.ofReal (4 * R ^ 3) * ‖Ψ s ω k‖ₑ := by
    filter_upwards [hXN, hR] with ω hω1 hω2 s k
    have hx : |X s ω| ≤ R := by rw [hω1 s]; exact hω2 s
    have hval : I s ω k = if s ∈ Set.Icc 0 T then 4 * X s ω ^ 3 * Ψ s ω k else 0 := by
      simp only [hI, itoIntegrand, Set.indicator, Set.mem_univ, Set.mem_ofPred_eq, ite_true,
        fderiv_pow_four]
      simp
    have hR0 : 0 ≤ R := (abs_nonneg _).trans hx
    rw [hval]
    split_ifs
    · rw [Real.enorm_eq_ofReal_abs, Real.enorm_eq_ofReal_abs,
        ← ENNReal.ofReal_mul (by positivity : (0:ℝ) ≤ 4 * R ^ 3)]
      refine ENNReal.ofReal_le_ofReal ?_
      rw [abs_mul, abs_mul, abs_pow]
      have : |X s ω| ^ 3 ≤ R ^ 3 := pow_le_pow_left₀ (abs_nonneg _) hx 3
      have h4 : |(4 : ℝ)| = 4 := by norm_num
      rw [h4]
      nlinarith [abs_nonneg (Ψ s ω k)]
    · simp
  have hIL2 : IsProgressiveL2 P ℱ I := IsProgressiveL2.of_ae_le hΨ hIprog.prog ENNReal.ofReal_ne_top hIle
  have hL := localItoIntegral_eq_itoIntegral hW hIL2
  have hLint : Integrable (itoIntegral P ℱ W I T) P :=
    (memLp_two_itoIntegral hW hIL2 T).integrable one_le_two
  have hL0 : ∫ ω, itoIntegral P ℱ W I T ω ∂P = 0 := integral_itoIntegral hW hIL2 T
  set D : Ω → ℝ := fun ω => ∫ s in Set.Icc 0 T, 6 * N s ω ^ 2 * ∑ k, Ψ s ω k ^ 2 with hD
  dsimp only at hito
  have hid : ∀ᵐ ω ∂P, IntegrableOn (fun s => 6 * N s ω ^ 2 * ∑ k, Ψ s ω k ^ 2) (Set.Icc 0 T) ∧
      N T ω ^ 4 = D ω + itoIntegral P ℱ W I T ω := by
    filter_upwards [hito, hXN, hL] with ω hω hXω hLω
    obtain ⟨hint, hall⟩ := hω
    have hdr : ∀ s, itoDrift T (fun (_ : ℝ) (x : ℝ) => x ^ 4) X b Ψ s ω =
        6 * N s ω ^ 2 * ∑ k, Ψ s ω k ^ 2 := fun s => by rw [itoDrift_pow_four, hXω s]
    simp only [hdr] at hint hall
    refine ⟨hint, ?_⟩
    have := hall T ⟨hT, le_rfl⟩
    rw [hXω T, hLω T] at this
    simpa [hD, X₀] using this
  have hNm : Measurable (N T) := ((adapted_itoIntegral P ℱ W Ψ) T).mono (ℱ.le T) le_rfl
  have hbd4 : Integrable (fun ω => N T ω ^ 4) P := by
    refine Integrable.mono' (integrable_const (R ^ 4)) (hNm.pow_const 4).aestronglyMeasurable ?_
    filter_upwards [hR] with ω hω
    rw [Real.norm_eq_abs, abs_pow]
    exact pow_le_pow_left₀ (abs_nonneg _) (hω T) 4
  have hDint : Integrable D P := by
    have : D =ᵐ[P] fun ω => N T ω ^ 4 - itoIntegral P ℱ W I T ω := by
      filter_upwards [hid] with ω hω
      rw [hω.2]; ring
    exact (hbd4.sub hLint).congr this.symm
  have hDnn : ∀ ω, 0 ≤ D ω := fun ω =>
    setIntegral_nonneg measurableSet_Icc fun s _ => by positivity
  have hint_eq : ∫ ω, N T ω ^ 4 ∂P = ∫ ω, D ω ∂P := by
    calc ∫ ω, N T ω ^ 4 ∂P = ∫ ω, (D ω + itoIntegral P ℱ W I T ω) ∂P :=
          integral_congr_ae (by filter_upwards [hid] with ω hω; exact hω.2)
      _ = ∫ ω, D ω ∂P + ∫ ω, itoIntegral P ℱ W I T ω ∂P := integral_add hDint hLint
      _ = ∫ ω, D ω ∂P := by rw [hL0, add_zero]
  calc ∫⁻ ω, ‖N T ω‖ₑ ^ 4 ∂P = ∫⁻ ω, ENNReal.ofReal (N T ω ^ 4) ∂P := by
        refine lintegral_congr fun ω => ?_
        rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), pow_abs, abs_of_nonneg (by positivity)]
    _ = ENNReal.ofReal (∫ ω, N T ω ^ 4 ∂P) :=
        (ofReal_integral_eq_lintegral_ofReal hbd4 (Eventually.of_forall fun ω => by positivity)).symm
    _ = ENNReal.ofReal (∫ ω, D ω ∂P) := by rw [hint_eq]
    _ = ∫⁻ ω, ENNReal.ofReal (D ω) ∂P :=
        ofReal_integral_eq_lintegral_ofReal hDint (Eventually.of_forall hDnn)
    _ = ∫⁻ ω, 6 * (∫⁻ s in Set.Icc 0 T, ‖N s ω‖ₑ ^ 2 * ∑ k, ‖Ψ s ω k‖ₑ ^ 2) ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hid] with ω hω
        rw [hD]
        simp only []
        rw [ofReal_integral_eq_lintegral_ofReal hω.1 (Eventually.of_forall fun s => by positivity),
          ← lintegral_const_mul' _ _ (by norm_num)]
        exact lintegral_congr fun s => ofReal_six_mul_sq_sum _ _
    _ = _ := lintegral_const_mul' _ _ (by norm_num)



/-- The localising time `inf {t ≥ 0 : |M_t| ≥ R}` of the integral `M = ∫ Φ dW`. -/
def bdgTime (P : Measure Ω) (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → ι → ℝ) (Φ : ℝ → Ω → ι → ℝ)
    (R : ℝ) : Ω → WithTop ℝ :=
  exitTime (itoIntegral P ℱ W Φ) (Metric.ball (0 : ℝ) R) 0

theorem isStoppingTime_bdgTime (R : ℝ) : IsStoppingTime ℱ (bdgTime P ℱ W Φ R) :=
  isStoppingTime_exitTime ℱ _ (adapted_itoIntegral P ℱ W Φ) (continuous_itoIntegral P ℱ W Φ)
    Metric.isOpen_ball 0

theorem abs_itoIntegral_le_of_le_bdgTime {R : ℝ} (hR : 0 < R) (ω : Ω) {r : ℝ}
    (hr : (r : WithTop ℝ) ≤ bdgTime P ℱ W Φ R ω) : |itoIntegral P ℱ W Φ r ω| ≤ R := by
  rcases le_or_gt r 0 with hr0 | hr0
  · rw [itoIntegral_of_nonpos P ℱ W Φ hr0 ω]; simpa using hR.le
  · have hS : IsClosed {s : ℝ | |itoIntegral P ℱ W Φ s ω| ≤ R} :=
      isClosed_le ((continuous_itoIntegral P ℱ W Φ ω).abs) continuous_const
    have hsub : Set.Ioo 0 r ⊆ {s : ℝ | |itoIntegral P ℱ W Φ s ω| ≤ R} := by
      intro s hs
      have hlt : (s : WithTop ℝ) < bdgTime P ℱ W Φ R ω :=
        lt_of_lt_of_le (by exact_mod_cast hs.2) hr
      have := mem_of_lt_exitTime (itoIntegral P ℱ W Φ) (Metric.ball (0 : ℝ) R) 0 ω s hs.1.le hlt
      have h' : |itoIntegral P ℱ W Φ s ω| < R := by simpa [Real.dist_eq] using this
      exact h'.le
    have hcl : r ∈ closure (Set.Ioo 0 r) := by
      rw [closure_Ioo hr0.ne]; exact ⟨hr0.le, le_rfl⟩
    exact (hS.closure_subset_iff.2 hsub) hcl

theorem stoppedProcess_of_le {M : ℝ → Ω → ℝ} {σ : Ω → WithTop ℝ} {ω : Ω} {t : ℝ}
    (h : (t : WithTop ℝ) ≤ σ ω) : stoppedProcess M σ t ω = M t ω := by
  cases hσ : σ ω with
  | top => exact stoppedProcess_apply_top hσ t
  | coe a =>
    rw [stoppedProcess_apply_coe hσ, min_eq_left]
    rw [hσ] at h
    exact_mod_cast h

theorem abs_stoppedProcess_bdgTime_le {R : ℝ} (hR : 0 < R) (ω : Ω) (t : ℝ) :
    |stoppedProcess (itoIntegral P ℱ W Φ) (bdgTime P ℱ W Φ R) t ω| ≤ R := by
  cases hσ : bdgTime P ℱ W Φ R ω with
  | top =>
    rw [stoppedProcess_apply_top hσ]
    exact abs_itoIntegral_le_of_le_bdgTime hR ω (by rw [hσ]; exact le_top)
  | coe a =>
    rw [stoppedProcess_apply_coe hσ]
    exact abs_itoIntegral_le_of_le_bdgTime hR ω (by
      rw [hσ]; exact_mod_cast min_le_right t a)

theorem bdgTime_nonneg (R : ℝ) (ω : Ω) : (0 : WithTop ℝ) ≤ bdgTime P ℱ W Φ R ω :=
  le_hittingAfter ω

theorem eventually_lt_bdgTime (ω : Ω) (T : ℝ) :
    ∃ n₀ : ℕ, ∀ n ≥ n₀, (T : WithTop ℝ) < bdgTime P ℱ W Φ ((n : ℝ) + 1) ω := by
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).bddAbove_image
    ((continuous_itoIntegral P ℱ W Φ ω).abs.continuousOn)
  obtain ⟨n₀, hn₀⟩ := exists_nat_gt B
  refine ⟨n₀, fun n hn => ?_⟩
  by_contra hcon
  rw [not_lt] at hcon
  have hcont := continuous_itoIntegral P ℱ W Φ ω
  have := (hittingAfter_le_iff_of_isClosed (itoIntegral P ℱ W Φ) ω hcont
    (Metric.isOpen_ball (x := (0 : ℝ)) (ε := (n : ℝ) + 1)).isClosed_compl 0 T).1 hcon
  obtain ⟨r, hr0, hrT, hr⟩ := this
  have h1 : (n : ℝ) + 1 ≤ |itoIntegral P ℱ W Φ r ω| := by
    simpa [Real.dist_eq] using hr
  have h2 := hB ⟨r, ⟨hr0, hrT⟩, rfl⟩
  have h3 : (n₀ : ℝ) ≤ n := by exact_mod_cast hn
  linarith


theorem two_mul_le_sq_add_sq (k : ℝ≥0∞) (hk : k ≠ ∞) (x y : ℝ≥0∞) :
    2 * k * (x * y) ≤ x ^ 2 + k ^ 2 * y ^ 2 := by
  by_cases hx : x = ∞
  · subst hx; simp
  by_cases hy : y = ∞
  · subst hy
    by_cases hk0 : k = 0
    · simp [hk0]
    · simp [hk0]
  lift x to ℝ≥0 using hx
  lift y to ℝ≥0 using hy
  lift k to ℝ≥0 using hk
  have : 2 * k * (x * y) ≤ x ^ 2 + k ^ 2 * y ^ 2 := by
    rw [← NNReal.coe_le_coe]
    push_cast
    nlinarith [sq_nonneg ((x : ℝ) - k * y)]
  exact_mod_cast this

omit [Fintype ι] in
theorem enorm_stopIntegrand_le_bdg (Φ : ℝ → Ω → ι → ℝ) (τ : Ω → WithTop ℝ) (s : ℝ) (ω : Ω) (k : ι) :
    ‖stopIntegrand Φ τ s ω k‖ₑ ≤ ‖Φ s ω k‖ₑ := by
  unfold stopIntegrand Set.indicator
  split_ifs <;> simp

theorem bdg_four_stopped [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {T : ℝ} (hT : 0 ≤ T) {R : ℝ} (hR : 0 < R) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T,
        ‖itoIntegral P ℱ W (stopIntegrand Φ (bdgTime P ℱ W Φ R)) t ω‖ₑ) ^ 4 ∂P ≤
      bdgConstFour * ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2) ^ 2 ∂P := by
  set τ := bdgTime P ℱ W Φ R with hτdef
  have hτ : IsStoppingTime ℱ τ := isStoppingTime_bdgTime R
  set Ψ := stopIntegrand Φ τ with hΨdef
  have hΨ : IsProgressiveL2 P ℱ Ψ := hΦ.stopIntegrand hτ
  set N := itoIntegral P ℱ W Ψ with hNdef
  have hstop := itoIntegral_stopIntegrand hW hΦ hτ
  have hbd : ∀ᵐ ω ∂P, ∀ t, |N t ω| ≤ R := by
    filter_upwards [hstop] with ω h t
    have e : N t ω = stoppedProcess (itoIntegral P ℱ W Φ) τ t ω := h t
    rw [e]; exact abs_stoppedProcess_bdgTime_le hR ω t
  have hid := fourth_identity_bdd hW hΨ hT hbd
  set S : Ω → ℝ≥0∞ := fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖N t ω‖ₑ with hS
  set A : Ω → ℝ≥0∞ := fun ω => ∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2 with hA
  have hdoob := doob_four_cont (martingale_itoIntegral hW hΨ) (continuous_itoIntegral P ℱ W Ψ) hT
  have hNmeas : ∀ t, Measurable (N t) := fun t => ((adapted_itoIntegral P ℱ W Ψ) t).mono (ℱ.le t) le_rfl
  have hSm : Measurable S := measurable_iSup_enorm_Icc hNmeas (continuous_itoIntegral P ℱ W Ψ) hT
  have hSle : ∀ᵐ ω ∂P, S ω ≤ ENNReal.ofReal R := by
    filter_upwards [hbd] with ω hω
    refine iSup₂_le fun t _ => ?_
    rw [Real.enorm_eq_ofReal_abs]
    exact ENNReal.ofReal_le_ofReal (hω t)
  -- pointwise bound on the integrand
  have hJ : ∀ᵐ ω ∂P, ∫⁻ s in Set.Icc 0 T, ‖N s ω‖ₑ ^ 2 * ∑ k, ‖Ψ s ω k‖ₑ ^ 2 ≤ S ω ^ 2 * A ω := by
    filter_upwards [hSle] with ω hω
    rw [hA, ← lintegral_const_mul' _ _ (ENNReal.pow_ne_top (ne_top_of_le_ne_top ENNReal.ofReal_ne_top hω))]
    refine setLIntegral_mono' measurableSet_Icc fun s hs => ?_
    have hsS : ‖N s ω‖ₑ ≤ S ω := le_iSup₂_of_le (f := fun t _ => ‖N t ω‖ₑ) s hs le_rfl
    refine mul_le_mul' (pow_le_pow_left' hsS 2) ?_
    exact Finset.sum_le_sum fun k _ => pow_le_pow_left' (enorm_stopIntegrand_le_bdg Φ τ s ω k) 2
  have hk : ENNReal.ofReal ((4 / 3 : ℝ) ^ 4) * 6 = ENNReal.ofReal (512 / 27) := by
    rw [show (6 : ℝ≥0∞) = ENNReal.ofReal 6 by simp, ← ENNReal.ofReal_mul (by norm_num)]
    norm_num
  set k : ℝ≥0∞ := ENNReal.ofReal (512 / 27) with hkdef
  have hkne : k ≠ ∞ := ENNReal.ofReal_ne_top
  set Sq := ∫⁻ ω, S ω ^ 4 ∂P with hSq
  set X := ∫⁻ ω, S ω ^ 2 * A ω ∂P with hX
  set Q := ∫⁻ ω, A ω ^ 2 ∂P with hQ
  have h1 : Sq ≤ k * X := by
    calc Sq ≤ ENNReal.ofReal ((4 / 3 : ℝ) ^ 4) * ∫⁻ ω, ‖N T ω‖ₑ ^ 4 ∂P := hdoob
      _ = ENNReal.ofReal ((4 / 3 : ℝ) ^ 4) * (6 * ∫⁻ ω, (∫⁻ s in Set.Icc 0 T,
            ‖N s ω‖ₑ ^ 2 * ∑ k, ‖Ψ s ω k‖ₑ ^ 2) ∂P) := by rw [hid]
      _ ≤ ENNReal.ofReal ((4 / 3 : ℝ) ^ 4) * (6 * X) := by
          gcongr
          exact lintegral_mono_ae hJ
      _ = k * X := by rw [← mul_assoc, hk]
  have h2 : 2 * k * X ≤ Sq + k ^ 2 * Q := by
    calc 2 * k * X = ∫⁻ ω, 2 * k * (S ω ^ 2 * A ω) ∂P := by
          rw [hX, lintegral_const_mul' _ _ (ENNReal.mul_ne_top (by norm_num) hkne)]
      _ ≤ ∫⁻ ω, (S ω ^ 4 + k ^ 2 * A ω ^ 2) ∂P := by
          refine lintegral_mono fun ω => ?_
          have := two_mul_le_sq_add_sq k hkne (S ω ^ 2) (A ω)
          rwa [← pow_mul] at this
      _ = Sq + k ^ 2 * Q := by
          rw [lintegral_add_left (hSm.pow_const 4), lintegral_const_mul' _ _ (ENNReal.pow_ne_top hkne)]
  have hSqfin : Sq ≠ ∞ := by
    have : Sq ≤ ∫⁻ _ω, ENNReal.ofReal R ^ 4 ∂P := by
      refine lintegral_mono_ae ?_
      filter_upwards [hSle] with ω hω
      gcongr
    refine ne_top_of_le_ne_top ?_ this
    simp
  have h3 : Sq + Sq ≤ Sq + k ^ 2 * Q := by
    calc Sq + Sq = 2 * Sq := by rw [two_mul]
      _ ≤ 2 * (k * X) := by gcongr
      _ = 2 * k * X := by rw [mul_assoc]
      _ ≤ _ := h2
  have h4 := (ENNReal.add_le_add_iff_left hSqfin).1 h3
  rw [bdgConstFour, show ENNReal.ofReal ((512 / 27 : ℝ) ^ 2) = k ^ 2 by
    rw [hkdef, ENNReal.ofReal_pow (by norm_num)]]
  exact h4

/-- `p = 4` BDG bound without the finiteness hypothesis. -/
theorem bdg_four_aux [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖itoIntegral P ℱ W Φ t ω‖ₑ) ^ 4 ∂P ≤
      bdgConstFour * ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2) ^ 2 ∂P := by
  let Ψ : ℕ → ℝ → Ω → ι → ℝ := fun n => stopIntegrand Φ (bdgTime P ℱ W Φ ((n : ℝ) + 1))
  let Sn : ℕ → Ω → ℝ≥0∞ := fun n ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖itoIntegral P ℱ W (Ψ n) t ω‖ₑ
  have hSnm : ∀ n, Measurable (Sn n) := fun n =>
    measurable_iSup_enorm_Icc (fun t => ((adapted_itoIntegral P ℱ W (Ψ n)) t).mono (ℱ.le t) le_rfl)
      (continuous_itoIntegral P ℱ W (Ψ n)) hT
  have hstop : ∀ᵐ ω ∂P, ∀ n t, itoIntegral P ℱ W (Ψ n) t ω =
      stoppedProcess (itoIntegral P ℱ W Φ) (bdgTime P ℱ W Φ ((n : ℝ) + 1)) t ω := by
    rw [ae_all_iff]
    intro n
    exact itoIntegral_stopIntegrand hW hΦ (isStoppingTime_bdgTime _)
  have hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, Sn n ω = ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖itoIntegral P ℱ W Φ t ω‖ₑ := by
    filter_upwards [hstop] with ω hω
    obtain ⟨n₀, hn₀⟩ := eventually_lt_bdgTime (P := P) (ℱ := ℱ) (W := W) (Φ := Φ) ω T
    filter_upwards [eventually_ge_atTop n₀] with n hn
    refine iSup_congr fun t => iSup_congr fun ht => ?_
    rw [hω n t, stoppedProcess_of_le]
    exact (lt_of_le_of_lt (by exact_mod_cast ht.2) (hn₀ n hn)).le
  calc ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖itoIntegral P ℱ W Φ t ω‖ₑ) ^ 4 ∂P
      = ∫⁻ ω, liminf (fun n => Sn n ω ^ 4) atTop ∂P := by
        refine lintegral_congr_ae ?_
        filter_upwards [hev] with ω hω
        have : ∀ᶠ n in atTop, Sn n ω ^ 4 = (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖itoIntegral P ℱ W Φ t ω‖ₑ) ^ 4 :=
          hω.mono fun n hn => by rw [hn]
        rw [Filter.liminf_congr this, Filter.liminf_const]
    _ ≤ liminf (fun n => ∫⁻ ω, Sn n ω ^ 4 ∂P) atTop :=
        lintegral_liminf_le fun n => (hSnm n).pow_const 4
    _ ≤ _ := by
        refine (liminf_le_limsup).trans (limsup_le_of_le (by isBoundedDefault) ?_)
        refine Eventually.of_forall fun n => ?_
        exact bdg_four_stopped hW hΦ hT (by positivity)

theorem lintegral_itoIntegral_fourth_aux [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {T : ℝ} (hT : 0 ≤ T)
    (hfin : ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2) ^ 2 ∂P < ∞) :
    ∫⁻ ω, ‖itoIntegral P ℱ W Φ T ω‖ₑ ^ 4 ∂P =
      6 * ∫⁻ ω, (∫⁻ s in Set.Icc 0 T,
        ‖itoIntegral P ℱ W Φ s ω‖ₑ ^ 2 * ∑ k, ‖Φ s ω k‖ₑ ^ 2) ∂P := by
  set M := itoIntegral P ℱ W Φ with hM
  let τ : ℕ → Ω → WithTop ℝ := fun n => bdgTime P ℱ W Φ ((n : ℝ) + 1)
  let Ψ : ℕ → ℝ → Ω → ι → ℝ := fun n => stopIntegrand Φ (τ n)
  have hΨ : ∀ n, IsProgressiveL2 P ℱ (Ψ n) := fun n => hΦ.stopIntegrand (isStoppingTime_bdgTime _)
  let Nn : ℕ → ℝ → Ω → ℝ := fun n => itoIntegral P ℱ W (Ψ n)
  let S : Ω → ℝ≥0∞ := fun ω => ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖M t ω‖ₑ
  let J : Ω → ℝ≥0∞ := fun ω => ∫⁻ s in Set.Icc 0 T, ‖M s ω‖ₑ ^ 2 * ∑ k, ‖Φ s ω k‖ₑ ^ 2
  let Jn : ℕ → Ω → ℝ≥0∞ := fun n ω =>
    ∫⁻ s in Set.Icc 0 T, ‖Nn n s ω‖ₑ ^ 2 * ∑ k, ‖Ψ n s ω k‖ₑ ^ 2
  have hMmeas : ∀ t, Measurable (M t) := fun t => ((adapted_itoIntegral P ℱ W Φ) t).mono (ℱ.le t) le_rfl
  have hNmeas : ∀ n t, Measurable (Nn n t) := fun n t =>
    ((adapted_itoIntegral P ℱ W (Ψ n)) t).mono (ℱ.le t) le_rfl
  have hSm : Measurable S := measurable_iSup_enorm_Icc hMmeas (continuous_itoIntegral P ℱ W Φ) hT
  have hJm : Measurable J := measurable_lintegral_prog hΦ.prog (continuous_itoIntegral P ℱ W Φ) hMmeas T
  have hJnm : ∀ n, Measurable (Jn n) := fun n =>
    measurable_lintegral_prog (hΨ n).prog (continuous_itoIntegral P ℱ W (Ψ n)) (hNmeas n) T
  -- the finiteness of E S⁴
  have hSfin : ∫⁻ ω, S ω ^ 4 ∂P ≠ ∞ := by
    have := bdg_four_aux hW hΦ hT
    refine ne_top_of_le_ne_top ?_ this
    exact ENNReal.mul_ne_top (by simp [bdgConstFour]) hfin.ne
  -- stopped identities
  have hstop : ∀ᵐ ω ∂P, ∀ n t, Nn n t ω = stoppedProcess M (τ n) t ω := by
    rw [ae_all_iff]
    intro n
    exact itoIntegral_stopIntegrand hW hΦ (isStoppingTime_bdgTime _)
  have hid : ∀ n, ∫⁻ ω, ‖Nn n T ω‖ₑ ^ 4 ∂P = 6 * ∫⁻ ω, Jn n ω ∂P := by
    intro n
    have hbd : ∀ᵐ ω ∂P, ∀ t, |Nn n t ω| ≤ (n : ℝ) + 1 := by
      filter_upwards [hstop] with ω h t
      rw [h n t]
      exact abs_stoppedProcess_bdgTime_le (by positivity) ω t
    exact fourth_identity_bdd hW (hΨ n) hT hbd
  -- pointwise comparison
  have hpt : ∀ ω, (∀ n t, Nn n t ω = stoppedProcess M (τ n) t ω) → ∀ n s,
      ‖Nn n s ω‖ₑ ^ 2 * ∑ k, ‖Ψ n s ω k‖ₑ ^ 2 ≤ ‖M s ω‖ₑ ^ 2 * ∑ k, ‖Φ s ω k‖ₑ ^ 2 := by
    intro ω hω n s
    by_cases hs : (s : WithTop ℝ) ≤ τ n ω
    · rw [hω n s, stoppedProcess_of_le hs]
      refine le_of_eq ?_
      simp only [Ψ, stopIntegrand, Set.indicator, Set.mem_ofPred_eq, hs, ite_true]
    · have : ∀ k, Ψ n s ω k = 0 := fun k => by
        simp only [Ψ, stopIntegrand, Set.indicator, Set.mem_ofPred_eq, hs, ite_false]; rfl
      simp [this]
  have hJle : ∀ᵐ ω ∂P, ∀ n, Jn n ω ≤ J ω := by
    filter_upwards [hstop] with ω hω n
    exact lintegral_mono fun s => hpt ω hω n s
  have hNle : ∀ᵐ ω ∂P, ∀ n, ‖Nn n T ω‖ₑ ^ 4 ≤ S ω ^ 4 := by
    filter_upwards [hstop] with ω hω n
    refine pow_le_pow_left' ?_ 4
    rw [hω n T]
    cases hσ : τ n ω with
    | top =>
      rw [stoppedProcess_apply_top hσ]
      exact le_iSup₂_of_le (f := fun t _ => ‖M t ω‖ₑ) T ⟨hT, le_rfl⟩ le_rfl
    | coe a =>
      rw [stoppedProcess_apply_coe hσ]
      have ha : 0 ≤ a := by
        have := bdgTime_nonneg (P := P) (ℱ := ℱ) (W := W) (Φ := Φ) ((n : ℝ) + 1) ω
        change (0 : WithTop ℝ) ≤ τ n ω at this
        rw [hσ] at this
        exact_mod_cast this
      exact le_iSup₂_of_le (f := fun t _ => ‖M t ω‖ₑ) (min T a)
        ⟨le_min hT ha, min_le_left _ _⟩ le_rfl
  have hev : ∀ᵐ ω ∂P, ∀ᶠ n in atTop, Nn n T ω = M T ω ∧ Jn n ω = J ω := by
    filter_upwards [hstop] with ω hω
    obtain ⟨n₀, hn₀⟩ := eventually_lt_bdgTime (P := P) (ℱ := ℱ) (W := W) (Φ := Φ) ω T
    filter_upwards [eventually_ge_atTop n₀] with n hn
    have hlt := hn₀ n hn
    refine ⟨?_, ?_⟩
    · rw [hω n T, stoppedProcess_of_le hlt.le]
    · refine setLIntegral_congr_fun measurableSet_Icc fun s hs => ?_
      have hs' : (s : WithTop ℝ) ≤ τ n ω := (lt_of_le_of_lt (by exact_mod_cast hs.2) hlt).le
      rw [hω n s, stoppedProcess_of_le hs']
      simp only [Ψ, stopIntegrand, Set.indicator, Set.mem_ofPred_eq, hs', ite_true]
  have hb : Tendsto (fun n => ∫⁻ ω, ‖Nn n T ω‖ₑ ^ 4 ∂P) atTop (𝓝 (∫⁻ ω, ‖M T ω‖ₑ ^ 4 ∂P)) := by
    refine tendsto_lintegral_of_dominated_convergence (fun ω => S ω ^ 4)
      (fun n => ((hNmeas n T).enorm).pow_const 4)
      (fun n => hNle.mono fun ω hω => hω n) hSfin ?_
    filter_upwards [hev] with ω hω
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [hω] with n hn
    rw [hn.1]
  refine le_antisymm ?_ ?_
  · refine le_of_tendsto' hb fun n => ?_
    rw [hid n]
    have : ∫⁻ ω, Jn n ω ∂P ≤ ∫⁻ ω, J ω ∂P := lintegral_mono_ae (hJle.mono fun ω hω => hω n)
    exact mul_le_mul_right this 6
  · calc 6 * ∫⁻ ω, J ω ∂P = ∫⁻ ω, 6 * J ω ∂P := (lintegral_const_mul 6 hJm).symm
      _ ≤ ∫⁻ ω, liminf (fun n => 6 * Jn n ω) atTop ∂P := by
          refine lintegral_mono_ae ?_
          filter_upwards [hev] with ω hω
          have : ∀ᶠ n in atTop, 6 * Jn n ω = 6 * J ω := hω.mono fun n hn => by rw [hn.2]
          rw [Filter.liminf_congr this, Filter.liminf_const]
      _ ≤ liminf (fun n => ∫⁻ ω, 6 * Jn n ω ∂P) atTop :=
          lintegral_liminf_le fun n => (hJnm n).const_mul 6
      _ = liminf (fun n => ∫⁻ ω, ‖Nn n T ω‖ₑ ^ 4 ∂P) atTop := by
          congr 1; funext n
          rw [hid n, lintegral_const_mul 6 (hJnm n)]
      _ = _ := hb.liminf_eq

section Increments

/-- The integrand `1_{(a,b]} Φ`. -/
theorem isProgressiveL2_indicator_Ioc [IsProbabilityMeasure P] (hΦ : IsProgressiveL2 P ℱ Φ)
    (a b : ℝ) :
    IsProgressiveL2 P ℱ (fun r ω => Set.indicator (Set.Ioc a b) (fun _ => Φ r ω) r) := by
  have hprog : IsProgressive ℱ (fun r ω => Set.indicator (Set.Ioc a b) (fun _ => Φ r ω) r) := by
    intro i
    have hset : MeasurableSet[Subtype.instMeasurableSpace.prod (ℱ i)]
        {p : Set.Iic i × Ω | (p.1 : ℝ) ∈ Set.Ioc a b} :=
      measurableSet_Ioc.preimage (measurable_subtype_coe.comp
        (@measurable_fst (Set.Iic i) Ω Subtype.instMeasurableSpace (ℱ i)))
    have := (hΦ.prog i).indicator hset
    convert this using 1
    funext p
    beta_reduce
    by_cases hp : (p.1 : ℝ) ∈ Set.Ioc a b
    · have hp' : p ∈ {p : Set.Iic i × Ω | (p.1 : ℝ) ∈ Set.Ioc a b} := hp
      rw [Set.indicator_of_mem hp (f := fun _ => Φ p.1 p.2), Set.indicator_of_mem hp']
    · have hp' : p ∉ {p : Set.Iic i × Ω | (p.1 : ℝ) ∈ Set.Ioc a b} := hp
      rw [Set.indicator_of_notMem hp, Set.indicator_of_notMem hp']
  refine IsProgressiveL2.of_ae_le hΦ hprog (C := 1) (by simp) (Eventually.of_forall fun ω r k => ?_)
  by_cases hr : r ∈ Set.Ioc a b <;> simp [Set.indicator, hr]

theorem lintegral_sq_indicator_Ioc (Φ : ℝ → Ω → ι → ℝ) {s t : ℝ} (hs : 0 ≤ s) (ω : Ω) :
    ∫⁻ r in Set.Icc 0 t, ∑ k, ‖Set.indicator (Set.Ioc s t) (fun _ => Φ r ω) r k‖ₑ ^ 2 =
      ∫⁻ r in Set.Ioc s t, ∑ k, ‖Φ r ω k‖ₑ ^ 2 := by
  have h1 : ∀ r, ∑ k, ‖Set.indicator (Set.Ioc s t) (fun _ => Φ r ω) r k‖ₑ ^ 2 =
      Set.indicator (Set.Ioc s t) (fun r => ∑ k, ‖Φ r ω k‖ₑ ^ 2) r := fun r => by
    by_cases hr : r ∈ Set.Ioc s t <;> simp [Set.indicator, hr]
  simp_rw [h1]
  rw [lintegral_indicator measurableSet_Ioc, Measure.restrict_restrict measurableSet_Ioc]
  congr 2
  ext r
  simp only [Set.mem_inter_iff, Set.mem_Ioc, Set.mem_Icc]
  constructor
  · exact fun h => h.1
  · exact fun h => ⟨h, by linarith [h.1], h.2⟩

theorem sup_incr_le [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∀ᵐ ω ∂P, ⨆ u ∈ Set.Icc s t, ‖itoIntegral P ℱ W Φ u ω - itoIntegral P ℱ W Φ s ω‖ₑ ≤
      ⨆ u ∈ Set.Icc (0 : ℝ) t, ‖itoIntegral P ℱ W
        (fun r ω => Set.indicator (Set.Ioc s t) (fun _ => Φ r ω) r) u ω‖ₑ := by
  filter_upwards [itoIntegral_indicator_Ioc hW hΦ hs hst] with ω hω
  refine iSup₂_le fun u hu => ?_
  refine le_iSup₂_of_le (f := fun u _ => ‖itoIntegral P ℱ W
    (fun r ω => Set.indicator (Set.Ioc s t) (fun _ => Φ r ω) r) u ω‖ₑ) u ⟨hs.trans hu.1, hu.2⟩ ?_
  rw [hω u, min_eq_left hu.2, min_eq_right hu.1]

/-- BDG `p = 4` for increments. -/
theorem bdg_four_incr_aux [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫⁻ ω, (⨆ u ∈ Set.Icc s t, ‖itoIntegral P ℱ W Φ u ω - itoIntegral P ℱ W Φ s ω‖ₑ) ^ 4 ∂P ≤
      bdgConstFour * ∫⁻ ω, (∫⁻ r in Set.Ioc s t, ∑ k, ‖Φ r ω k‖ₑ ^ 2) ^ 2 ∂P := by
  have hΦ' := isProgressiveL2_indicator_Ioc hΦ s t
  calc _ ≤ ∫⁻ ω, (⨆ u ∈ Set.Icc (0 : ℝ) t, ‖itoIntegral P ℱ W
        (fun r ω => Set.indicator (Set.Ioc s t) (fun _ => Φ r ω) r) u ω‖ₑ) ^ 4 ∂P :=
        lintegral_mono_ae ((sup_incr_le hW hΦ hs hst).mono fun ω hω => pow_le_pow_left' hω 4)
    _ ≤ _ := bdg_four_aux hW hΦ' (hs.trans hst)
    _ = _ := by simp_rw [lintegral_sq_indicator_Ioc Φ hs]

theorem bdg_two_incr_aux [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫⁻ ω, (⨆ u ∈ Set.Icc s t, ‖itoIntegral P ℱ W Φ u ω - itoIntegral P ℱ W Φ s ω‖ₑ) ^ 2 ∂P ≤
      4 * ∫⁻ ω, (∫⁻ r in Set.Ioc s t, ∑ k, ‖Φ r ω k‖ₑ ^ 2) ∂P := by
  have hΦ' := isProgressiveL2_indicator_Ioc hΦ s t
  calc _ ≤ ∫⁻ ω, (⨆ u ∈ Set.Icc (0 : ℝ) t, ‖itoIntegral P ℱ W
        (fun r ω => Set.indicator (Set.Ioc s t) (fun _ => Φ r ω) r) u ω‖ₑ) ^ 2 ∂P :=
        lintegral_mono_ae ((sup_incr_le hW hΦ hs hst).mono fun ω hω => pow_le_pow_left' hω 2)
    _ ≤ 4 * sqIntegralOn P (fun r ω => Set.indicator (Set.Ioc s t) (fun _ => Φ r ω) r) t :=
        lintegral_iSup_itoIntegral_sq_le hW hΦ' t
    _ = _ := by
        unfold sqIntegralOn
        simp_rw [lintegral_sq_indicator_Ioc Φ hs]

end Increments

/-- BDG, `p = 2`: `E sup_{t ≤ T} |M_t|² ≤ 4 E ∫_0^T ∑_k |Φ^k|²`. -/
theorem bdg_two [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) (T : ℝ) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖itoIntegral P ℱ W Φ t ω‖ₑ) ^ 2 ∂P ≤
      4 * sqIntegralOn P Φ T :=
  lintegral_iSup_itoIntegral_sq_le hW hΦ T

/-- The fourth-moment identity behind BDG: `E[M_T⁴] = 6 E ∫_0^T M_s² ∑_k |Φ^k_s|² ds`
(from Itô's formula for `x ↦ x⁴`, valid whenever the right-hand side is finite, with both sides
possibly `∞` otherwise). -/
theorem lintegral_itoIntegral_fourth [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {T : ℝ} (hT : 0 ≤ T)
    (hfin : ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2) ^ 2 ∂P < ∞) :
    ∫⁻ ω, ‖itoIntegral P ℱ W Φ T ω‖ₑ ^ 4 ∂P =
      6 * ∫⁻ ω, (∫⁻ s in Set.Icc 0 T,
        ‖itoIntegral P ℱ W Φ s ω‖ₑ ^ 2 * ∑ k, ‖Φ s ω k‖ₑ ^ 2) ∂P :=
  lintegral_itoIntegral_fourth_aux hW hΦ hT hfin

/-- BDG, `p = 4`: `E sup_{t ≤ T} |M_t|⁴ ≤ (512/27)² E (∫_0^T ∑_k |Φ^k|²)²`. -/
theorem bdg_four [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖itoIntegral P ℱ W Φ t ω‖ₑ) ^ 4 ∂P ≤
      bdgConstFour * ∫⁻ ω, (∫⁻ s in Set.Icc 0 T, ∑ k, ‖Φ s ω k‖ₑ ^ 2) ^ 2 ∂P :=
  bdg_four_aux hW hΦ hT

/-- BDG `p = 4` for increments: `E sup_{s ≤ u ≤ t} |M_u - M_s|⁴ ≤ (512/27)² E (∫_s^t |Φ|²)²`. -/
theorem bdg_four_incr [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫⁻ ω, (⨆ u ∈ Set.Icc s t, ‖itoIntegral P ℱ W Φ u ω - itoIntegral P ℱ W Φ s ω‖ₑ) ^ 4 ∂P ≤
      bdgConstFour * ∫⁻ ω, (∫⁻ r in Set.Ioc s t, ∑ k, ‖Φ r ω k‖ₑ ^ 2) ^ 2 ∂P :=
  bdg_four_incr_aux hW hΦ hs hst

/-- BDG `p = 2` for increments. -/
theorem bdg_two_incr [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W)
    (hΦ : IsProgressiveL2 P ℱ Φ) {s t : ℝ} (hs : 0 ≤ s) (hst : s ≤ t) :
    ∫⁻ ω, (⨆ u ∈ Set.Icc s t, ‖itoIntegral P ℱ W Φ u ω - itoIntegral P ℱ W Φ s ω‖ₑ) ^ 2 ∂P ≤
      4 * ∫⁻ ω, (∫⁻ r in Set.Ioc s t, ∑ k, ‖Φ r ω k‖ₑ ^ 2) ∂P :=
  bdg_two_incr_aux hW hΦ hs hst

/-- Doob's `L⁴` maximal inequality for the Itô integral: `E sup_{t ≤ T} |M_t|⁴ ≤ (4/3)⁴ E|M_T|⁴`. -/
theorem lintegral_iSup_itoIntegral_fourth_le [IsProbabilityMeasure P]
    (hW : IsBrownianFiltration P ℱ W) (hΦ : IsProgressiveL2 P ℱ Φ) {T : ℝ} (hT : 0 ≤ T) :
    ∫⁻ ω, (⨆ t ∈ Set.Icc (0 : ℝ) T, ‖itoIntegral P ℱ W Φ t ω‖ₑ) ^ 4 ∂P ≤
      ENNReal.ofReal ((4 / 3 : ℝ) ^ 4) * ∫⁻ ω, ‖itoIntegral P ℱ W Φ T ω‖ₑ ^ 4 ∂P :=
  doob_four_cont (martingale_itoIntegral hW hΦ) (continuous_itoIntegral P ℱ W Φ) hT

end HRS
