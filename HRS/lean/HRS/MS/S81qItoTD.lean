import HRS.Prob.HilbertMartingale

/-!
# S8.1 (worker S81Q): deterministic weights in countable-index Itô integrals

Namespace `HRS.Whole.S81Q`, prefix `s81q_`.

For a countable-index Itô integral `I = ∫ ξ d𝔚` (`IsItoC`) and a bounded continuous deterministic weight `f`, the integral `J = ∫ f ξ d𝔚` is the
`L²`-limit of the Riemann-Stieltjes sums `∑_p f(a_p) (I_{a_{p+1}} - I_{a_p})` along dyadic grids of `[0,τ]` (`s81q_rs_tendsto`).  Consequently the
weighted integral depends on `ξ` only through the process `I` (`s81q_weighted_eq`): two representations of the same martingale `I` by different
Brownian motions/integrands give a.s. equal weighted integrals.  `s81q_hilbert_isItoC` reads an `IsHilbertItoIntegral` coordinatewise as `IsItoC`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS

namespace HRS.Whole.S81Q

section Basic

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]

/-- Uniqueness of `L²` limits. -/
theorem s81q_ae_eq_of_L2 {a : ℕ → Ω → ℝ} {x y : Ω → ℝ} (hx : AEMeasurable x P) (hy : AEMeasurable y P)
    (ha : ∀ n, AEMeasurable (a n) P)
    (h1 : Tendsto (fun n => ∫⁻ ω, ‖a n ω - x ω‖ₑ ^ 2 ∂P) atTop (𝓝 0))
    (h2 : Tendsto (fun n => ∫⁻ ω, ‖a n ω - y ω‖ₑ ^ 2 ∂P) atTop (𝓝 0)) : x =ᵐ[P] y := by
  have h0 : ∫⁻ ω, ‖x ω - y ω‖ₑ ^ 2 ∂P = 0 := by
    refine le_antisymm ?_ bot_le
    have h3 : Tendsto (fun n => 2 * ∫⁻ ω, ‖a n ω - x ω‖ₑ ^ 2 ∂P +
        2 * ∫⁻ ω, ‖a n ω - y ω‖ₑ ^ 2 ∂P) atTop (𝓝 (2 * 0 + 2 * 0)) :=
      (ENNReal.Tendsto.const_mul h1 (Or.inr (by norm_num))).add
        (ENNReal.Tendsto.const_mul h2 (Or.inr (by norm_num)))
    simp only [mul_zero, add_zero] at h3
    refine ge_of_tendsto' h3 fun n => ?_
    have := lintegral_enorm_sq_add_le' (P := P) ((ha n).sub hx) (hy.sub (ha n))
    have e : ∀ ω, (a n ω - x ω) + (y ω - a n ω) = y ω - x ω := fun ω => by ring
    simp only [Pi.sub_apply, e] at this
    calc ∫⁻ ω, ‖x ω - y ω‖ₑ ^ 2 ∂P = ∫⁻ ω, ‖y ω - x ω‖ₑ ^ 2 ∂P := by
          refine lintegral_congr fun ω => ?_
          rw [← enorm_neg, neg_sub]
      _ ≤ _ := this
      _ = _ := by
          congr 2
          refine lintegral_congr fun ω => ?_
          rw [← enorm_neg, neg_sub]
  filter_upwards [ae_eq_zero_of_lintegral_enorm_sq_eq_zero (hx.sub hy) h0] with ω hω
  simpa [sub_eq_zero] using hω

end Basic

section Grid

/-- The dyadic grid `a_p = τ p / 2^n` of `[0,τ]`. -/
def s81q_grid (τ : ℝ) (n p : ℕ) : ℝ := τ * (p : ℝ) / 2 ^ n

/-- The left-endpoint step approximation `∑_p f(a_p) 1_{(a_p,a_{p+1}]}`. -/
def s81q_stepFun (f : ℝ → ℝ) (τ : ℝ) (n : ℕ) (r : ℝ) : ℝ :=
  ∑ p ∈ Finset.range (2 ^ n),
    (Set.Ioc (s81q_grid τ n p) (s81q_grid τ n (p + 1))).indicator (fun _ => f (s81q_grid τ n p)) r

theorem s81q_grid_zero (τ : ℝ) (n : ℕ) : s81q_grid τ n 0 = 0 := by simp [s81q_grid]

theorem s81q_grid_top (τ : ℝ) (n : ℕ) : s81q_grid τ n (2 ^ n) = τ := by
  unfold s81q_grid
  have : ((2 ^ n : ℕ) : ℝ) = 2 ^ n := by push_cast; ring
  rw [this]; field_simp

theorem s81q_grid_mono {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) {p q : ℕ} (h : p ≤ q) :
    s81q_grid τ n p ≤ s81q_grid τ n q := by
  unfold s81q_grid
  gcongr

theorem s81q_grid_nonneg {τ : ℝ} (hτ : 0 ≤ τ) (n p : ℕ) : 0 ≤ s81q_grid τ n p := by
  unfold s81q_grid; positivity

theorem s81q_grid_le {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) {p : ℕ} (hp : p ≤ 2 ^ n) :
    s81q_grid τ n p ≤ τ := by
  calc s81q_grid τ n p ≤ s81q_grid τ n (2 ^ n) := s81q_grid_mono hτ n hp
    _ = τ := s81q_grid_top τ n

theorem s81q_grid_succ_sub (τ : ℝ) (n p : ℕ) :
    s81q_grid τ n (p + 1) - s81q_grid τ n p = τ / 2 ^ n := by
  unfold s81q_grid; push_cast; ring

/-- The step function is uniformly close to a continuous `f` on `(0,τ]`. -/
theorem s81q_stepFun_close {f : ℝ → ℝ} (hf : Continuous f) {τ : ℝ} (hτ : 0 < τ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N0 : ℕ, ∀ n ≥ N0, ∀ r ∈ Set.Ioc 0 τ, |f r - s81q_stepFun f τ n r| ≤ ε := by
  obtain ⟨δ, hδ, hδf⟩ := Metric.uniformContinuousOn_iff.1
    (isCompact_Icc.uniformContinuousOn_of_continuous hf.continuousOn) ε hε
  obtain ⟨N0, hN0⟩ : ∃ N0 : ℕ, τ / 2 ^ N0 < δ := by
    obtain ⟨N0, hN0⟩ := exists_pow_lt_of_lt_one (div_pos hδ hτ) (by norm_num : (1 / 2 : ℝ) < 1)
    refine ⟨N0, ?_⟩
    rw [one_div, inv_pow] at hN0
    rw [div_lt_iff₀ (by positivity)]
    have h2 : (0 : ℝ) < 2 ^ N0 := by positivity
    calc τ = τ * ((2 ^ N0)⁻¹ * 2 ^ N0) := by rw [inv_mul_cancel₀ h2.ne', mul_one]
      _ = (τ * (2 ^ N0)⁻¹) * 2 ^ N0 := by ring
      _ < δ * 2 ^ N0 := by
          have : τ * (2 ^ N0)⁻¹ < δ := by
            have := (lt_div_iff₀ hτ).1 hN0
            linarith [mul_comm τ ((2 ^ N0 : ℝ)⁻¹)]
          gcongr
  refine ⟨N0, fun n hn r hr => ?_⟩
  have hτn : τ / 2 ^ n ≤ τ / 2 ^ N0 := by
    apply div_le_div_of_nonneg_left hτ.le (by positivity)
    exact pow_le_pow_right₀ (by norm_num) hn
  set x : ℝ := 2 ^ n * r / τ with hx
  have hx0 : 0 < x := by have := hr.1; positivity
  have hx1 : x ≤ 2 ^ n := by
    rw [hx, div_le_iff₀ hτ]
    have := hr.2
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    nlinarith
  set k : ℕ := ⌈x⌉₊ with hk
  have hk1 : 1 ≤ k := Nat.one_le_iff_ne_zero.2 (by
    intro h0; rw [hk, Nat.ceil_eq_zero] at h0; linarith)
  have hk2 : k ≤ 2 ^ n := by
    rw [hk]
    exact Nat.ceil_le.2 (by push_cast; exact hx1)
  set p : ℕ := k - 1 with hp
  have hpk : p + 1 = k := by omega
  have hp1 : (p : ℝ) < x := by
    have h2 : (p : ℝ) + 1 = k := by exact_mod_cast hpk
    have h3 : (k : ℝ) < x + 1 := by
      have := Nat.ceil_lt_add_one hx0.le
      rw [← hk] at this
      exact this
    linarith
  have hp2 : x ≤ (p : ℝ) + 1 := by
    have h2 : (p : ℝ) + 1 = k := by exact_mod_cast hpk
    rw [h2]; exact Nat.le_ceil x
  have hgp : s81q_grid τ n p < r ∧ r ≤ s81q_grid τ n (p + 1) := by
    unfold s81q_grid
    have h2 : (0 : ℝ) < 2 ^ n := by positivity
    constructor
    · rw [div_lt_iff₀ h2]
      rw [hx, lt_div_iff₀ hτ] at hp1
      push_cast; nlinarith
    · rw [le_div_iff₀ h2]
      rw [hx, div_le_iff₀ hτ] at hp2
      push_cast; nlinarith
  have hrmem : r ∈ Set.Ioc (s81q_grid τ n p) (s81q_grid τ n (p + 1)) := hgp
  have hstep : s81q_stepFun f τ n r = f (s81q_grid τ n p) := by
    unfold s81q_stepFun
    rw [Finset.sum_eq_single p]
    · rw [Set.indicator_of_mem hrmem]
    · intro q hq hqp
      rw [Set.indicator_of_notMem]
      intro hmem
      -- q < x ≤ q+1 forces q = p
      have hq1 : (q : ℝ) < x := by
        have h2 := hmem.1
        unfold s81q_grid at h2
        have h3 : (0 : ℝ) < 2 ^ n := by positivity
        rw [div_lt_iff₀ h3] at h2
        rw [hx, lt_div_iff₀ hτ]
        push_cast at h2 ⊢; nlinarith
      have hq2 : x ≤ (q : ℝ) + 1 := by
        have h2 := hmem.2
        unfold s81q_grid at h2
        have h3 : (0 : ℝ) < 2 ^ n := by positivity
        rw [le_div_iff₀ h3] at h2
        rw [hx, div_le_iff₀ hτ]
        push_cast at h2 ⊢; nlinarith
      have hqp1 : q < p + 1 := by
        have : (q : ℝ) < p + 1 := by linarith
        exact_mod_cast this
      have hqp2 : p < q + 1 := by
        have : (p : ℝ) < q + 1 := by linarith
        exact_mod_cast this
      omega
    · intro hp'
      exact absurd (Finset.mem_range.2 (by omega)) hp'
  rw [hstep]
  have hpgrid : s81q_grid τ n p ∈ Set.Icc 0 τ :=
    ⟨s81q_grid_nonneg hτ.le n p, s81q_grid_le hτ.le n (by omega)⟩
  have hdist : dist r (s81q_grid τ n p) < δ := by
    rw [Real.dist_eq, abs_of_nonneg (by linarith [hgp.1])]
    have h1 := s81q_grid_succ_sub τ n p
    have := hgp.2
    linarith
  have := hδf r ⟨hr.1.le, hr.2⟩ (s81q_grid τ n p) hpgrid hdist
  rw [Real.dist_eq] at this
  exact this.le

end Grid

section Weighted

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {A : Type*} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ} {ξ : ℝ → Ω → A → ℝ}
  {I : ℝ → Ω → ℝ}

/-- The Riemann-Stieltjes sum `∑_p f(a_p) (I_{t ∧ a_{p+1}} - I_{t ∧ a_p})`. -/
def s81q_RS (I : ℝ → Ω → ℝ) (f : ℝ → ℝ) (τ : ℝ) (n : ℕ) (t : ℝ) (ω : Ω) : ℝ :=
  ∑ p ∈ Finset.range (2 ^ n), f (s81q_grid τ n p) *
    (I (min t (s81q_grid τ n (p + 1))) ω - I (min t (s81q_grid τ n p)) ω)

theorem s81q_step_itoC (hW : IsCylindricalBrownian P ℱ 𝔚) (hξ : IsCtbl P ℱ ξ)
    (hI : IsItoC P ℱ 𝔚 ξ I) (f : ℝ → ℝ) {τ : ℝ} (hτ : 0 ≤ τ) (n : ℕ) :
    IsCtbl P ℱ (fun r ω a => s81q_stepFun f τ n r * ξ r ω a) ∧
      IsItoC P ℱ 𝔚 (fun r ω a => s81q_stepFun f τ n r * ξ r ω a)
        (fun t ω => s81q_RS I f τ n t ω) := by
  classical
  have hmem : ∀ p ∈ Finset.range (2 ^ n), p ≤ 2 ^ n := fun p hp => (Finset.mem_range.1 hp).le
  have hCt : ∀ p ∈ Finset.range (2 ^ n), IsCtbl P ℱ (fun r ω a =>
      (fun _ : Ω => f (s81q_grid τ n p)) ω *
        (Set.Ioc (s81q_grid τ n p) (s81q_grid τ n (p + 1))).indicator (fun _ => ξ r ω a) r) :=
    fun p _ => hξ.block (a := s81q_grid τ n p) (a' := s81q_grid τ n (p + 1))
      (c := fun _ => f (s81q_grid τ n p)) measurable_const (C := |f (s81q_grid τ n p)|)
      (fun _ => le_rfl)
  have hIt : ∀ p ∈ Finset.range (2 ^ n), IsItoC P ℱ 𝔚 (fun r ω a =>
      (fun _ : Ω => f (s81q_grid τ n p)) ω *
        (Set.Ioc (s81q_grid τ n p) (s81q_grid τ n (p + 1))).indicator (fun _ => ξ r ω a) r)
      (fun t ω => (fun _ : Ω => f (s81q_grid τ n p)) ω *
        (I (min t (s81q_grid τ n (p + 1))) ω - I (min t (s81q_grid τ n p)) ω)) :=
    fun p hp => hI.block hW hξ (s81q_grid_nonneg hτ n p)
      (s81q_grid_mono hτ n (Nat.le_succ p)) (c := fun _ => f (s81q_grid τ n p)) measurable_const
      (C := |f (s81q_grid τ n p)|) (fun _ => le_rfl)
  obtain ⟨h1, h2⟩ := IsItoC.finset_sum hW (Finset.range (2 ^ n)) _ _ hCt hIt
  have e1 : (fun r ω a => ∑ p ∈ Finset.range (2 ^ n), (fun _ : Ω => f (s81q_grid τ n p)) ω *
      (Set.Ioc (s81q_grid τ n p) (s81q_grid τ n (p + 1))).indicator (fun _ => ξ r ω a) r) =
      fun r ω a => s81q_stepFun f τ n r * ξ r ω a := by
    funext r ω a
    unfold s81q_stepFun
    rw [Finset.sum_mul]
    refine Finset.sum_congr rfl fun p _ => ?_
    by_cases h : r ∈ Set.Ioc (s81q_grid τ n p) (s81q_grid τ n (p + 1)) <;> simp [h]
  have e2 : (fun t ω => ∑ p ∈ Finset.range (2 ^ n), (fun _ : Ω => f (s81q_grid τ n p)) ω *
      (I (min t (s81q_grid τ n (p + 1))) ω - I (min t (s81q_grid τ n p)) ω)) =
      fun t ω => s81q_RS I f τ n t ω := rfl
  rw [e1] at h1 h2
  rw [e2] at h2
  exact ⟨h1, h2⟩

theorem s81q_exists_eta {K ε' : ℝ≥0∞} (hK : K ≠ ⊤) (hε : 0 < ε') :
    ∃ η : ℝ, 0 < η ∧ ENNReal.ofReal (η ^ 2) * K ≤ ε' := by
  rcases eq_or_ne ε' ⊤ with h | h
  · exact ⟨1, one_pos, by simp [h]⟩
  · have he : 0 < ε'.toReal := ENNReal.toReal_pos hε.ne' h
    have hk : 0 ≤ K.toReal := ENNReal.toReal_nonneg
    refine ⟨Real.sqrt (ε'.toReal / (K.toReal + 1)), Real.sqrt_pos.2 (by positivity), ?_⟩
    rw [Real.sq_sqrt (by positivity)]
    calc ENNReal.ofReal (ε'.toReal / (K.toReal + 1)) * K
        = ENNReal.ofReal (ε'.toReal / (K.toReal + 1)) * ENNReal.ofReal K.toReal := by
          rw [ENNReal.ofReal_toReal hK]
      _ = ENNReal.ofReal (ε'.toReal / (K.toReal + 1) * K.toReal) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ ≤ ENNReal.ofReal ε'.toReal := by
          refine ENNReal.ofReal_le_ofReal ?_
          rw [div_mul_eq_mul_div, div_le_iff₀ (by positivity)]
          nlinarith
      _ = ε' := ENNReal.ofReal_toReal h

theorem s81q_rs_tendsto (hW : IsCylindricalBrownian P ℱ 𝔚) (hξ : IsCtbl P ℱ ξ)
    (hI : IsItoC P ℱ 𝔚 ξ I) {f : ℝ → ℝ} (hf : Continuous f) (hfb : ∃ C, ∀ r, |f r| ≤ C)
    {J : ℝ → Ω → ℝ} (hJ : IsItoC P ℱ 𝔚 (fun r ω a => f r * ξ r ω a) J) {τ : ℝ} (hτ : 0 ≤ τ) :
    Tendsto (fun n : ℕ => ∫⁻ ω, ‖s81q_RS I f τ n τ ω - J τ ω‖ₑ ^ 2 ∂P) atTop (𝓝 0) := by
  classical
  obtain ⟨C, hC⟩ := hfb
  have hfξ : IsCtbl P ℱ (fun r ω a => f r * ξ r ω a) :=
    hξ.mul_bdd (w := fun r (_ : Ω) => f r) (pc_isProgressive_det hf.measurable) (C := C)
      (fun r _ => hC r)
  rcases hτ.eq_or_lt with h0 | hpos
  · -- `τ = 0`
    subst h0
    have : ∀ n ω, s81q_RS I f 0 n 0 ω - J 0 ω = 0 := by
      intro n ω
      unfold s81q_RS
      rw [hJ.zero 0 le_rfl ω]
      simp [s81q_grid]
    simp only [this, enorm_zero]
    simp
  have hK : ∑' a, cT P ξ a τ ≠ ⊤ := hξ.sq τ
  refine ENNReal.tendsto_nhds_zero.2 fun ε' hε' => ?_
  obtain ⟨η, hη, hηε⟩ := s81q_exists_eta hK hε'
  obtain ⟨N0, hN0⟩ := s81q_stepFun_close hf hpos hη
  refine eventually_atTop.2 ⟨N0, fun n hn => ?_⟩
  obtain ⟨hSc, hSi⟩ := s81q_step_itoC hW hξ hI f hτ n
  have hdc : IsCtbl P ℱ (fun r ω a => f r * ξ r ω a - s81q_stepFun f τ n r * ξ r ω a) := by
    have h2 := hSc.mul_bdd (w := fun _ (_ : Ω) => (-1 : ℝ)) (pc_isProgressive_det measurable_const)
      (C := 1) (fun _ _ => by simp)
    have h3 := hfξ.add h2
    have e : (fun r ω a => f r * ξ r ω a - s81q_stepFun f τ n r * ξ r ω a) =
        fun r ω a => f r * ξ r ω a +
          (fun _ (_ : Ω) => (-1 : ℝ)) r ω * (s81q_stepFun f τ n r * ξ r ω a) := by
      funext r ω a; ring
    rw [e]; exact h3
  have hdi := IsItoC.sub hW hfξ hSc hJ hSi
  have hsq := IsItoC.lintegral_sq_le hdc hW hdi hτ
  have hflip : ∫⁻ ω, ‖s81q_RS I f τ n τ ω - J τ ω‖ₑ ^ 2 ∂P =
      ∫⁻ ω, ‖J τ ω - s81q_RS I f τ n τ ω‖ₑ ^ 2 ∂P := by
    refine lintegral_congr fun ω => ?_
    rw [← enorm_neg, neg_sub]
  rw [hflip]
  refine hsq.trans (le_trans ?_ hηε)
  rw [← ENNReal.tsum_mul_left]
  refine ENNReal.tsum_le_tsum fun a => ?_
  unfold cT
  rw [← lintegral_const_mul' _ _ (by simp)]
  refine lintegral_mono fun ω => ?_
  rw [setLIntegral_congr (Ioc_ae_eq_Icc (a := (0 : ℝ)) (b := τ)).symm,
    ← lintegral_const_mul _ (measurable_slice_enorm_sq hξ.prog a ω)]
  refine (setLIntegral_mono' measurableSet_Ioc fun s hs => ?_).trans
    (lintegral_mono_set Ioc_subset_Icc_self)
  have hd := hN0 n hn s hs
  show ‖f s * ξ s ω a - s81q_stepFun f τ n s * ξ s ω a‖ₑ ^ 2 ≤ _
  rw [← sub_mul, enorm_mul, mul_pow]
  gcongr
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _)]
  exact ENNReal.ofReal_le_ofReal (by nlinarith [abs_nonneg (f s - s81q_stepFun f τ n s)])

theorem s81q_RS_aemeasurable (hI : IsItoC P ℱ 𝔚 ξ I) (f : ℝ → ℝ) (τ : ℝ) (n : ℕ) (t : ℝ) :
    AEMeasurable (s81q_RS I f τ n t) P := by
  unfold s81q_RS
  refine Finset.aemeasurable_fun_sum _ fun p _ => ?_
  exact ((hI.aemeasurable _).sub (hI.aemeasurable _)).const_mul _

/-- Two representations of the same process `I` give almost surely equal weighted integrals. -/
theorem s81q_weighted_eq {A₂ : Type*} [Countable A₂] {𝔚₂ : ℝ≥0 → Ω → A₂ → ℝ} {ξ₂ : ℝ → Ω → A₂ → ℝ}
    {I₂ : ℝ → Ω → ℝ} (hW : IsCylindricalBrownian P ℱ 𝔚) (hξ : IsCtbl P ℱ ξ)
    (hI : IsItoC P ℱ 𝔚 ξ I) (hW₂ : IsCylindricalBrownian P ℱ 𝔚₂) (hξ₂ : IsCtbl P ℱ ξ₂)
    (hI₂ : IsItoC P ℱ 𝔚₂ ξ₂ I₂) {τ : ℝ} (hτ : 0 ≤ τ) (hII : ∀ t ∈ Set.Icc 0 τ, I t =ᵐ[P] I₂ t)
    {f : ℝ → ℝ} (hf : Continuous f)
    (hfb : ∃ C, ∀ r, |f r| ≤ C) {J J₂ : ℝ → Ω → ℝ}
    (hJ : IsItoC P ℱ 𝔚 (fun r ω a => f r * ξ r ω a) J)
    (hJ₂ : IsItoC P ℱ 𝔚₂ (fun r ω a => f r * ξ₂ r ω a) J₂) :
    J τ =ᵐ[P] J₂ τ := by
  have h1 := s81q_rs_tendsto hW hξ hI hf hfb hJ hτ
  have h2 := s81q_rs_tendsto hW₂ hξ₂ hI₂ hf hfb hJ₂ hτ
  have hae : ∀ n, s81q_RS I f τ n τ =ᵐ[P] s81q_RS I₂ f τ n τ := by
    intro n
    unfold s81q_RS
    have : ∀ p ∈ Finset.range (2 ^ n), ∀ᵐ ω ∂P,
        I (min τ (s81q_grid τ n (p + 1))) ω = I₂ (min τ (s81q_grid τ n (p + 1))) ω ∧
        I (min τ (s81q_grid τ n p)) ω = I₂ (min τ (s81q_grid τ n p)) ω := fun p _ => by
      filter_upwards [hII (min τ (s81q_grid τ n (p + 1)))
          ⟨le_min hτ (s81q_grid_nonneg hτ n _), min_le_left _ _⟩,
        hII (min τ (s81q_grid τ n p)) ⟨le_min hτ (s81q_grid_nonneg hτ n _), min_le_left _ _⟩]
        with ω a b using ⟨a, b⟩
    have hall := (ae_ball_iff (Finset.range (2 ^ n)).countable_toSet).2 this
    filter_upwards [hall] with ω hω
    exact Finset.sum_congr rfl fun p hp => by rw [(hω p hp).1, (hω p hp).2]
  refine s81q_ae_eq_of_L2 (a := fun n => s81q_RS I f τ n τ) (hJ.aemeasurable τ) (hJ₂.aemeasurable τ)
    (fun n => s81q_RS_aemeasurable hI f τ n τ) h1 ?_
  refine h2.congr fun n => ?_
  refine lintegral_congr_ae ?_
  filter_upwards [hae n] with ω hω
  rw [hω]

/-- Integrals up to time `h` depend only on the integrand on `(0,h]`. -/
theorem s81q_agree_at {ξ' : ℝ → Ω → A → ℝ} {I' : ℝ → Ω → ℝ} (hW : IsCylindricalBrownian P ℱ 𝔚)
    (hξ : IsCtbl P ℱ ξ) (hξ' : IsCtbl P ℱ ξ') (hI : IsItoC P ℱ 𝔚 ξ I) (hI' : IsItoC P ℱ 𝔚 ξ' I')
    {h : ℝ} (hh : 0 ≤ h) (hagree : ∀ r ∈ Set.Ioc 0 h, ∀ ω a, ξ r ω a = ξ' r ω a) :
    I h =ᵐ[P] I' h := by
  have b1 := hI.block hW hξ (le_refl (0 : ℝ)) hh (c := fun _ => (1 : ℝ)) measurable_const (C := 1)
    (fun _ => by simp)
  have b2 := hI'.block hW hξ' (le_refl (0 : ℝ)) hh (c := fun _ => (1 : ℝ)) measurable_const (C := 1)
    (fun _ => by simp)
  have e : (fun r ω a => (fun _ : Ω => (1 : ℝ)) ω * (Set.Ioc (0 : ℝ) h).indicator (fun _ => ξ r ω a) r) =
      fun r ω a => (fun _ : Ω => (1 : ℝ)) ω * (Set.Ioc (0 : ℝ) h).indicator (fun _ => ξ' r ω a) r := by
    funext r ω a
    by_cases hr : r ∈ Set.Ioc (0 : ℝ) h
    · simp [hr, hagree r hr ω a]
    · simp [hr]
  rw [e] at b1
  filter_upwards [IsItoC.ae_eq_forall b1 b2] with ω hω
  have := hω h
  simp only [min_self, min_eq_right hh, one_mul] at this
  have h1 := hI.zero 0 le_rfl ω
  have h2 := hI'.zero 0 le_rfl ω
  rw [h1, h2] at this
  simpa using this

end Weighted

section Hilbert

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- The coordinates of an `IsHilbertItoIntegral` are countable-index Itô integrals. -/
theorem s81q_hilbert_isItoC {ℱ : Filtration ℝ mΩ} {κ : Type*} [Countable κ]
    {W : ℝ≥0 → Ω → κ → ℝ} {Φ : ℝ → Ω → κ → H} {M : ℝ → Ω → H}
    (hM : IsHilbertItoIntegral P ℱ W Φ M) (x : H) :
    IsItoC P ℱ W (fun r ω k => inner ℝ (Φ r ω k) x) (fun τ ω => inner ℝ (M τ ω) x) := by
  refine ⟨fun ω => (hM.cont ω).inner continuous_const, fun t => ?_, fun t ht ω => ?_,
    fun t ht => hM.approx t ht x⟩
  · exact (hM.adapted t).inner measurable_const
  · simp [hM.zero t ht ω]

end Hilbert

section Transfer

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω} [IsProbabilityMeasure P]
  {ℱ : Filtration ℝ mΩ} {Ω' : Type*} {mΩ' : MeasurableSpace Ω'} {P' : Measure Ω'}
  {ℱ' : Filtration ℝ mΩ'} {A : Type} [Countable A] {𝔚 : ℝ≥0 → Ω → A → ℝ} {ξ : ℝ → Ω → A → ℝ}
  {I : ℝ → Ω → ℝ} {π : Ω' → Ω}

/-- Transfer of a countable-index Itô integral along a measure preserving enlargement for which the pulled-back
Brownian motion is still Brownian. -/
theorem s81q_isItoC_comp (hπ : ∀ t, Measurable[ℱ' t, ℱ t] π) (hπp : MeasurePreserving π P' P)
    [IsProbabilityMeasure P'] (hW : IsCylindricalBrownian P ℱ 𝔚)
    (hW' : IsCylindricalBrownian P' ℱ' (fun t ω' a => 𝔚 t (π ω') a)) (hξ : IsCtbl P ℱ ξ)
    (hI : IsItoC P ℱ 𝔚 ξ I) :
    IsCtbl P' ℱ' (fun r ω' a => ξ r (π ω') a) ∧
      IsItoC P' ℱ' (fun t ω' a => 𝔚 t (π ω') a) (fun r ω' a => ξ r (π ω') a)
        (fun t ω' => I t (π ω')) := by
  refine ⟨pc_isCtbl_comp hπ hπp hξ, fun ω' => (hI.cont (π ω')), fun t => (hI.adapted t).comp (hπ t),
    fun t ht ω' => hI.zero t ht (π ω'), fun t ht => ?_⟩
  have h1 := hI.approx t ht
  refine h1.congr fun F => ?_
  have hae := itoIntegral_comp_π hπ hπp (hW F) (hW' F) (hξ.progressiveL2 F)
  have hmeas : Measurable fun ω => ‖ItoF P ℱ 𝔚 ξ F t ω - I t ω‖ₑ ^ 2 :=
    ((((adapted_itoIntegral P ℱ _ _ t).mono (ℱ.le t) le_rfl).sub
      ((hI.adapted t).mono (ℱ.le t) le_rfl)).enorm).pow_const 2
  rw [← hπp.lintegral_comp hmeas]
  refine lintegral_congr_ae ?_
  filter_upwards [hae] with ω' hω'
  have : ItoF P' ℱ' (fun t ω' a => 𝔚 t (π ω') a) (fun r ω' a => ξ r (π ω') a) F t ω' =
      ItoF P ℱ 𝔚 ξ F t (π ω') := hω' t
  rw [this]

end Transfer

end HRS.Whole.S81Q
