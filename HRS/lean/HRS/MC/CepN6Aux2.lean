import HRS.Stochastic.Brownian
import HRS.Stochastic.Filtration
import Mathlib.Probability.Martingale.OptionalStopping

/-!
# Packet CEPN6 (aux 2): a conditional Kolmogorov (Doob) maximal inequality for a Brownian filtration

For `A ∈ ℱ a`: `η² · P(A ∩ {∃ u ∈ [a, a+d], |W^k_u - W^k_a| > η}) ≤ d · P(A)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepN6

open HRS

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} {P : Measure Ω}
variable {ι : Type*} [Fintype ι] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → ι → ℝ}

/-- Discrete-time filtration along monotone real times. -/
def n6_gfilt (ℱ : Filtration ℝ mΩ) (s : ℕ → ℝ) (hs : Monotone s) : Filtration ℕ mΩ where
  seq m := ℱ (s m)
  mono' _ _ h := ℱ.mono (hs h)
  le' m := ℱ.le _

/-- The increment of coordinate `k` from time `a` to time `t`. -/
def n6_D (W : ℝ≥0 → Ω → ι → ℝ) (k : ι) (a t : ℝ) (ω : Ω) : ℝ :=
  ofNNRealTime W t ω k - ofNNRealTime W a ω k

theorem n6_Zadapted (hW : IsBrownianFiltration P ℱ W) (k : ι) {a : ℝ} {A : Set Ω}
    (hA : MeasurableSet[ℱ a] A) {t : ℝ} (hat : a ≤ t) :
    Measurable[ℱ t] (A.indicator (n6_D W k a t)) := by
  have h1 : Measurable[ℱ t] (fun ω => ofNNRealTime W t ω k) :=
    (measurable_pi_apply k).comp (hW.adapted_ofNNRealTime_aux t)
  have h2 : Measurable[ℱ t] (fun ω => ofNNRealTime W a ω k) :=
    Measurable.mono ((measurable_pi_apply k).comp (hW.adapted_ofNNRealTime_aux a)) (ℱ.mono hat) le_rfl
  exact (h1.sub h2).indicator (ℱ.mono hat _ hA)

theorem n6_memLp_D [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) (k : ι) (a t : ℝ) :
    MemLp (n6_D W k a t) 2 P :=
  (hW.memLp_two_coord_real t k).sub (hW.memLp_two_coord_real a k)

theorem n6_submart [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) (k : ι) {a : ℝ}
    {A : Set Ω} (hA : MeasurableSet[ℱ a] A) {s : ℕ → ℝ} (hs : Monotone s) (has : ∀ m, a ≤ s m) :
    Submartingale (fun m ω => (A.indicator (n6_D W k a (s m)) ω) ^ 2) (n6_gfilt ℱ s hs) P := by
  have hmemZ : ∀ t, MemLp (A.indicator (n6_D W k a t)) 2 P := fun t =>
    (n6_memLp_D hW k a t).indicator (ℱ.le a _ hA)
  refine submartingale_nat ?_ ?_ ?_
  · intro m
    exact ((n6_Zadapted hW k hA (has m)).pow_const 2).stronglyMeasurable
  · intro m
    exact (hmemZ (s m)).integrable_sq
  · intro m
    have hle : ℱ (s m) ≤ mΩ := ℱ.le _
    set g : Ω → ℝ := A.indicator (n6_D W k a (s m)) with hg
    set Δ : Ω → ℝ := fun ω => ofNNRealTime W (s (m + 1)) ω k - ofNNRealTime W (s m) ω k with hΔ
    have hgm : StronglyMeasurable[ℱ (s m)] g := (n6_Zadapted hW k hA (has m)).stronglyMeasurable
    have hΔ2 : MemLp Δ 2 P :=
      (hW.memLp_two_coord_real (s (m + 1)) k).sub (hW.memLp_two_coord_real (s m) k)
    have hΔint : Integrable Δ P := hΔ2.integrable one_le_two
    have hgΔint : Integrable (fun ω => g ω * Δ ω) P := (hmemZ (s m)).integrable_mul hΔ2
    have hg2 : Integrable (fun ω => g ω ^ 2) P := (hmemZ (s m)).integrable_sq
    have hf1 : Integrable (fun ω => A.indicator (n6_D W k a (s (m + 1))) ω ^ 2) P :=
      (hmemZ _).integrable_sq
    have hlow : (fun ω => g ω ^ 2 + 2 * (g ω * Δ ω)) ≤ᵐ[P]
        fun ω => A.indicator (n6_D W k a (s (m + 1))) ω ^ 2 := by
      refine Filter.Eventually.of_forall fun ω => ?_
      by_cases hω : ω ∈ A
      · simp only [hg, Set.indicator_of_mem hω, n6_D, hΔ]
        nlinarith [sq_nonneg (ofNNRealTime W (s (m + 1)) ω k - ofNNRealTime W (s m) ω k)]
      · simp [hg, Set.indicator_of_notMem hω]
    have hmono := condExp_mono (m := ℱ (s m)) (hg2.add (hgΔint.const_mul 2)) hf1 hlow
    have hadd := condExp_add (m := ℱ (s m)) hg2 (hgΔint.const_mul 2)
    have hsm : P[fun ω => (2 : ℝ) * (g ω * Δ ω) | ℱ (s m)] =ᵐ[P] fun _ => (0 : ℝ) := by
      have h1 := condExp_smul (μ := P) (2 : ℝ) (fun ω => g ω * Δ ω) (ℱ (s m))
      have h2 := hW.condExp_mul_incr_real (hs (Nat.le_succ m)) k hgm hgΔint
      have e : (fun ω => (2 : ℝ) * (g ω * Δ ω)) = (2 : ℝ) • (fun ω => g ω * Δ ω) := by
        funext ω; simp
      rw [e]
      filter_upwards [h1, h2] with ω a' b'
      rw [a']
      show (2 : ℝ) * _ = 0
      have b'' : P[fun ω => g ω * Δ ω | ℱ (s m)] ω = 0 := b'
      rw [b'']; simp
    have hself : P[fun ω => g ω ^ 2 | ℱ (s m)] = fun ω => g ω ^ 2 :=
      condExp_of_stronglyMeasurable hle (hgm.pow 2) hg2
    filter_upwards [hmono, hadd, hsm] with ω a' b' c'
    rw [hself] at b'
    try simp only [Pi.add_apply] at b'
    show g ω ^ 2 ≤ P[fun ω => A.indicator (n6_D W k a (s (m + 1))) ω ^ 2 | ℱ (s m)] ω
    linarith [b', c']

theorem n6_integral_sq [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) (k : ι) {a : ℝ}
    (ha : 0 ≤ a) {A : Set Ω} (hA : MeasurableSet[ℱ a] A) {t : ℝ} (hat : a ≤ t) :
    ∫ ω, (A.indicator (n6_D W k a t) ω) ^ 2 ∂P = (t - a) * P.real A := by
  have hint : Integrable (fun ω => (n6_D W k a t ω) ^ 2) P := (n6_memLp_D hW k a t).integrable_sq
  have h1 : (fun ω => (A.indicator (n6_D W k a t) ω) ^ 2) =
      A.indicator (fun ω => (n6_D W k a t ω) ^ 2) := by
    funext ω; by_cases hω : ω ∈ A <;> simp [hω]
  rw [h1, integral_indicator (ℱ.le a _ hA), ← setIntegral_condExp (ℱ.le a) hint hA]
  have h2 : P[fun ω => (n6_D W k a t ω) ^ 2 | ℱ a] =ᵐ[P] fun _ => max t 0 - max a 0 :=
    hW.condExp_incr_sq_real hat k
  rw [setIntegral_congr_ae (ℱ.le a _ hA) (h2.mono fun ω hω _ => hω)]
  rw [setIntegral_const, max_eq_left (ha.trans hat), max_eq_left ha]
  simp [Measure.real, smul_eq_mul, mul_comm]

theorem n6_doob_seq [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) (k : ι) {a : ℝ}
    (ha : 0 ≤ a) {A : Set Ω} (hA : MeasurableSet[ℱ a] A) {s : ℕ → ℝ} (hs : Monotone s)
    (has : ∀ m, a ≤ s m) {η : ℝ} (hη : 0 < η) (n : ℕ) :
    ENNReal.ofReal (η ^ 2) * P (A ∩ {ω | ∃ m ≤ n, η < |n6_D W k a (s m) ω|}) ≤
      ENNReal.ofReal ((s n - a) * P.real A) := by
  have hsub := n6_submart hW k hA hs has
  have hnn : (0 : ℕ → Ω → ℝ) ≤ fun m ω => (A.indicator (n6_D W k a (s m)) ω) ^ 2 :=
    fun m ω => sq_nonneg _
  have key := maximal_ineq hsub hnn (ε := (η ^ 2).toNNReal) n
  have hε : (((η ^ 2).toNNReal : ℝ≥0) : ℝ) = η ^ 2 := Real.coe_toNNReal _ (sq_nonneg _)
  rw [hε] at key
  have hsubset : A ∩ {ω | ∃ m ≤ n, η < |n6_D W k a (s m) ω|} ⊆
      {ω | η ^ 2 ≤ (Finset.range (n + 1)).sup' Finset.nonempty_range_add_one
        fun m => (A.indicator (n6_D W k a (s m)) ω) ^ 2} := by
    rintro ω ⟨hωA, m, hm, hm2⟩
    have h1 : η ^ 2 ≤ (A.indicator (n6_D W k a (s m)) ω) ^ 2 := by
      rw [Set.indicator_of_mem hωA]
      have := abs_nonneg (n6_D W k a (s m) ω)
      nlinarith [sq_abs (n6_D W k a (s m) ω)]
    exact h1.trans (Finset.le_sup' (fun m => (A.indicator (n6_D W k a (s m)) ω) ^ 2)
      (Finset.mem_range.2 (Nat.lt_succ_of_le hm)))
  calc ENNReal.ofReal (η ^ 2) * P (A ∩ {ω | ∃ m ≤ n, η < |n6_D W k a (s m) ω|})
      ≤ ((η ^ 2).toNNReal : ℝ≥0∞) * P {ω | η ^ 2 ≤ (Finset.range (n + 1)).sup'
          Finset.nonempty_range_add_one fun m => (A.indicator (n6_D W k a (s m)) ω) ^ 2} :=
        mul_le_mul' le_rfl (measure_mono hsubset)
    _ ≤ _ := key
    _ ≤ ENNReal.ofReal (∫ ω, (A.indicator (n6_D W k a (s n)) ω) ^ 2 ∂P) := by
        apply ENNReal.ofReal_le_ofReal
        exact setIntegral_le_integral ((n6_memLp_D hW k a (s n)).indicator (ℱ.le a _ hA)).integrable_sq
          (Filter.Eventually.of_forall fun ω => sq_nonneg _)
    _ = _ := by rw [n6_integral_sq hW k ha hA (has n)]

/-- dyadic time grid on `[a, a + d]` -/
def n6_grid (a d : ℝ) (n m : ℕ) : ℝ := a + d * ((min m (2 ^ n) : ℕ) : ℝ) / 2 ^ n

theorem n6_grid_mono {a d : ℝ} (hd : 0 ≤ d) (n : ℕ) : Monotone (n6_grid a d n) := by
  intro m m' h
  unfold n6_grid
  have : ((min m (2 ^ n) : ℕ) : ℝ) ≤ ((min m' (2 ^ n) : ℕ) : ℝ) := by
    exact_mod_cast min_le_min_right _ h
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  gcongr

theorem n6_grid_ge {a d : ℝ} (hd : 0 ≤ d) (n m : ℕ) : a ≤ n6_grid a d n m := by
  unfold n6_grid
  have : (0 : ℝ) ≤ d * ((min m (2 ^ n) : ℕ) : ℝ) / 2 ^ n := by positivity
  linarith

theorem n6_grid_top (a d : ℝ) (n : ℕ) : n6_grid a d n (2 ^ n) = a + d := by
  unfold n6_grid
  rw [min_self]
  have h2 : (2 : ℝ) ^ n ≠ 0 := by positivity
  push_cast
  field_simp

theorem n6_grid_double (a d : ℝ) (n m : ℕ) (hm : m ≤ 2 ^ n) :
    n6_grid a d (n + 1) (2 * m) = n6_grid a d n m := by
  unfold n6_grid
  have h1 : min (2 * m) (2 ^ (n + 1)) = 2 * m := min_eq_left (by rw [pow_succ]; omega)
  have h2 : min m (2 ^ n) = m := min_eq_left hm
  rw [h1, h2]
  push_cast
  rw [pow_succ]
  field_simp

theorem n6_kolmogorov [IsProbabilityMeasure P] (hW : IsBrownianFiltration P ℱ W) (k : ι) {a d η : ℝ}
    (ha : 0 ≤ a) (hd : 0 ≤ d) (hη : 0 < η) {A : Set Ω} (hA : MeasurableSet[ℱ a] A) :
    ENNReal.ofReal (η ^ 2) *
        P (A ∩ {ω | ∃ u ∈ Set.Icc a (a + d), η < |n6_D W k a u ω|}) ≤
      ENNReal.ofReal (d * P.real A) := by
  set Ev : ℕ → Set Ω := fun n =>
    A ∩ {ω | ∃ m ≤ 2 ^ n, η < |n6_D W k a (n6_grid a d n m) ω|} with hEv
  have hdir : Monotone Ev := by
    refine monotone_nat_of_le_succ fun n => ?_
    rintro ω ⟨hωA, m, hm, hlt⟩
    refine ⟨hωA, 2 * m, by rw [pow_succ]; omega, ?_⟩
    rwa [n6_grid_double a d n m hm]
  have hsub : A ∩ {ω | ∃ u ∈ Set.Icc a (a + d), η < |n6_D W k a u ω|} ⊆ ⋃ n, Ev n := by
    rintro ω ⟨hωA, u, hu, hlt⟩
    have hcont : Continuous fun v : ℝ => |n6_D W k a v ω| := by
      unfold n6_D
      have hc : Continuous fun v : ℝ => ofNNRealTime W v ω k :=
        ((continuous_apply k).comp (hW.cont ω)).comp continuous_real_toNNReal
      exact (hc.sub continuous_const).abs
    obtain ⟨δ, hδ, hball⟩ := Metric.isOpen_iff.1 (isOpen_lt continuous_const hcont) u hlt
    rcases eq_or_lt_of_le hd with hd0 | hdpos
    · exfalso
      have hua : u = a := by
        have := hu.1; have := hu.2; rw [← hd0] at this; linarith
      subst hua
      have : |n6_D W k u u ω| = 0 := by simp [n6_D]
      linarith
    · obtain ⟨n, hn⟩ := exists_pow_lt_of_lt_one (show 0 < δ / d from by positivity)
        (show (1 / 2 : ℝ) < 1 by norm_num)
      refine Set.mem_iUnion.2 ⟨n, hωA, ?_⟩
      set m : ℕ := ⌊(u - a) * 2 ^ n / d⌋₊ with hm
      have h2n : (0 : ℝ) < 2 ^ n := by positivity
      have hx0 : 0 ≤ (u - a) * 2 ^ n / d := by
        have := hu.1; positivity
      have hx1 : (u - a) * 2 ^ n / d ≤ 2 ^ n := by
        rw [div_le_iff₀ hdpos]
        have := hu.2
        nlinarith
      have hmle : m ≤ 2 ^ n := by
        have : (m : ℝ) ≤ 2 ^ n := (Nat.floor_le hx0).trans hx1
        exact_mod_cast this
      refine ⟨m, hmle, ?_⟩
      have hg : n6_grid a d n m = a + d * m / 2 ^ n := by
        unfold n6_grid; rw [min_eq_left hmle]
      have hfl1 : (m : ℝ) ≤ (u - a) * 2 ^ n / d := Nat.floor_le hx0
      have hfl2 : (u - a) * 2 ^ n / d < m + 1 := Nat.lt_floor_add_one _
      have hdist : |n6_grid a d n m - u| < δ := by
        rw [hg]
        have hmd : (m : ℝ) * d ≤ (u - a) * 2 ^ n := (le_div_iff₀ hdpos).1 hfl1
        have hdm : (u - a) * 2 ^ n < (m + 1) * d := (div_lt_iff₀ hdpos).1 hfl2
        have hδd : d / 2 ^ n < δ := by
          have h3 : (1 / 2 : ℝ) ^ n * d < δ := (lt_div_iff₀ hdpos).1 hn
          rw [one_div_pow] at h3
          calc d / 2 ^ n = 1 / 2 ^ n * d := by ring
            _ < δ := h3
        have e1 : a + d * m / 2 ^ n ≤ u := by
          have : d * m / 2 ^ n ≤ u - a := by
            rw [div_le_iff₀ h2n]; nlinarith
          linarith
        have e2 : u - (a + d * m / 2 ^ n) < d / 2 ^ n := by
          have : (u - a) < (m + 1) * d / 2 ^ n := by rw [lt_div_iff₀ h2n]; exact hdm
          have h4 : (m + 1) * d / 2 ^ n = d * m / 2 ^ n + d / 2 ^ n := by ring
          linarith
        rw [abs_sub_comm, abs_of_nonneg (by linarith)]
        linarith
      have := hball (show n6_grid a d n m ∈ Metric.ball u δ from by rwa [Metric.mem_ball, Real.dist_eq])
      exact this
  have hle : ENNReal.ofReal (η ^ 2) * P (⋃ n, Ev n) ≤ ENNReal.ofReal (d * P.real A) := by
    rw [hdir.directed_le.measure_iUnion, ENNReal.mul_iSup]
    refine iSup_le fun n => ?_
    have := n6_doob_seq hW k ha hA (n6_grid_mono hd n) (n6_grid_ge hd n) hη (2 ^ n)
    rw [n6_grid_top] at this
    simpa using this
  exact le_trans (mul_le_mul' le_rfl (measure_mono hsub)) hle

end HRS.MC.CepN6
