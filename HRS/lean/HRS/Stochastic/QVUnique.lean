import HRS.Prob.CLT

/-!
# Uniqueness of the quadratic variation (SI-01p)

`quadraticVariation_unique`: two quadratic variations `A, A'` of the same continuous `L²`
martingale `M` agree a.s. on `[0,t]`.

Route (shorter than localisation by stopping times): `D = A - A'` is a martingale of a.s.
continuous paths with variation on `[0,s]` bounded by the integrable `V_s = A_s + A'_s`.  For the
convex function `Φ(x) = √(1+x²) - 1` (with bounded Lipschitz derivative `Φ'`), the telescoping
sum along the partition `t_i = i s / N` and the martingale property give
`E Φ(D_s) = E Σ_i [Φ(D_{t_{i+1}}) - Φ(D_{t_i}) - Φ'(D_{t_i}) ΔD_i] ≤ E Σ_i (ΔD_i)²`, and
the right-hand side tends to `0` by dominated convergence (bound `2 V_s`, pointwise uniform
continuity of the paths).  Hence `Φ(D_s) = 0`, i.e. `D_s = 0` a.s., for every `s ∈ [0,t]`; the
statement follows from path continuity on the rationals.  No stopping times, localisation or
augmentation of the filtration is needed.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS

/-- Convex test function `√(1+x²) − 1`. -/
def qvPhi (x : ℝ) : ℝ := Real.sqrt (1 + x ^ 2) - 1

/-- its derivative. -/
def qvPhi' (x : ℝ) : ℝ := x / Real.sqrt (1 + x ^ 2)

lemma qv_one_le_sqrt (x : ℝ) : (1:ℝ) ≤ Real.sqrt (1 + x ^ 2) := by
  have := Real.sqrt_le_sqrt (show (1:ℝ) ≤ 1 + x ^ 2 by nlinarith [sq_nonneg x])
  simpa using this

lemma qv_abs_le_sqrt (x : ℝ) : |x| ≤ Real.sqrt (1 + x ^ 2) := by
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])

lemma qvPhi_nonneg (x : ℝ) : 0 ≤ qvPhi x := by
  unfold qvPhi
  linarith [qv_one_le_sqrt x]

lemma qvPhi_eq_zero {x : ℝ} (h : qvPhi x = 0) : x = 0 := by
  unfold qvPhi at h
  have h1 : Real.sqrt (1 + x ^ 2) = 1 := by linarith
  have h2 : (1 + x ^ 2) = 1 := by
    have := Real.sq_sqrt (show (0:ℝ) ≤ 1 + x ^ 2 by positivity)
    rw [h1] at this; linarith
  nlinarith [sq_nonneg x]

lemma qvPhi_le_abs (x : ℝ) : qvPhi x ≤ |x| := by
  unfold qvPhi
  have h0 : (0:ℝ) ≤ 1 + x ^ 2 := by positivity
  have : Real.sqrt (1 + x ^ 2) ≤ 1 + |x| := by
    apply Real.sqrt_le_iff.mpr
    constructor
    · positivity
    · nlinarith [sq_abs x, abs_nonneg x]
  linarith

lemma qvPhi'_abs_le (x : ℝ) : |qvPhi' x| ≤ 1 := by
  unfold qvPhi'
  have hs : (0:ℝ) < Real.sqrt (1 + x ^ 2) := Real.sqrt_pos.mpr (by positivity)
  rw [abs_div, abs_of_pos hs, div_le_one hs]
  rw [← Real.sqrt_sq_eq_abs]
  exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])

lemma continuous_qvPhi : Continuous qvPhi := by
  unfold qvPhi; fun_prop

lemma continuous_qvPhi' : Continuous qvPhi' := by
  unfold qvPhi'
  refine Continuous.div continuous_id (by fun_prop) fun x => ?_
  exact (Real.sqrt_pos.mpr (by positivity)).ne'

lemma qvPhi_remainder (x y : ℝ) :
    |qvPhi y - qvPhi x - qvPhi' x * (y - x)| ≤ 2 * |y - x| ∧
    |qvPhi y - qvPhi x - qvPhi' x * (y - x)| ≤ (y - x) ^ 2 := by
  set a := Real.sqrt (1 + x ^ 2) with ha_def
  set b := Real.sqrt (1 + y ^ 2) with hb_def
  have ha2 : a ^ 2 = 1 + x ^ 2 := Real.sq_sqrt (by positivity)
  have hb2 : b ^ 2 = 1 + y ^ 2 := Real.sq_sqrt (by positivity)
  have ha1 : 1 ≤ a := qv_one_le_sqrt x
  have hb1 : 1 ≤ b := qv_one_le_sqrt y
  have ha0 : 0 < a := by linarith
  have hR : qvPhi y - qvPhi x - qvPhi' x * (y - x) = (a * b - 1 - x * y) / a := by
    unfold qvPhi qvPhi'
    rw [← ha_def, ← hb_def]
    field_simp
    nlinarith [ha2]
  -- ab ≥ 1 + |xy|
  have hab : 1 + |x * y| ≤ a * b := by
    have h0 : 0 ≤ a * b := by positivity
    by_contra hcon
    push Not at hcon
    have h1 : (a * b) ^ 2 < (1 + |x * y|) ^ 2 := by
      exact pow_lt_pow_left₀ hcon h0 (by norm_num)
    have h2 : (a * b) ^ 2 = (1 + x ^ 2) * (1 + y ^ 2) := by rw [mul_pow, ha2, hb2]
    nlinarith [sq_abs (x * y), abs_nonneg (x * y), sq_nonneg (x - y), abs_nonneg x, abs_nonneg y,
      sq_abs x, sq_abs y, abs_mul x y, sq_nonneg (|x| - |y|)]
  have hxy : -|x * y| ≤ x * y := neg_abs_le _
  have hden : 2 ≤ a * b + 1 + x * y := by linarith
  have hprod : (a * b - 1 - x * y) * (a * b + 1 + x * y) = (y - x) ^ 2 := by
    have : (a * b) ^ 2 = (1 + x ^ 2) * (1 + y ^ 2) := by rw [mul_pow, ha2, hb2]
    nlinarith [this]
  have hnum_nonneg : 0 ≤ a * b - 1 - x * y := by
    by_contra hcon
    push Not at hcon
    have : (a * b - 1 - x * y) * (a * b + 1 + x * y) < 0 :=
      mul_neg_of_neg_of_pos hcon (by linarith)
    nlinarith [sq_nonneg (y - x)]
  have hRnn : 0 ≤ (a * b - 1 - x * y) / a := div_nonneg hnum_nonneg ha0.le
  rw [hR, abs_of_nonneg hRnn]
  constructor
  · -- ≤ 2|y-x|
    have h1 : a * b - 1 - x * y ≤ a * (2 * |y - x|) := by
      have hbound : b - a ≤ |y - x| := by
        have : (b - a) * (b + a) = (y - x) * (y + x) := by nlinarith [ha2, hb2]
        have hab' : |y + x| ≤ a + b := by
          have h1 : |y| ≤ b := by
            rw [← Real.sqrt_sq_eq_abs, hb_def]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg y])
          have h2 : |x| ≤ a := by
            rw [← Real.sqrt_sq_eq_abs, ha_def]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
          linarith [abs_add_le y x]
        by_contra hcon
        push Not at hcon
        have hlt : |y - x| * (b + a) < (b - a) * (b + a) := mul_lt_mul_of_pos_right hcon (by linarith)
        have h3 : |(b - a) * (b + a)| = |y - x| * |y + x| := by rw [this, abs_mul]
        have h4 : (b - a) * (b + a) ≤ |y - x| * (a + b) := by
          calc (b - a) * (b + a) ≤ |(b - a) * (b + a)| := le_abs_self _
            _ = |y - x| * |y + x| := h3
            _ ≤ |y - x| * (a + b) := mul_le_mul_of_nonneg_left hab' (abs_nonneg _)
        nlinarith
      have hx : |x| ≤ a := by
        rw [← Real.sqrt_sq_eq_abs, ha_def]; exact Real.sqrt_le_sqrt (by nlinarith [sq_nonneg x])
      -- ab - 1 - xy = a (b - a) - x (y - x) + (a² - 1 - x²) = a(b-a) - x(y-x)
      have : a * b - 1 - x * y = a * (b - a) - x * (y - x) := by nlinarith [ha2]
      rw [this]
      have h5 : x * (y - x) ≥ -(a * |y - x|) := by
        have : |x * (y - x)| ≤ a * |y - x| := by
          rw [abs_mul]; exact mul_le_mul_of_nonneg_right hx (abs_nonneg _)
        linarith [neg_abs_le (x * (y - x))]
      nlinarith [mul_le_mul_of_nonneg_left hbound ha0.le]
    rw [div_le_iff₀ ha0]; linarith
  · rw [div_le_iff₀ ha0]
    have : (y - x) ^ 2 ≤ a * ((y - x) ^ 2) := by nlinarith [sq_nonneg (y - x)]
    have hh : (a * b - 1 - x * y) * 2 ≤ (y - x) ^ 2 := by
      nlinarith [mul_le_mul_of_nonneg_left hden hnum_nonneg]
    nlinarith [sq_nonneg (y - x)]


section

variable {Ω : Type*} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]

/-- Martingale increments are orthogonal to bounded `ℱ_i`-measurable multipliers. -/
lemma martingale_mul_sub_integral_eq_zero {ℱ : Filtration ℝ mΩ} {D : ℝ → Ω → ℝ}
    (hD : Martingale D ℱ P) {i j : ℝ} (hij : i ≤ j) {g : Ω → ℝ}
    (hg : StronglyMeasurable[ℱ i] g) (hgb : ∀ ω, |g ω| ≤ 1) :
    ∫ ω, g ω * (D j ω - D i ω) ∂P = 0 := by
  have hDj : Integrable (D j) P := hD.integrable j
  have hDi : Integrable (D i) P := hD.integrable i
  have hsub : Integrable (D j - D i) P := hDj.sub hDi
  have hgm : AEStronglyMeasurable g P := (hg.mono (ℱ.le i)).aestronglyMeasurable
  have hprod : Integrable (g * (D j - D i)) P :=
    hsub.bdd_mul hgm (Filter.Eventually.of_forall fun ω => by simpa using hgb ω)
  have hce : P[g * (D j - D i) | ℱ i] =ᵐ[P] g * P[D j - D i | ℱ i] :=
    condExp_mul_of_stronglyMeasurable_left hg hprod hsub
  have hz : P[D j - D i | ℱ i] =ᵐ[P] 0 := by
    have h1 : P[D j - D i | ℱ i] =ᵐ[P] P[D j | ℱ i] - P[D i | ℱ i] :=
      condExp_sub hDj hDi (ℱ i)
    have h2 : P[D i | ℱ i] = D i :=
      condExp_of_stronglyMeasurable (ℱ.le i) (hD.1 i) hDi
    filter_upwards [h1, hD.condExp_ae_eq hij] with ω h1ω h2ω
    rw [h1ω, Pi.sub_apply, h2ω, h2]; simp
  have : ∫ ω, (g * (D j - D i)) ω ∂P = 0 := by
    rw [← integral_condExp (ℱ.le i)]
    have : P[g * (D j - D i) | ℱ i] =ᵐ[P] 0 := by
      filter_upwards [hce, hz] with ω h1 h2
      rw [h1, Pi.mul_apply, h2]; simp
    rw [integral_congr_ae this]; simp
  simpa using this

/-- Partition points `i s / N`. -/
def qvT (s : ℝ) (N i : ℕ) : ℝ := (i : ℝ) * s / (N : ℝ)

lemma qvT_mem {s : ℝ} (hs : 0 ≤ s) {N i : ℕ} (hN : 0 < N) (hi : i ≤ N) :
    qvT s N i ∈ Set.Icc (0:ℝ) s := by
  have hN' : (0:ℝ) < N := by exact_mod_cast hN
  have hi' : (i:ℝ) ≤ N := by exact_mod_cast hi
  unfold qvT
  constructor
  · positivity
  · rw [div_le_iff₀ hN']
    exact mul_le_mul_of_nonneg_right hi' hs |>.trans (le_of_eq (by ring))

lemma qvT_succ_sub (s : ℝ) (N i : ℕ) : qvT s N (i + 1) - qvT s N i = s / N := by
  unfold qvT; push_cast; ring

/-- Abstract core: a martingale `D` with `D_0 = 0` a.s., a.s. continuous on `[0,s]`, whose
variation along every uniform partition of `[0,s]` is a.s. bounded by an integrable `V`,
vanishes at time `s` a.s. -/
lemma martingale_eq_zero_of_variation {ℱ : Filtration ℝ mΩ} {D : ℝ → Ω → ℝ}
    (hD : Martingale D ℱ P) {s : ℝ} (hs : 0 ≤ s) {V : Ω → ℝ} (hV : Integrable V P)
    (h0 : ∀ᵐ ω ∂P, D 0 ω = 0)
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun τ => D τ ω) (Set.Icc 0 s))
    (hvar : ∀ᵐ ω ∂P, ∀ N : ℕ,
      ∑ i ∈ Finset.range (N + 1), |D (qvT s (N + 1) (i + 1)) ω - D (qvT s (N + 1) i) ω| ≤ V ω) :
    D s =ᵐ[P] 0 := by
  -- measurability and integrability of the building blocks
  have hDm : ∀ τ, Measurable (D τ) := fun τ =>
    ((hD.1 τ).mono (ℱ.le τ)).measurable
  have hDi : ∀ τ, Integrable (D τ) P := hD.integrable
  have hPhiint : ∀ τ, Integrable (fun ω => qvPhi (D τ ω)) P := by
    intro τ
    refine (hDi τ).norm.mono' ?_ (Filter.Eventually.of_forall fun ω => ?_)
    · exact (continuous_qvPhi.measurable.comp (hDm τ)).aestronglyMeasurable
    · rw [Real.norm_of_nonneg (qvPhi_nonneg _)]
      simpa using qvPhi_le_abs (D τ ω)
  set R : ℝ → ℝ → ℝ := fun x y => qvPhi y - qvPhi x - qvPhi' x * (y - x) with hR_def
  set G : ℕ → Ω → ℝ := fun N ω =>
    ∑ i ∈ Finset.range (N + 1), R (D (qvT s (N + 1) i) ω) (D (qvT s (N + 1) (i + 1)) ω) with hG
  -- Claim 1: `∫ G N = ∫ Φ (D s)`.
  have hmul_int : ∀ (N i : ℕ), Integrable (fun ω => qvPhi' (D (qvT s (N + 1) i) ω) *
        (D (qvT s (N + 1) (i + 1)) ω - D (qvT s (N + 1) i) ω)) P := by
    intro N i
    refine ((hDi _).sub (hDi _)).bdd_mul (c := 1)
      ((continuous_qvPhi'.measurable.comp (hDm _)).aestronglyMeasurable)
      (Filter.Eventually.of_forall fun ω => ?_)
    simpa using qvPhi'_abs_le _
  have hterm_int : ∀ (N i : ℕ), Integrable (fun ω =>
      R (D (qvT s (N + 1) i) ω) (D (qvT s (N + 1) (i + 1)) ω)) P := fun N i =>
    ((hPhiint _).sub (hPhiint _)).sub (hmul_int N i)
  have hint_eq : ∀ N : ℕ, ∫ ω, G N ω ∂P = ∫ ω, qvPhi (D s ω) ∂P := by
    intro N
    have hs' : qvT s (N + 1) (N + 1) = s := by
      unfold qvT
      have : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
      field_simp
    have hz : qvT s (N + 1) 0 = 0 := by simp [qvT]
    have hortho : ∀ i : ℕ,
        ∫ ω, qvPhi' (D (qvT s (N + 1) i) ω) *
          (D (qvT s (N + 1) (i + 1)) ω - D (qvT s (N + 1) i) ω) ∂P = 0 := by
      intro i
      refine martingale_mul_sub_integral_eq_zero P hD ?_ ?_ ?_
      · unfold qvT
        have : (0:ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
        rw [div_le_div_iff_of_pos_right this]
        exact mul_le_mul_of_nonneg_right (by simp) hs
      · exact continuous_qvPhi'.comp_stronglyMeasurable (hD.1 _)
      · intro ω; simpa using qvPhi'_abs_le _
    have hsplit : ∀ i : ℕ, ∫ ω, R (D (qvT s (N + 1) i) ω) (D (qvT s (N + 1) (i + 1)) ω) ∂P =
        ∫ ω, qvPhi (D (qvT s (N + 1) (i + 1)) ω) ∂P -
          ∫ ω, qvPhi (D (qvT s (N + 1) i) ω) ∂P := by
      intro i
      have : (fun ω => R (D (qvT s (N + 1) i) ω) (D (qvT s (N + 1) (i + 1)) ω)) =
          fun ω => (qvPhi (D (qvT s (N + 1) (i + 1)) ω) - qvPhi (D (qvT s (N + 1) i) ω)) -
            qvPhi' (D (qvT s (N + 1) i) ω) *
              (D (qvT s (N + 1) (i + 1)) ω - D (qvT s (N + 1) i) ω) := by
        funext ω; simp only [hR_def]
      have h1 : Integrable (fun ω => qvPhi (D (qvT s (N + 1) (i + 1)) ω) -
          qvPhi (D (qvT s (N + 1) i) ω)) P := (hPhiint _).sub (hPhiint _)
      rw [this, integral_sub h1 (hmul_int N i), hortho i,
        integral_sub (hPhiint _) (hPhiint _)]
      ring
    have hD0 : ∫ ω, qvPhi (D 0 ω) ∂P = 0 := by
      have : (fun ω => qvPhi (D 0 ω)) =ᵐ[P] 0 := by
        filter_upwards [h0] with ω hω
        simp [hω, qvPhi]
      rw [integral_congr_ae this]; simp
    show ∫ ω, ∑ i ∈ Finset.range (N + 1),
      R (D (qvT s (N + 1) i) ω) (D (qvT s (N + 1) (i + 1)) ω) ∂P = _
    rw [integral_finsetSum _ (fun i _ => hterm_int N i)]
    simp_rw [hsplit]
    rw [Finset.sum_range_sub (fun i => ∫ ω, qvPhi (D (qvT s (N + 1) i) ω) ∂P) (N + 1), hs', hz,
      hD0]
    simp
  -- Claim 2: `∫ G N → 0`.
  have hR_bound : ∀ x y, |R x y| ≤ 2 * |y - x| ∧ |R x y| ≤ (y - x) ^ 2 := fun x y =>
    qvPhi_remainder x y
  have hG_meas : ∀ N, AEStronglyMeasurable (G N) P := fun N =>
    (integrable_finsetSum (Finset.range (N + 1)) (fun i _ => hterm_int N i)).aestronglyMeasurable
  have hbound : ∀ N, ∀ᵐ ω ∂P, ‖G N ω‖ ≤ 2 * V ω := by
    intro N
    filter_upwards [hvar] with ω hω
    rw [Real.norm_eq_abs]
    calc |G N ω| ≤ ∑ i ∈ Finset.range (N + 1),
          |R (D (qvT s (N + 1) i) ω) (D (qvT s (N + 1) (i + 1)) ω)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (N + 1),
          2 * |D (qvT s (N + 1) (i + 1)) ω - D (qvT s (N + 1) i) ω| :=
          Finset.sum_le_sum fun i _ => (hR_bound _ _).1
      _ = 2 * ∑ i ∈ Finset.range (N + 1),
          |D (qvT s (N + 1) (i + 1)) ω - D (qvT s (N + 1) i) ω| := by rw [Finset.mul_sum]
      _ ≤ 2 * V ω := by linarith [hω N]
  have hlim : ∀ᵐ ω ∂P, Tendsto (fun N => G N ω) atTop (𝓝 0) := by
    filter_upwards [hvar, hcont] with ω hω hc
    have hV0 : 0 ≤ V ω := le_trans (Finset.sum_nonneg fun i _ => abs_nonneg _) (hω 0)
    have huc := Metric.uniformContinuousOn_iff.mp
      (isCompact_Icc.uniformContinuousOn_of_continuous hc)
    rw [Metric.tendsto_atTop]
    intro ε hε
    have hη : 0 < ε / (V ω + 1) := by positivity
    obtain ⟨δ, hδ, hδ'⟩ := huc _ hη
    obtain ⟨N0, hN0⟩ := exists_nat_gt (s / δ)
    refine ⟨N0, fun N hN => ?_⟩
    have hNpos : (0:ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have hstep : s / ((N + 1 : ℕ) : ℝ) < δ := by
      rw [div_lt_iff₀ hNpos]
      have h1 : s / δ < ((N + 1 : ℕ) : ℝ) := by
        have : (N0 : ℝ) ≤ N := by exact_mod_cast hN
        push_cast; linarith
      rw [div_lt_iff₀ hδ] at h1
      linarith
    have hdelta : ∀ i ∈ Finset.range (N + 1),
        |D (qvT s (N + 1) (i + 1)) ω - D (qvT s (N + 1) i) ω| < ε / (V ω + 1) := by
      intro i hi
      have hi' : i + 1 ≤ N + 1 := by simpa [Finset.mem_range] using hi
      have := hδ' _ (qvT_mem hs (Nat.succ_pos N) hi') _
        (qvT_mem hs (Nat.succ_pos N) (Nat.le_of_succ_le hi'))
        (by
          rw [Real.dist_eq, qvT_succ_sub, abs_of_nonneg (by positivity)]
          exact hstep)
      simpa [Real.dist_eq] using this
    rw [Real.dist_eq, sub_zero]
    calc |G N ω| ≤ ∑ i ∈ Finset.range (N + 1),
          |R (D (qvT s (N + 1) i) ω) (D (qvT s (N + 1) (i + 1)) ω)| :=
          Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i ∈ Finset.range (N + 1),
          (ε / (V ω + 1)) * |D (qvT s (N + 1) (i + 1)) ω - D (qvT s (N + 1) i) ω| := by
          refine Finset.sum_le_sum fun i hi => ?_
          refine (hR_bound _ _).2.trans ?_
          rw [← sq_abs, sq]
          exact mul_le_mul_of_nonneg_right (hdelta i hi).le (abs_nonneg _)
      _ = (ε / (V ω + 1)) * ∑ i ∈ Finset.range (N + 1),
          |D (qvT s (N + 1) (i + 1)) ω - D (qvT s (N + 1) i) ω| := by rw [Finset.mul_sum]
      _ ≤ (ε / (V ω + 1)) * V ω := mul_le_mul_of_nonneg_left (hω N) hη.le
      _ < ε := by
          rw [div_mul_eq_mul_div, div_lt_iff₀ (by positivity)]
          nlinarith
  have hDC := tendsto_integral_of_dominated_convergence (μ := P) (F := G) (f := fun _ => (0:ℝ))
    (fun ω => 2 * V ω) hG_meas (hV.const_mul 2) hbound hlim
  simp only [integral_zero] at hDC
  have hzero : ∫ ω, qvPhi (D s ω) ∂P = 0 :=
    tendsto_nhds_unique (by simpa only [hint_eq] using tendsto_const_nhds) hDC
  have h2 := (integral_eq_zero_iff_of_nonneg (fun ω => qvPhi_nonneg (D s ω)) (hPhiint s)).mp hzero
  filter_upwards [h2] with ω hω
  exact qvPhi_eq_zero hω

/-- Uniqueness core: the difference of two quadratic variations vanishes at each time. -/
lemma qv_eq_ae (ℱ : Filtration ℝ mΩ) (t : ℝ) (M A A' : ℝ → Ω → ℝ)
    (hM : IsContSqMartingale P ℱ t M) (hA : IsQuadraticVariation P ℱ t M A)
    (hA' : IsQuadraticVariation P ℱ t M A') {s : ℝ} (hs : s ∈ Set.Icc 0 t) :
    A s =ᵐ[P] A' s := by
  have hD : Martingale (fun τ ω => A τ ω - A' τ ω) ℱ P := by
    have := hA'.compensator.sub hA.compensator
    convert this using 1
    funext τ ω
    simp
  have hAint : ∀ {B : ℝ → Ω → ℝ}, IsQuadraticVariation P ℱ t M B → Integrable (B s) P := by
    intro B hB
    have h1 : Integrable (fun ω => M s ω ^ 2) P := (hM.sq_int s hs).integrable_sq
    have h2 := hB.compensator.integrable s
    have := h1.sub h2
    refine this.congr (Filter.Eventually.of_forall fun ω => ?_)
    simp
  have hmem : ∀ {N i : ℕ}, i ≤ N + 1 → qvT s (N + 1) i ∈ Set.Icc (0:ℝ) t := by
    intro N i hi
    obtain ⟨h1, h2⟩ := qvT_mem hs.1 (Nat.succ_pos N) hi
    exact ⟨h1, h2.trans hs.2⟩
  have hD0 : ∀ᵐ ω ∂P, A 0 ω - A' 0 ω = 0 := by
    filter_upwards [hA.zero, hA'.zero] with ω h1 h2
    rw [h1, h2]; simp
  have hcont : ∀ᵐ ω ∂P, ContinuousOn (fun τ => A τ ω - A' τ ω) (Set.Icc 0 s) := by
    filter_upwards [hA.cont, hA'.cont] with ω h1 h2
    exact (h1.mono (Set.Icc_subset_Icc_right hs.2)).sub (h2.mono (Set.Icc_subset_Icc_right hs.2))
  have hvar : ∀ᵐ ω ∂P, ∀ N : ℕ, ∑ i ∈ Finset.range (N + 1),
      |(fun τ ω => A τ ω - A' τ ω) (qvT s (N + 1) (i + 1)) ω -
        (fun τ ω => A τ ω - A' τ ω) (qvT s (N + 1) i) ω| ≤ A s ω + A' s ω := by
    filter_upwards [hA.zero, hA'.zero, hA.mono, hA'.mono] with ω h0 h0' hm hm'
    intro N
    have hNpos : (0:ℝ) < ((N + 1 : ℕ) : ℝ) := by positivity
    have hle : ∀ i ∈ Finset.range (N + 1), qvT s (N + 1) i ≤ qvT s (N + 1) (i + 1) := by
      intro i hi
      have := qvT_succ_sub s (N + 1) i
      have h : 0 ≤ s / ((N + 1 : ℕ) : ℝ) := div_nonneg hs.1 hNpos.le
      linarith
    have hsum : ∀ i ∈ Finset.range (N + 1),
        |(A (qvT s (N + 1) (i + 1)) ω - A' (qvT s (N + 1) (i + 1)) ω) -
          (A (qvT s (N + 1) i) ω - A' (qvT s (N + 1) i) ω)| ≤
        (A (qvT s (N + 1) (i + 1)) ω + A' (qvT s (N + 1) (i + 1)) ω) -
          (A (qvT s (N + 1) i) ω + A' (qvT s (N + 1) i) ω) := by
      intro i hi
      have hi' : i ≤ N + 1 := by simp [Finset.mem_range] at hi; omega
      have h1 := hm (hmem hi') (hmem (by simp [Finset.mem_range] at hi; omega)) (hle i hi)
      have h2 := hm' (hmem hi') (hmem (by simp [Finset.mem_range] at hi; omega)) (hle i hi)
      rw [abs_le]; constructor <;> linarith
    calc _ ≤ ∑ i ∈ Finset.range (N + 1),
          ((A (qvT s (N + 1) (i + 1)) ω + A' (qvT s (N + 1) (i + 1)) ω) -
          (A (qvT s (N + 1) i) ω + A' (qvT s (N + 1) i) ω)) :=
          Finset.sum_le_sum hsum
      _ = (A (qvT s (N + 1) (N + 1)) ω + A' (qvT s (N + 1) (N + 1)) ω) -
          (A (qvT s (N + 1) 0) ω + A' (qvT s (N + 1) 0) ω) :=
          Finset.sum_range_sub (fun i => A (qvT s (N + 1) i) ω + A' (qvT s (N + 1) i) ω) (N + 1)
      _ = A s ω + A' s ω := by
          have hs' : qvT s (N + 1) (N + 1) = s := by
            unfold qvT
            have : ((N + 1 : ℕ) : ℝ) ≠ 0 := by positivity
            field_simp
          have hz : qvT s (N + 1) 0 = 0 := by simp [qvT]
          rw [hs', hz, h0, h0']; ring
  have hmain := martingale_eq_zero_of_variation P hD hs.1 ((hAint hA).add (hAint hA')) hD0 hcont hvar
  filter_upwards [hmain] with ω hω
  simpa [sub_eq_zero] using hω

/-- Two quadratic variations of the same continuous `L²` martingale agree a.s. on `[0,t]`. -/
theorem quadraticVariation_unique (ℱ : Filtration ℝ mΩ) (t : ℝ) (M A A' : ℝ → Ω → ℝ)
    (hM : IsContSqMartingale P ℱ t M) (hA : IsQuadraticVariation P ℱ t M A)
    (hA' : IsQuadraticVariation P ℱ t M A') :
    ∀ᵐ ω ∂P, ∀ τ ∈ Set.Icc 0 t, A τ ω = A' τ ω := by
  -- rational times in `[0,t]`
  have hq : ∀ᵐ ω ∂P, ∀ q : ℚ, (q : ℝ) ∈ Set.Icc 0 t → A q ω = A' q ω := by
    rw [ae_all_iff]
    intro q
    by_cases hqt : (q : ℝ) ∈ Set.Icc 0 t
    · filter_upwards [qv_eq_ae P ℱ t M A A' hM hA hA' hqt] with ω hω
      exact fun _ => hω
    · exact Filter.Eventually.of_forall fun ω h => absurd h hqt
  filter_upwards [hq, hA.zero, hA'.zero, hA.cont, hA'.cont] with ω hqω h0 h0' hc hc'
  intro τ hτ
  by_cases ht : 0 < t
  · set S : Set ℝ := {x | x ∈ Set.Icc 0 t ∧ ∃ q : ℚ, x = q} with hS
    have hSsub : S ⊆ Set.Icc 0 t := fun x hx => hx.1
    have hSeq : Set.EqOn (fun τ => A τ ω) (fun τ => A' τ ω) S := by
      rintro x ⟨hx, q, rfl⟩
      exact hqω q hx
    have hIoo : Set.Ioo 0 t ⊆ closure S := by
      intro x hx
      rw [mem_closure_iff]
      intro o ho hxo
      obtain ⟨q, hq'⟩ := Rat.denseRange_cast.exists_mem_open (ho.inter isOpen_Ioo) ⟨x, hxo, hx⟩
      exact ⟨(q : ℝ), hq'.1, ⟨Set.Ioo_subset_Icc_self hq'.2, q, rfl⟩⟩
    have hcl : Set.Icc 0 t ⊆ closure S := by
      rw [← closure_Ioo ht.ne]
      exact closure_minimal hIoo isClosed_closure
    exact Set.EqOn.of_subset_closure hSeq hc hc' hSsub hcl hτ
  · have : τ = 0 := le_antisymm (hτ.2.trans (not_lt.mp ht)) hτ.1
    subst this
    rw [h0, h0']

end

end HRS
