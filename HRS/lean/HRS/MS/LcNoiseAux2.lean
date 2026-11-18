import HRS.MS.LcNoiseAux1

/-!
# LC-3, part 2: uniform moments of the running supremum of the noise (`lc_sup_moment`)

For a Brownian filtration `(P, ℱ, W)` on `Fin d`, `ν` continuous with `0 ≤ ν ≤ ν*`, and
`G = lcNoiseE W ν`, we prove for every `p : ℕ` and `T`:

  `ω ↦ (1 + ⨆ v ∈ Icc 0 T, ‖G v ω‖)^p` is integrable and `∫ (1 + sup_{[0,T]} ‖G‖)^p dP ≤ C`,

where `C = C(d, p, ν*, T)` does not depend on `Ω, P, ℱ, W, ν`.

Route.  (1) Doob's weak-type inequality (`maximal_ineq`) for the discrete submartingale
`‖X_{t_j}‖^m` (`m = p + 1`; conditional Jensen `Integrable.norm_condExp_rpow_le`) along the dyadic
grids, passage to the continuous supremum over `[0,S]` by continuity and continuity of measure from
below.  (2) Each coordinate of a Brownian motion has Gaussian marginals, so
`P(sup_{s ≤ S} |W^k_s| > l) ≤ E|W^k_S|^m / l^m`, and a union bound over coordinates gives the tail
`t^m P(sup ‖W‖ ≥ t) ≤ B`.  (3) A layer-cake estimate with the tail `min(1, B t^{-m})` bounds
`E (sup ‖W‖)^p`.  (4) Pathwise the time change only reduces the supremum:
`sup_{v ≤ T} ‖W_{τ(v)}‖ ≤ sup_{s ≤ 2ν*T} ‖W_s‖`, since `0 ≤ τ(v) ≤ 2ν* v`.

Only the Gaussian moments `E |Z|^m` (finite, a function of the variance alone) enter `C`; no
closed form is needed.  The measurability of the supremum is `lc_noise_sup_measurable`
(`LcNoiseAux1`), so the integral is never a junk value: integrability is part of the conclusion.
Helper lemmas carry the prefix `lc3_`.
-/

open MeasureTheory Set Filter Topology ProbabilityTheory
open scoped NNReal ENNReal
open HRS

noncomputable section

namespace HRS.MS.Lc

variable {d : ℕ} {Ω : Type*} {mΩ : MeasurableSpace Ω}

/-! ### Doob's weak-type inequality for a continuous martingale -/

section Doob

variable {μ : Measure Ω} [IsProbabilityMeasure μ] {ℱ : Filtration ℝ mΩ} {X : ℝ → Ω → ℝ}

/-- Weak-type inequality along a finite increasing list of times. -/
theorem lc3_weak_grid (hX : Martingale X ℱ μ) (m : ℕ) (hm : 1 ≤ m)
    (hint : ∀ t, Integrable (fun ω => ‖X t ω‖ ^ m) μ) {τ : ℕ → ℝ} (hτ : Monotone τ) (N : ℕ)
    {l : ℝ} (hl : 0 < l) :
    ENNReal.ofReal (l ^ m) * μ {ω | ∃ j ≤ N, l < ‖X (τ j) ω‖} ≤
      ENNReal.ofReal (∫ ω, ‖X (τ N) ω‖ ^ m ∂μ) := by
  let 𝒢 : Filtration ℕ mΩ :=
    ⟨fun k => ℱ (τ k), fun i j hij => ℱ.mono (hτ hij), fun k => ℱ.le _⟩
  let f : ℕ → Ω → ℝ := fun k ω => ‖X (τ k) ω‖ ^ m
  have hnn : 0 ≤ f := fun k ω => by positivity
  have hsub : Submartingale f 𝒢 μ := by
    refine ⟨fun k => ?_, fun i j hij => ?_, fun k => hint _⟩
    · exact (hX.stronglyMeasurable (τ k)).norm.pow m
    · have hrp : Integrable (fun ω => ‖X (τ j) ω‖ ^ (m : ℝ)) μ := by
        simpa [Real.rpow_natCast] using hint (τ j)
      have h1 := Integrable.norm_condExp_rpow_le (m := ℱ (τ i)) (μ := μ)
        (f := X (τ j)) (p := (m : ℝ)) (by exact_mod_cast hm) hrp
      have h2 := hX.condExp_ae_eq (hτ hij)
      simp only [Real.rpow_natCast] at h1
      filter_upwards [h1, h2] with ω hω1 hω2
      simp only [f]
      rw [← hω2]
      exact hω1
  have hε : (((l ^ m).toNNReal : ℝ≥0) : ℝ) = l ^ m := Real.coe_toNNReal _ (by positivity)
  have key := maximal_ineq hsub hnn (ε := (l ^ m).toNNReal) N
  simp only [hε] at key
  have hsubset : {ω | ∃ j ≤ N, l < ‖X (τ j) ω‖} ⊆
      {ω | l ^ m ≤ (Finset.range (N + 1)).sup' Finset.nonempty_range_add_one fun k => f k ω} := by
    rintro ω ⟨j, hj, hjl⟩
    refine le_trans ?_ (Finset.le_sup' (fun k => f k ω) (Finset.mem_range.2 (Nat.lt_succ_of_le hj)))
    exact pow_le_pow_left₀ hl.le hjl.le m
  calc ENNReal.ofReal (l ^ m) * μ {ω | ∃ j ≤ N, l < ‖X (τ j) ω‖}
      ≤ ((l ^ m).toNNReal : ℝ≥0∞) * μ {ω | l ^ m ≤ (Finset.range (N + 1)).sup'
          Finset.nonempty_range_add_one fun k => f k ω} :=
        mul_le_mul' le_rfl (measure_mono hsubset)
    _ ≤ _ := key
    _ ≤ ENNReal.ofReal (∫ ω, f N ω ∂μ) := by
        apply ENNReal.ofReal_le_ofReal
        exact setIntegral_le_integral (hsub.integrable N) (Eventually.of_forall (hnn N))

/-- Weak-type inequality for the supremum over `[0,S]` of a continuous martingale. -/
theorem lc3_weak_sup (hX : Martingale X ℱ μ) (hc : ∀ ω, Continuous fun t => X t ω) (m : ℕ)
    (hm : 1 ≤ m) (hint : ∀ t, Integrable (fun ω => ‖X t ω‖ ^ m) μ) {S : ℝ} (hS : 0 ≤ S) {l : ℝ}
    (hl : 0 < l) :
    ENNReal.ofReal (l ^ m) * μ {ω | l < ⨆ t ∈ Icc (0 : ℝ) S, ‖X t ω‖} ≤
      ENNReal.ofReal (∫ ω, ‖X S ω‖ ^ m ∂μ) := by
  let A : ℕ → Set Ω := fun n => {ω | ∃ j ≤ 2 ^ n, l < ‖X (lc3Grid S n j) ω‖}
  have hAmono : Monotone A := by
    refine monotone_nat_of_le_succ fun n ω hω => ?_
    obtain ⟨j, hj, hjl⟩ := hω
    refine ⟨2 * j, by rw [pow_succ]; omega, ?_⟩
    rwa [lc3Grid_double S n j hj]
  have hsub : {ω | l < ⨆ t ∈ Icc (0 : ℝ) S, ‖X t ω‖} ⊆ ⋃ n, A n := by
    intro ω hω
    simp only [mem_setOf_eq] at hω
    obtain ⟨t, ht, htl⟩ : ∃ t ∈ Icc (0 : ℝ) S, l < ‖X t ω‖ := by
      by_contra hcon
      push Not at hcon
      exact absurd (lc3_sup_le hl.le hcon) (not_le.2 hω)
    obtain ⟨k, hk⟩ := lc3_exists_grid hS ht
    have hlim : Tendsto (fun n => ‖X (lc3Grid S n (k n)) ω‖) atTop (𝓝 ‖X t ω‖) :=
      (continuous_norm.comp (hc ω)).tendsto t |>.comp hk
    obtain ⟨n, hn⟩ := (hlim.eventually (lt_mem_nhds htl)).exists
    refine mem_iUnion.2 ⟨n, min (k n) (2 ^ n), min_le_right _ _, ?_⟩
    have : lc3Grid S n (min (k n) (2 ^ n)) = lc3Grid S n (k n) := by
      unfold lc3Grid; rw [min_assoc, min_self]
    rw [this]; exact hn
  have hmeas : μ {ω | l < ⨆ t ∈ Icc (0 : ℝ) S, ‖X t ω‖} ≤ ⨆ n, μ (A n) := by
    refine (measure_mono hsub).trans ?_
    rw [hAmono.measure_iUnion]
  calc ENNReal.ofReal (l ^ m) * μ {ω | l < ⨆ t ∈ Icc (0 : ℝ) S, ‖X t ω‖}
      ≤ ENNReal.ofReal (l ^ m) * ⨆ n, μ (A n) := by gcongr
    _ = ⨆ n, ENNReal.ofReal (l ^ m) * μ (A n) := ENNReal.mul_iSup _ _
    _ ≤ _ := by
        refine iSup_le fun n => ?_
        have := lc3_weak_grid hX m hm hint (τ := lc3Grid S n) (lc3Grid_mono hS n) (2 ^ n) hl
        rwa [lc3Grid_top] at this

end Doob

/-! ### Brownian motion in `Euc d` and its coordinates -/

/-- The Brownian path in real time with values in `Euc d`. -/
def lcBM (W : ℝ≥0 → Ω → Fin d → ℝ) (s : ℝ) (ω : Ω) : Euc d :=
  WithLp.toLp 2 (ofNNRealTime W s ω)

theorem lcNoiseE_eq_lcBM (W : ℝ≥0 → Ω → Fin d → ℝ) (ν : ℝ → ℝ) (v : ℝ) (ω : Ω) :
    lcNoiseE W ν v ω = lcBM W (lcTau ν v) ω := rfl

/-- The `m`-th absolute moment of `N(0, S)`. -/
def lc3Mom (m : ℕ) (S : ℝ) : ℝ := ∫ x, ‖x‖ ^ m ∂gaussianReal 0 S.toNNReal

theorem lc3Mom_nonneg (m : ℕ) (S : ℝ) : 0 ≤ lc3Mom m S :=
  integral_nonneg fun x => by positivity

section BM

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ}
  {W : ℝ≥0 → Ω → Fin d → ℝ}

theorem lc3_coord_integrable (hW : IsBrownianFiltration P ℱ W) (k : Fin d) (m : ℕ) (hm : 1 ≤ m)
    (t : ℝ) : Integrable (fun ω => ‖ofNNRealTime W t ω k‖ ^ m) P :=
  ((hW.memLp_coord t.toNNReal k (p := (m : ℝ≥0∞)) (ENNReal.natCast_ne_top m)).integrable_norm_pow
    (by omega))

theorem lc3_coord_moment (hW : IsBrownianFiltration P ℱ W) (k : Fin d) (m : ℕ) {S : ℝ}
    (hS : 0 ≤ S) : ∫ ω, ‖ofNNRealTime W S ω k‖ ^ m ∂P = lc3Mom m S := by
  have h := (hW.hasLaw_coord S.toNNReal k).integral_comp (f := fun x : ℝ => ‖x‖ ^ m) (by fun_prop)
  simpa [lc3Mom] using h

/-- Tail of the supremum of one coordinate. -/
theorem lc3_coord_tail (hW : IsBrownianFiltration P ℱ W) (k : Fin d) (m : ℕ) (hm : 1 ≤ m) {S : ℝ}
    (hS : 0 ≤ S) {l : ℝ} (hl : 0 < l) :
    ENNReal.ofReal (l ^ m) * P {ω | l < ⨆ t ∈ Icc (0 : ℝ) S, ‖ofNNRealTime W t ω k‖} ≤
      ENNReal.ofReal (lc3Mom m S) := by
  have hmart := hW.martingale k
  have hc : ∀ ω, Continuous fun t : ℝ => ofNNRealTime W t ω k := fun ω =>
    (continuous_apply k).comp (continuous_ofNNRealTime W ω (hW.cont ω))
  have := lc3_weak_sup hmart hc m hm (lc3_coord_integrable hW k m hm) hS hl
  rwa [lc3_coord_moment hW k m hS] at this

theorem lcBM_cont (hW : IsBrownianFiltration P ℱ W) (ω : Ω) : Continuous fun s => lcBM W s ω :=
  (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).comp
    (continuous_pi fun k => (continuous_apply k).comp
      (continuous_ofNNRealTime W ω (hW.cont ω)))

theorem lcBM_measurable (hW : IsBrownianFiltration P ℱ W) (s : ℝ) : Measurable (lcBM W s) :=
  (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp (hW.measurable _)

theorem lc3_norm_le_of_coord (x : Euc d) {c : ℝ} (hc : 0 ≤ c) (h : ∀ k, |x k| ≤ c) :
    ‖x‖ ≤ d * c := by
  have h1 : ‖x‖ ^ 2 ≤ (d * c) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, c ^ 2 := by
          refine Finset.sum_le_sum fun i _ => ?_
          rw [Real.norm_eq_abs]
          exact pow_le_pow_left₀ (abs_nonneg _) (h i) 2
      _ = d * c ^ 2 := by simp
      _ ≤ (d * c) ^ 2 := by
          rcases Nat.eq_zero_or_pos d with hd | hd
          · subst hd; simp
          · have : (1 : ℝ) ≤ d := by exact_mod_cast hd
            nlinarith [sq_nonneg c]
  exact (pow_le_pow_iff_left₀ (norm_nonneg _) (by positivity) (by norm_num)).1 h1

/-- Tail of the supremum of the Euclidean norm of the Brownian path on `[0,S]`. -/
theorem lc3_bm_tail (hW : IsBrownianFiltration P ℱ W) (m : ℕ) (hm : 1 ≤ m) {S : ℝ} (hS : 0 ≤ S)
    {t : ℝ} (ht : 0 < t) :
    ENNReal.ofReal (t ^ m) * P {ω | t ≤ ⨆ s ∈ Icc (0 : ℝ) S, ‖lcBM W s ω‖} ≤
      ENNReal.ofReal (d * (2 * d) ^ m * lc3Mom m S) := by
  set R : Ω → ℝ := fun ω => ⨆ s ∈ Icc (0 : ℝ) S, ‖lcBM W s ω‖ with hR
  set lam : ℝ := t / (2 * d) with hlam
  have hsub : {ω | t ≤ R ω} ⊆ ⋃ k : Fin d,
      {ω | lam < ⨆ s ∈ Icc (0 : ℝ) S, ‖ofNNRealTime W s ω k‖} := by
    intro ω hω
    simp only [mem_setOf_eq] at hω
    by_contra hcon
    simp only [mem_iUnion, mem_setOf_eq, not_exists, not_lt] at hcon
    have hlam0 : 0 ≤ lam := by
      rcases Nat.eq_zero_or_pos d with hd | hd
      · simp [hlam, hd]
      · positivity
    have hcoord : ∀ s ∈ Icc (0 : ℝ) S, ∀ k, |ofNNRealTime W s ω k| ≤ lam := fun s hs k => by
      have := lc3_le_sup (g := fun s => ofNNRealTime W s ω k)
        ((continuous_apply k).comp (continuous_ofNNRealTime W ω (hW.cont ω))) hs
      exact (by simpa using this : |ofNNRealTime W s ω k| ≤ _).trans (hcon k)
    have hnorm : ∀ s ∈ Icc (0 : ℝ) S, ‖lcBM W s ω‖ ≤ t / 2 := by
      intro s hs
      have h1 := lc3_norm_le_of_coord (lcBM W s ω) hlam0 (hcoord s hs)
      refine h1.trans ?_
      rcases Nat.eq_zero_or_pos d with hd | hd
      · simp [hd]; positivity
      · have : (0 : ℝ) < d := by exact_mod_cast hd
        have e : (d : ℝ) * lam = t / 2 := by rw [hlam]; field_simp
        rw [e]
    have := lc3_sup_le (g := fun s => lcBM W s ω) (by positivity) hnorm
    exact absurd hω (not_le.2 (lt_of_le_of_lt this (by linarith)))
  calc ENNReal.ofReal (t ^ m) * P {ω | t ≤ R ω}
      ≤ ENNReal.ofReal (t ^ m) * ∑ k : Fin d,
          P {ω | lam < ⨆ s ∈ Icc (0 : ℝ) S, ‖ofNNRealTime W s ω k‖} :=
        mul_le_mul' le_rfl ((measure_mono hsub).trans (measure_iUnion_fintype_le _ _))
    _ = ∑ k : Fin d, ENNReal.ofReal (t ^ m) *
          P {ω | lam < ⨆ s ∈ Icc (0 : ℝ) S, ‖ofNNRealTime W s ω k‖} := Finset.mul_sum _ _ _
    _ ≤ ∑ _k : Fin d, ENNReal.ofReal ((2 * d) ^ m * lc3Mom m S) := by
        refine Finset.sum_le_sum fun k _ => ?_
        have hd : 0 < d := Fin.pos k
        have hd' : (0 : ℝ) < d := by exact_mod_cast hd
        have hlampos : 0 < lam := by positivity
        have htl : t ^ m = (2 * d) ^ m * lam ^ m := by
          rw [← mul_pow]; congr 1; rw [hlam]; field_simp
        have := lc3_coord_tail hW k m hm hS hlampos
        calc ENNReal.ofReal (t ^ m) * P {ω | lam < ⨆ s ∈ Icc (0 : ℝ) S, ‖ofNNRealTime W s ω k‖}
            = ENNReal.ofReal ((2 * d) ^ m) * (ENNReal.ofReal (lam ^ m) *
                P {ω | lam < ⨆ s ∈ Icc (0 : ℝ) S, ‖ofNNRealTime W s ω k‖}) := by
              rw [htl, ENNReal.ofReal_mul (by positivity), mul_assoc]
          _ ≤ ENNReal.ofReal ((2 * d) ^ m) * ENNReal.ofReal (lc3Mom m S) := by gcongr
          _ = _ := by rw [← ENNReal.ofReal_mul (by positivity)]
    _ = ENNReal.ofReal (d * (2 * d) ^ m * lc3Mom m S) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity), mul_assoc]

end BM

/-! ### Layer cake: moments from a polynomial tail -/

section Layer

variable {μ : Measure Ω} [IsProbabilityMeasure μ]

/-- The constant `∫ (1 + t²)⁻¹` (finite; equals `π`). -/
def lc3K0 : ℝ≥0∞ := ∫⁻ t : ℝ, ENNReal.ofReal ((1 + t ^ 2)⁻¹)

theorem lc3K0_lt_top : lc3K0 < ∞ := integrable_inv_one_add_sq.lintegral_lt_top

/-- From the tail `t^{q+2} μ(R ≥ t) ≤ B` to a bound on `∫⁻ R^{q+1}`. -/
theorem lc3_layer {R : Ω → ℝ} (hR : Measurable R) (hR0 : ∀ ω, 0 ≤ R ω) (q : ℕ) {B : ℝ}
    (hB : 0 ≤ B)
    (htail : ∀ t : ℝ, 0 < t → ENNReal.ofReal (t ^ (q + 2)) * μ {ω | t ≤ R ω} ≤ ENNReal.ofReal B) :
    ∫⁻ ω, ENNReal.ofReal (R ω ^ (q + 1)) ∂μ ≤
      ENNReal.ofReal ((q + 1 : ℕ) : ℝ) * (ENNReal.ofReal (2 * (1 + B)) * lc3K0) := by
  have hp : (0 : ℝ) < ((q + 1 : ℕ) : ℝ) := by positivity
  have h1 := lintegral_rpow_eq_lintegral_meas_le_mul (μ := μ) (f := R)
    (Eventually.of_forall hR0) hR.aemeasurable hp
  have e1 : ∀ ω, R ω ^ ((q + 1 : ℕ) : ℝ) = R ω ^ (q + 1) := fun ω => Real.rpow_natCast _ _
  have e2 : ∀ t : ℝ, t ^ (((q + 1 : ℕ) : ℝ) - 1) = t ^ q := fun t => by
    rw [show ((q + 1 : ℕ) : ℝ) - 1 = (q : ℝ) by push_cast; ring, Real.rpow_natCast]
  simp only [e1, e2] at h1
  rw [h1]
  gcongr
  calc ∫⁻ t in Ioi (0 : ℝ), μ {a | t ≤ R a} * ENNReal.ofReal (t ^ q)
      ≤ ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal (2 * (1 + B)) * ENNReal.ofReal ((1 + t ^ 2)⁻¹) := by
        refine setLIntegral_mono' measurableSet_Ioi fun t ht => ?_
        have ht' : (0 : ℝ) < t := ht
        set a : ℝ := (μ {a | t ≤ R a}).toReal with ha
        have hμ : μ {a | t ≤ R a} = ENNReal.ofReal a := (ENNReal.ofReal_toReal (measure_ne_top _ _)).symm
        have ha0 : 0 ≤ a := ENNReal.toReal_nonneg
        have ha1 : a ≤ 1 := by
          rw [ha]
          exact ENNReal.toReal_le_of_le_ofReal zero_le_one (by simpa using prob_le_one)
        have h2 := htail t ht'
        rw [hμ, ← ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_le_ofReal_iff hB] at h2
        have h3 : a * t ^ q * (1 + t ^ 2) ≤ 2 * (1 + B) := by
          rcases le_or_gt t 1 with h | h
          · have : t ^ q ≤ 1 := pow_le_one₀ ht'.le h
            have : a * t ^ q ≤ 1 := by nlinarith
            nlinarith [sq_nonneg t]
          · have e : t ^ (q + 2) = t ^ q * t ^ 2 := pow_add _ _ _
            have : a * t ^ q * (1 + t ^ 2) ≤ a * t ^ q * (2 * t ^ 2) := by
              apply mul_le_mul_of_nonneg_left _ (by positivity)
              nlinarith
            nlinarith
        rw [hμ, ← ENNReal.ofReal_mul ha0, ← ENNReal.ofReal_mul (by positivity)]
        refine ENNReal.ofReal_le_ofReal ?_
        rw [← div_eq_mul_inv, le_div_iff₀ (by positivity)]
        exact h3
    _ = ENNReal.ofReal (2 * (1 + B)) * ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal ((1 + t ^ 2)⁻¹) :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ _ := by
        unfold lc3K0
        exact mul_le_mul' le_rfl (setLIntegral_le_lintegral _ _)

end Layer

/-! ### The supremum moment of Brownian motion -/

/-- The tail constant `B = d (2d)^{q+2} E|Z|^{q+2}`, `Z ~ N(0,S)`. -/
def lc3B (d q : ℕ) (S : ℝ) : ℝ := d * (2 * d) ^ (q + 2) * lc3Mom (q + 2) S

theorem lc3B_nonneg (d q : ℕ) (S : ℝ) : 0 ≤ lc3B d q S := by
  unfold lc3B; have := lc3Mom_nonneg (q + 2) S; positivity

/-- The moment constant `C(d, q, S)` for `E (1 + sup_{s ≤ S} ‖B_s‖)^{q+1}`. -/
def lc3C (d q : ℕ) (S : ℝ) : ℝ :=
  2 ^ (q + 1) * (1 + (ENNReal.ofReal ((q + 1 : ℕ) : ℝ) *
    (ENNReal.ofReal (2 * (1 + lc3B d q S)) * lc3K0)).toReal)

theorem lc3_one_add_pow_le {R : ℝ} (hR : 0 ≤ R) (p : ℕ) : (1 + R) ^ p ≤ 2 ^ p * (1 + R ^ p) := by
  have hRp : 0 ≤ R ^ p := pow_nonneg hR p
  rcases le_or_gt R 1 with h | h
  · calc (1 + R) ^ p ≤ 2 ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
      _ ≤ 2 ^ p * (1 + R ^ p) := by nlinarith [pow_pos (by norm_num : (0 : ℝ) < 2) p]
  · calc (1 + R) ^ p ≤ (2 * R) ^ p := pow_le_pow_left₀ (by linarith) (by linarith) p
      _ = 2 ^ p * R ^ p := mul_pow _ _ _
      _ ≤ 2 ^ p * (1 + R ^ p) := by
          apply mul_le_mul_of_nonneg_left _ (by positivity); linarith

section BMMoment

variable {P : Measure Ω} [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W : ℝ≥0 → Ω → Fin d → ℝ}

/-- **Moments of the running supremum of Brownian motion**: `E (1 + sup_{s ≤ S} ‖W_s‖)^{q+1}
≤ C(d, q, S)`, with integrability. -/
theorem lc3_bm_sup_moment (hW : IsBrownianFiltration P ℱ W) (q : ℕ) {S : ℝ} (hS : 0 ≤ S) :
    Integrable (fun ω => (1 + ⨆ s ∈ Icc (0 : ℝ) S, ‖lcBM W s ω‖) ^ (q + 1)) P ∧
    ∫ ω, (1 + ⨆ s ∈ Icc (0 : ℝ) S, ‖lcBM W s ω‖) ^ (q + 1) ∂P ≤ lc3C d q S := by
  set R : Ω → ℝ := fun ω => ⨆ s ∈ Icc (0 : ℝ) S, ‖lcBM W s ω‖ with hRdef
  have hRm : Measurable R :=
    lc_measurable_sup_norm (fun s => lcBM_measurable hW s) (lcBM_cont hW) S
  have hR0 : ∀ ω, 0 ≤ R ω := fun ω => lc3_sup_nonneg (g := fun s => lcBM W s ω) S
  have htail : ∀ t : ℝ, 0 < t →
      ENNReal.ofReal (t ^ (q + 2)) * P {ω | t ≤ R ω} ≤ ENNReal.ofReal (lc3B d q S) :=
    fun t ht => lc3_bm_tail hW (q + 2) (by omega) hS ht
  have hL := lc3_layer hRm hR0 q (lc3B_nonneg d q S) htail
  set M : ℝ≥0∞ := ENNReal.ofReal ((q + 1 : ℕ) : ℝ) *
    (ENNReal.ofReal (2 * (1 + lc3B d q S)) * lc3K0) with hM
  have hMtop : M < ∞ :=
    ENNReal.mul_lt_top ENNReal.ofReal_lt_top (ENNReal.mul_lt_top ENNReal.ofReal_lt_top lc3K0_lt_top)
  have hRint : Integrable (fun ω => R ω ^ (q + 1)) P := by
    refine ⟨(hRm.pow_const _).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal (Eventually.of_forall fun ω => pow_nonneg (hR0 ω) _)]
    exact lt_of_le_of_lt hL hMtop
  have hRle : ∫ ω, R ω ^ (q + 1) ∂P ≤ M.toReal := by
    rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun ω => pow_nonneg (hR0 ω) _)
      (hRint.aestronglyMeasurable)]
    exact ENNReal.toReal_mono hMtop.ne hL
  have hG : Integrable (fun ω => 2 ^ (q + 1) * (1 + R ω ^ (q + 1))) P :=
    (integrable_const _ |>.add hRint).const_mul _
  have hI : Integrable (fun ω => (1 + R ω) ^ (q + 1)) P := by
    refine hG.mono' (((measurable_const.add hRm).pow_const _).aestronglyMeasurable) ?_
    refine Eventually.of_forall fun ω => ?_
    rw [Real.norm_of_nonneg (by have := hR0 ω; positivity)]
    exact lc3_one_add_pow_le (hR0 ω) _
  refine ⟨hI, ?_⟩
  calc ∫ ω, (1 + R ω) ^ (q + 1) ∂P ≤ ∫ ω, 2 ^ (q + 1) * (1 + R ω ^ (q + 1)) ∂P :=
        integral_mono hI hG fun ω => lc3_one_add_pow_le (hR0 ω) _
    _ = 2 ^ (q + 1) * (1 + ∫ ω, R ω ^ (q + 1) ∂P) := by
        rw [integral_const_mul, integral_add (integrable_const _) hRint]
        simp
    _ ≤ lc3C d q S := by
        unfold lc3C
        exact mul_le_mul_of_nonneg_left (by linarith) (by positivity)

end BMMoment

/-! ### The main theorem -/

/-- **LC-3 (sup moment).**  For every `p`, `T`, `ν*` there is a constant `C` (depending only on
`d, p, ν* T`, not on `Ω, P, ℱ, W, ν`) such that, for every Brownian filtration and every continuous
`ν` with `0 ≤ ν ≤ ν*`, `(1 + sup_{v ≤ T} ‖G_v‖)^p` is integrable with `E ≤ C`, where `G = lcNoiseE W ν`
is the time-changed noise. -/
theorem lc_sup_moment.{u} (d p : ℕ) (T νstar : ℝ) :
    ∃ C : ℝ, ∀ {Ω : Type u} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin d → ℝ) (ν : ℝ → ℝ),
      IsBrownianFiltration P ℱ W → Continuous ν → (∀ r, 0 ≤ ν r ∧ ν r ≤ νstar) →
      Integrable (fun ω => (1 + ⨆ v ∈ Icc (0 : ℝ) T, ‖lcNoiseE W ν v ω‖) ^ p) P ∧
      ∫ ω, (1 + ⨆ v ∈ Icc (0 : ℝ) T, ‖lcNoiseE W ν v ω‖) ^ p ∂P ≤ C := by
  rcases p with _ | q
  · exact ⟨1, fun {Ω} {mΩ} P _ ℱ W ν _ _ _ => by simp⟩
  · refine ⟨lc3C d q (2 * max νstar 0 * max T 0), fun {Ω} {mΩ} P _ ℱ W ν hW hν hν' => ?_⟩
    have hS : 0 ≤ 2 * max νstar 0 * max T 0 := by positivity
    obtain ⟨hI, hle⟩ := lc3_bm_sup_moment hW q hS
    set S := 2 * max νstar 0 * max T 0 with hSdef
    set R : Ω → ℝ := fun ω => ⨆ s ∈ Icc (0 : ℝ) S, ‖lcBM W s ω‖ with hRdef
    set g : Ω → ℝ := fun ω => ⨆ v ∈ Icc (0 : ℝ) T, ‖lcNoiseE W ν v ω‖ with hgdef
    have hR0 : ∀ ω, 0 ≤ R ω := fun ω => lc3_sup_nonneg (g := fun s => lcBM W s ω) S
    have hg0 : ∀ ω, 0 ≤ g ω := fun ω => lc3_sup_nonneg (g := fun v => lcNoiseE W ν v ω) T
    have hgR : ∀ ω, g ω ≤ R ω := by
      intro ω
      refine lc3_sup_le (hR0 ω) fun v hv => ?_
      rw [lcNoiseE_eq_lcBM]
      refine lc3_le_sup (g := fun s => lcBM W s ω) (lcBM_cont hW ω) ⟨lcTau_nonneg hν (fun x => (hν' x).1) hv.1, ?_⟩
      have h1 := lcTau_le hν (fun x => (hν' x).2) hv.1
      have hνs : 0 ≤ νstar := (hν' 0).1.trans (hν' 0).2
      have hT0 : 0 ≤ T := hv.1.trans hv.2
      rw [hSdef, max_eq_left hνs, max_eq_left hT0]
      nlinarith [hv.2]
    have hgm : Measurable g := lc_noise_sup_measurable hW hν T
    have hint : Integrable (fun ω => (1 + g ω) ^ (q + 1)) P := by
      refine hI.mono' ((measurable_const.add hgm).pow_const _).aestronglyMeasurable ?_
      refine Eventually.of_forall fun ω => ?_
      rw [Real.norm_of_nonneg (by have := hg0 ω; positivity)]
      exact pow_le_pow_left₀ (by have := hg0 ω; positivity) (by linarith [hgR ω]) _
    refine ⟨hint, (integral_mono hint hI fun ω => ?_).trans hle⟩
    exact pow_le_pow_left₀ (by have := hg0 ω; positivity) (by linarith [hgR ω]) _

end HRS.MS.Lc
