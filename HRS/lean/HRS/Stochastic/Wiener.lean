import HRS.Stochastic.Brownian

/-!
# Existence of Brownian motion (Lévy–Ciesielski construction)

Package SI-01m.  Brownian motion with everywhere continuous paths on the sequence space
`WienerSeq = (ℕ × ℕ) → ℝ` with the product Gaussian measure `wienerMeasure`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS

/-! ### A.1 Discrete coefficients and Parseval -/

/-- Midpoint-displacement amplitude at level `N`: `lcAmp N ^ 2 = 2^{-(N+2)}`. -/
def lcAmp (N : ℕ) : ℝ := (2 : ℝ) ^ (-((N : ℝ) + 2) / 2)

theorem lcAmp_pos (N : ℕ) : 0 < lcAmp N := Real.rpow_pos_of_pos (by norm_num) _

theorem lcAmp_sq (N : ℕ) : lcAmp N ^ 2 = (2 : ℝ)⁻¹ ^ (N + 2) := by
  unfold lcAmp
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  have : -((N : ℝ) + 2) / 2 * ((2 : ℕ) : ℝ) = -((N + 2 : ℕ) : ℝ) := by push_cast; ring
  rw [this, Real.rpow_neg (by norm_num), Real.rpow_natCast, inv_pow]

/-- `lcCoef N c i`: coefficient of coordinate `c = (m, j)` in the increment of the level-`N`
process over the level-`N` cell `[i 2^{-N}, (i+1) 2^{-N}]`. -/
def lcCoef : ℕ → ℕ × ℕ → ℕ → ℝ
  | 0, (0, j), i => if i = j then 1 else 0
  | 0, (_ + 1, _), _ => 0
  | N + 1, (m, j), i =>
      if m ≤ N then lcCoef N (m, j) (i / 2) / 2
      else if m = N + 1 then
        (if i = 2 * j then lcAmp N else if i = 2 * j + 1 then -lcAmp N else 0)
      else 0

theorem lcCoef_support : ∀ {N m j i : ℕ}, lcCoef N (m, j) i ≠ 0 → m ≤ N ∧ j ≤ i
  | 0, 0, j, i, h => by
    simp only [lcCoef] at h
    split_ifs at h with h1
    · exact ⟨le_rfl, h1.symm.le⟩
    · exact absurd rfl h
  | 0, m + 1, j, i, h => by simp [lcCoef] at h
  | N + 1, m, j, i, h => by
    simp only [lcCoef] at h
    split_ifs at h with h1 h2 h3 h4
    · have := lcCoef_support (N := N) (m := m) (j := j) (i := i / 2)
        (by intro h0; apply h; rw [h0]; simp)
      exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · exact ⟨by omega, by omega⟩
    · exact absurd rfl h
    · exact absurd rfl h

theorem lcCoef_even (N m j i : ℕ) (hm : m ≤ N) :
    lcCoef (N + 1) (m, j) (2 * i) = lcCoef N (m, j) i / 2 := by
  simp [lcCoef, hm]

theorem lcCoef_odd (N m j i : ℕ) (hm : m ≤ N) :
    lcCoef (N + 1) (m, j) (2 * i + 1) = lcCoef N (m, j) i / 2 := by
  have : (2 * i + 1) / 2 = i := by omega
  simp [lcCoef, hm, this]

theorem lcCoef_top_even (N j i : ℕ) :
    lcCoef (N + 1) (N + 1, j) (2 * i) = if i = j then lcAmp N else 0 := by
  simp only [lcCoef, Nat.not_succ_le_self, ite_false, ite_true]
  by_cases h : i = j
  · simp [h]
  · have h1 : ¬ 2 * i = 2 * j := by omega
    have h2 : ¬ 2 * i = 2 * j + 1 := by omega
    simp [h, h1, h2]

theorem lcCoef_top_odd (N j i : ℕ) :
    lcCoef (N + 1) (N + 1, j) (2 * i + 1) = if i = j then -lcAmp N else 0 := by
  simp only [lcCoef, Nat.not_succ_le_self, ite_false, ite_true]
  by_cases h : i = j
  · have h2 : ¬ 2 * i + 1 = 2 * j := by omega
    simp [h]
  · have h1 : ¬ 2 * i + 1 = 2 * j := by omega
    have h2 : ¬ 2 * i + 1 = 2 * j + 1 := by omega
    simp [h, h1]

/-- The coordinates that can appear at level `N` for cells `i < n`. -/
def lcSupp (N n : ℕ) : Finset (ℕ × ℕ) := Finset.range (N + 1) ×ˢ Finset.range n

theorem sum_range_two_mul {M : Type*} [AddCommMonoid M] (f : ℕ → M) (n : ℕ) :
    ∑ i ∈ Finset.range (2 * n), f i = ∑ p ∈ Finset.range n, (f (2 * p) + f (2 * p + 1)) := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [show 2 * (n + 1) = 2 * n + 1 + 1 by ring, Finset.sum_range_succ, Finset.sum_range_succ,
      ih, Finset.sum_range_succ]
    abel

/-- Truncation of a coefficient sequence. -/
def trunc (n : ℕ) (θ : ℕ → ℝ) (i : ℕ) : ℝ := if i < n then θ i else 0

theorem sum_range_trunc_two_mul (n : ℕ) (θ g : ℕ → ℝ) :
    ∑ i ∈ Finset.range n, θ i * g i =
      ∑ p ∈ Finset.range n, (trunc n θ (2 * p) * g (2 * p) + trunc n θ (2 * p + 1) * g (2 * p + 1)) := by
  rw [← sum_range_two_mul (fun i => trunc n θ i * g i) n]
  have h1 : ∑ i ∈ Finset.range n, θ i * g i = ∑ i ∈ Finset.range n, trunc n θ i * g i :=
    Finset.sum_congr rfl fun i hi => by simp [trunc, Finset.mem_range.1 hi]
  rw [h1]
  apply Finset.sum_subset
  · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
  · intro i _ hi; simp [trunc, show ¬ i < n from fun h => hi (Finset.mem_range.2 h)]

/-- **Discrete Parseval.** -/
theorem lcCoef_parseval (N n : ℕ) (θ : ℕ → ℝ) :
    ∑ c ∈ lcSupp N n, (∑ i ∈ Finset.range n, θ i * lcCoef N c i) ^ 2 =
      (2 : ℝ)⁻¹ ^ N * ∑ i ∈ Finset.range n, θ i ^ 2 := by
  induction N generalizing θ with
  | zero =>
    simp only [lcSupp, Finset.sum_product, Finset.sum_range_succ, Finset.sum_range_zero, zero_add,
      pow_zero, one_mul]
    refine Finset.sum_congr rfl fun j hj => ?_
    simp [lcCoef, Finset.mem_range.1 hj]
  | succ N ih =>
    have hold : ∀ m j, m ≤ N → ∑ i ∈ Finset.range n, θ i * lcCoef (N + 1) (m, j) i =
        (∑ p ∈ Finset.range n, (trunc n θ (2 * p) + trunc n θ (2 * p + 1)) * lcCoef N (m, j) p) / 2 := by
      intro m j hm
      rw [sum_range_trunc_two_mul, Finset.sum_div]
      refine Finset.sum_congr rfl fun p _ => ?_
      rw [lcCoef_even _ _ _ _ hm, lcCoef_odd _ _ _ _ hm]; ring
    have hnew : ∀ j ∈ Finset.range n, ∑ i ∈ Finset.range n, θ i * lcCoef (N + 1) (N + 1, j) i =
        lcAmp N * (trunc n θ (2 * j) - trunc n θ (2 * j + 1)) := by
      intro j hj
      rw [sum_range_trunc_two_mul]
      simp_rw [lcCoef_top_even, lcCoef_top_odd]
      have : ∀ p, trunc n θ (2 * p) * (if p = j then lcAmp N else 0) +
          trunc n θ (2 * p + 1) * (if p = j then -lcAmp N else 0) =
          if p = j then lcAmp N * (trunc n θ (2 * p) - trunc n θ (2 * p + 1)) else 0 := by
        intro p; split_ifs <;> simp; ring
      simp_rw [this]
      rw [Finset.sum_ite_eq' (Finset.range n) j]
      simp [hj]
    have hsq : ∑ i ∈ Finset.range n, θ i ^ 2 = ∑ p ∈ Finset.range n,
        (trunc n θ (2 * p) ^ 2 + trunc n θ (2 * p + 1) ^ 2) := by
      have := sum_range_trunc_two_mul n (fun i => θ i ^ 2) (fun _ => 1)
      simp only [mul_one] at this
      rw [this]
      refine Finset.sum_congr rfl fun p _ => ?_
      simp only [trunc]; split_ifs <;> simp
    have ih' := ih (fun p => trunc n θ (2 * p) + trunc n θ (2 * p + 1))
    unfold lcSupp at ih' ⊢
    rw [Finset.sum_product] at ih'
    rw [Finset.sum_product, Finset.sum_range_succ]
    have e1 : ∑ m ∈ Finset.range (N + 1), ∑ j ∈ Finset.range n,
        (∑ i ∈ Finset.range n, θ i * lcCoef (N + 1) (m, j) i) ^ 2 =
        (1 / 4) * ((2 : ℝ)⁻¹ ^ N * ∑ p ∈ Finset.range n,
          (trunc n θ (2 * p) + trunc n θ (2 * p + 1)) ^ 2) := by
      rw [← ih', Finset.mul_sum]
      refine Finset.sum_congr rfl fun m hm => ?_
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [hold m j (by have := Finset.mem_range.1 hm; omega)]; ring
    have e2 : ∑ j ∈ Finset.range n, (∑ i ∈ Finset.range n, θ i * lcCoef (N + 1) (N + 1, j) i) ^ 2 =
        ((2 : ℝ)⁻¹ ^ (N + 2)) * ∑ p ∈ Finset.range n,
          (trunc n θ (2 * p) - trunc n θ (2 * p + 1)) ^ 2 := by
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun j hj => ?_
      rw [hnew j hj, mul_pow, lcAmp_sq]
    rw [e1, e2, hsq]
    simp only [Finset.mul_sum]
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun p _ => ?_
    ring

/-! ### A.2 The sequence space and the level-`N` increments -/

/-- The sequence space of the Lévy–Ciesielski construction. -/
abbrev WienerSeq : Type := (ℕ × ℕ) → ℝ

/-- i.i.d. `N(0,1)` coordinates. -/
noncomputable def wienerMeasure : Measure WienerSeq :=
  Measure.infinitePi fun _ : ℕ × ℕ => gaussianReal 0 1

instance : IsProbabilityMeasure wienerMeasure := by unfold wienerMeasure; infer_instance

theorem hasLaw_coord (c : ℕ × ℕ) :
    HasLaw (fun ω : WienerSeq => ω c) (gaussianReal 0 1) wienerMeasure :=
  (measurePreserving_eval_infinitePi (fun _ : ℕ × ℕ => gaussianReal 0 1) c).hasLaw

theorem iIndepFun_coord : iIndepFun (fun (c : ℕ × ℕ) (ω : WienerSeq) => ω c) wienerMeasure :=
  iIndepFun_infinitePi (P := fun _ : ℕ × ℕ => gaussianReal 0 1) (X := fun _ => id)
    fun _ => measurable_id

/-- Law of a finite linear combination of the coordinates. -/
theorem hasLaw_finset_sum_coord (S : Finset (ℕ × ℕ)) (a : ℕ × ℕ → ℝ) :
    HasLaw (fun ω : WienerSeq => ∑ c ∈ S, a c * ω c)
      (gaussianReal 0 (Real.toNNReal (∑ c ∈ S, a c ^ 2))) wienerMeasure := by
  have hm : Measurable fun ω : WienerSeq => ∑ c ∈ S, a c * ω c := by fun_prop
  refine ⟨hm.aemeasurable, ?_⟩
  refine Measure.ext_of_charFun ?_
  funext u
  have hind : iIndepFun (S.restrict (fun c (ω : WienerSeq) => a c * ω c)) wienerMeasure :=
    (iIndepFun_coord.comp (fun c x => a c * x) (fun c => by fun_prop)).restrict S
  have h := iIndepFun.charFun_map_fun_finsetSum_eq_prod (P := wienerMeasure) (s := S)
    (X := fun c (ω : WienerSeq) => a c * ω c) (fun c _ => (measurable_const.mul (measurable_pi_apply c)).aemeasurable) hind
  rw [congrFun h u, Finset.prod_apply]
  have h1 : ∀ c ∈ S, charFun (wienerMeasure.map (fun ω : WienerSeq => a c * ω c)) u =
      Complex.exp (-(((a c ^ 2 : ℝ)) * u ^ 2 / 2 : ℝ)) := by
    intro c _
    rw [charFun_map_mul_comp (hasLaw_coord c).aemeasurable, (hasLaw_coord c).map_eq,
      charFun_gaussianReal]
    congr 1
    push_cast
    ring
  rw [Finset.prod_congr rfl h1, ← Complex.exp_sum, charFun_gaussianReal]
  congr 1
  rw [Real.coe_toNNReal _ (Finset.sum_nonneg fun c _ => sq_nonneg (a c))]
  push_cast
  rw [Finset.sum_neg_distrib, ← Finset.sum_div, ← Finset.sum_mul]
  simp

/-- Level-`N` increment over cell `i`. -/
def lcIncr (N i : ℕ) (ω : WienerSeq) : ℝ := ∑ c ∈ lcSupp N (i + 1), lcCoef N c i * ω c

theorem measurable_lcIncr (N i : ℕ) : Measurable (lcIncr N i) := by
  unfold lcIncr
  exact Finset.measurable_sum _ fun c _ => measurable_const.mul (measurable_pi_apply c)

theorem lcIncr_eq_sum (N i n : ℕ) (h : i < n) (ω : WienerSeq) :
    lcIncr N i ω = ∑ c ∈ lcSupp N n, lcCoef N c i * ω c := by
  unfold lcIncr
  apply Finset.sum_subset
  · intro c hc
    simp only [lcSupp, Finset.mem_product, Finset.mem_range] at hc ⊢
    omega
  · intro c hc hc'
    by_contra hne
    have h0 : lcCoef N c i ≠ 0 := fun h0 => hne (by rw [h0]; simp)
    obtain ⟨m, j⟩ := c
    have := lcCoef_support h0
    simp only [lcSupp, Finset.mem_product, Finset.mem_range] at hc'
    omega

theorem sum_lcSupp_succ (N n : ℕ) (f : ℕ × ℕ → ℝ) :
    ∑ c ∈ lcSupp (N + 1) n, f c = ∑ c ∈ lcSupp N n, f c + ∑ j ∈ Finset.range n, f (N + 1, j) := by
  unfold lcSupp
  rw [Finset.sum_product, Finset.sum_product, Finset.sum_range_succ]

theorem lcIncr_even (N i : ℕ) (ω : WienerSeq) :
    lcIncr (N + 1) (2 * i) ω = lcIncr N i ω / 2 + lcAmp N * ω (N + 1, i) := by
  rw [lcIncr_eq_sum (N + 1) (2 * i) (2 * i + 2) (by omega), lcIncr_eq_sum N i (2 * i + 2) (by omega),
    sum_lcSupp_succ, Finset.sum_div]
  congr 1
  · refine Finset.sum_congr rfl fun c hc => ?_
    obtain ⟨m, j⟩ := c
    have hm : m ≤ N := by
      simp only [lcSupp, Finset.mem_product, Finset.mem_range] at hc; omega
    rw [lcCoef_even _ _ _ _ hm]; ring
  · simp_rw [lcCoef_top_even]
    simp [show i < 2 * i + 2 by omega]

theorem lcIncr_odd (N i : ℕ) (ω : WienerSeq) :
    lcIncr (N + 1) (2 * i + 1) ω = lcIncr N i ω / 2 - lcAmp N * ω (N + 1, i) := by
  rw [lcIncr_eq_sum (N + 1) (2 * i + 1) (2 * i + 2) (by omega),
    lcIncr_eq_sum N i (2 * i + 2) (by omega), sum_lcSupp_succ, Finset.sum_div, sub_eq_add_neg]
  congr 1
  · refine Finset.sum_congr rfl fun c hc => ?_
    obtain ⟨m, j⟩ := c
    have hm : m ≤ N := by
      simp only [lcSupp, Finset.mem_product, Finset.mem_range] at hc; omega
    rw [lcCoef_odd _ _ _ _ hm]; ring
  · simp_rw [lcCoef_top_odd]
    simp [show i < 2 * i + 2 by omega]

theorem lcIncr_even_add_odd (N i : ℕ) (ω : WienerSeq) :
    lcIncr (N + 1) (2 * i) ω + lcIncr (N + 1) (2 * i + 1) ω = lcIncr N i ω := by
  rw [lcIncr_even, lcIncr_odd]; ring

/-- Law of a linear combination of level-`N` increments (Parseval). -/
theorem hasLaw_lcIncr_sum (N n : ℕ) (ϑ : ℕ → ℝ) :
    HasLaw (fun ω : WienerSeq => ∑ i ∈ Finset.range n, ϑ i * lcIncr N i ω)
      (gaussianReal 0 (Real.toNNReal ((2 : ℝ)⁻¹ ^ N * ∑ i ∈ Finset.range n, ϑ i ^ 2)))
      wienerMeasure := by
  have h := hasLaw_finset_sum_coord (lcSupp N n) (fun c => ∑ i ∈ Finset.range n, ϑ i * lcCoef N c i)
  rw [lcCoef_parseval] at h
  refine h.congr (Filter.Eventually.of_forall fun ω => ?_)
  simp only
  have e : ∀ i ∈ Finset.range n, ϑ i * lcIncr N i ω =
      ∑ c ∈ lcSupp N n, ϑ i * lcCoef N c i * ω c := fun i hi => by
    rw [lcIncr_eq_sum N i n (Finset.mem_range.1 hi), Finset.mul_sum]
    exact Finset.sum_congr rfl fun c _ => by ring
  rw [Finset.sum_congr rfl e, Finset.sum_comm]
  exact Finset.sum_congr rfl fun c _ => by rw [Finset.sum_mul]

/-! ### A.3 Interpolation, the approximating processes, the telescoping bound -/

/-- `clamp x = max 0 (min 1 x)`. -/
def clamp (x : ℝ) : ℝ := max 0 (min 1 x)

theorem clamp_nonneg (x : ℝ) : 0 ≤ clamp x := le_max_left _ _

theorem clamp_le_one (x : ℝ) : clamp x ≤ 1 :=
  max_le zero_le_one (min_le_left _ _)

theorem continuous_clamp : Continuous clamp := by unfold clamp; fun_prop

theorem clamp_of_nonpos {x : ℝ} (hx : x ≤ 0) : clamp x = 0 := by
  simp [clamp, hx]

theorem clamp_of_one_le {x : ℝ} (hx : 1 ≤ x) : clamp x = 1 := by
  simp [clamp, hx]

theorem clamp_mono : Monotone clamp := fun _ _ h =>
  max_le_max le_rfl (min_le_min le_rfl h)

theorem clamp_half (x : ℝ) : clamp (x / 2) = (clamp x + clamp (x - 1)) / 2 := by
  simp only [clamp, min_def, max_def]
  split_ifs <;> linarith

/-- Piecewise-linear interpolation of the partial sums of `D` on the level-`N` grid. -/
def interp (D : ℕ → ℝ) (N : ℕ) (t : ℝ) : ℝ :=
  ∑ i ∈ Finset.range (⌊(2 : ℝ) ^ N * t⌋₊ + 1), D i * clamp ((2 : ℝ) ^ N * t - i)

theorem interp_eq_sum (D : ℕ → ℝ) (N : ℕ) (t : ℝ) {n : ℕ} (hn : ⌊(2 : ℝ) ^ N * t⌋₊ + 1 ≤ n) :
    interp D N t = ∑ i ∈ Finset.range n, D i * clamp ((2 : ℝ) ^ N * t - i) := by
  unfold interp
  apply Finset.sum_subset
  · intro i hi; simp only [Finset.mem_range] at hi ⊢; omega
  · intro i _ hi
    have h1 := Nat.lt_floor_add_one ((2 : ℝ) ^ N * t)
    have h2 : (⌊(2 : ℝ) ^ N * t⌋₊ + 1 : ℕ) ≤ i := by
      simpa [Finset.mem_range] using hi
    have h3 : ((⌊(2 : ℝ) ^ N * t⌋₊ + 1 : ℕ) : ℝ) ≤ i := by exact_mod_cast h2
    push_cast at h3
    rw [clamp_of_nonpos (by linarith), mul_zero]

theorem continuous_interp (D : ℕ → ℝ) (N : ℕ) : Continuous (interp D N) := by
  rw [continuous_iff_continuousAt]
  intro t
  set n := ⌊(2 : ℝ) ^ N * t⌋₊ + 1 with hn
  have hlt : (2 : ℝ) ^ N * t < n := by rw [hn]; push_cast; exact Nat.lt_floor_add_one _
  have hcont : Continuous fun s : ℝ => ∑ i ∈ Finset.range n, D i * clamp ((2 : ℝ) ^ N * s - i) := by
    apply continuous_finsetSum; intro i _
    exact continuous_const.mul (continuous_clamp.comp (by fun_prop))
  refine hcont.continuousAt.congr ?_
  have hopen : ∀ᶠ s in 𝓝 t, (2 : ℝ) ^ N * s < n :=
    (continuous_const.mul continuous_id).continuousAt.eventually (Iio_mem_nhds hlt)
  filter_upwards [hopen] with s hs
  refine (interp_eq_sum D N s ?_).symm
  have : ⌊(2 : ℝ) ^ N * s⌋₊ < n := (Nat.floor_lt' (by omega)).2 hs
  omega

theorem interp_grid (D : ℕ → ℝ) (N k : ℕ) :
    interp D N ((k : ℝ) / 2 ^ N) = ∑ i ∈ Finset.range k, D i := by
  have hx : (2 : ℝ) ^ N * ((k : ℝ) / 2 ^ N) = k := by field_simp
  rw [interp_eq_sum D N _ (n := k + 1) (by rw [hx, Nat.floor_natCast]), hx, Finset.sum_range_succ]
  simp only [sub_self, clamp_of_nonpos le_rfl, mul_zero, add_zero]
  refine Finset.sum_congr rfl fun i hi => ?_
  have : (i : ℝ) + 1 ≤ k := by exact_mod_cast Finset.mem_range.1 hi
  rw [clamp_of_one_le (by linarith), mul_one]

theorem interp_zero (D : ℕ → ℝ) (N : ℕ) : interp D N 0 = 0 := by
  simpa using interp_grid D N 0

/-- The level-`N` approximation, indexed by `ℝ≥0`. -/
def lcApprox (N : ℕ) (t : ℝ≥0) (ω : WienerSeq) : ℝ := interp (fun i => lcIncr N i ω) N t

theorem measurable_lcApprox (N : ℕ) (t : ℝ≥0) : Measurable (lcApprox N t) := by
  unfold lcApprox interp
  exact Finset.measurable_sum _ fun i _ => (measurable_lcIncr N i).mul_const _

theorem continuous_lcApprox (N : ℕ) (ω : WienerSeq) : Continuous fun t : ℝ≥0 => lcApprox N t ω :=
  (continuous_interp _ _).comp NNReal.continuous_coe

theorem lcApprox_zero (N : ℕ) (ω : WienerSeq) : lcApprox N 0 ω = 0 := by
  simpa [lcApprox] using interp_zero (fun i => lcIncr N i ω) N

theorem lcApprox_grid (N k : ℕ) (ω : WienerSeq) :
    lcApprox N ((k : ℝ≥0) / 2 ^ N) ω = ∑ i ∈ Finset.range k, lcIncr N i ω := by
  unfold lcApprox
  have : (((k : ℝ≥0) / 2 ^ N : ℝ≥0) : ℝ) = (k : ℝ) / 2 ^ N := by simp
  rw [this]
  exact interp_grid (fun i => lcIncr N i ω) N k

theorem sum_lcIncr_pow (N k m : ℕ) (ω : WienerSeq) :
    ∑ i ∈ Finset.range (k * 2 ^ m), lcIncr (N + m) i ω = ∑ i ∈ Finset.range k, lcIncr N i ω := by
  induction m with
  | zero => simp
  | succ m ih =>
    rw [show k * 2 ^ (m + 1) = 2 * (k * 2 ^ m) by ring, sum_range_two_mul, ← ih]
    exact Finset.sum_congr rfl fun p _ => lcIncr_even_add_odd (N + m) p ω

theorem lcApprox_grid_pow (N k m : ℕ) (ω : WienerSeq) :
    lcApprox (N + m) ((k : ℝ≥0) / 2 ^ N) ω = lcApprox N ((k : ℝ≥0) / 2 ^ N) ω := by
  have h : ((k : ℝ≥0) / 2 ^ N) = ((k * 2 ^ m : ℕ) : ℝ≥0) / 2 ^ (N + m) := by
    rw [pow_add]; push_cast
    field_simp
  rw [h, lcApprox_grid, sum_lcIncr_pow, ← lcApprox_grid, ← h]

/-- The tent of level-`N` cell `i`, in the variable `x = 2^{N+1} t`. -/
def tent (i : ℕ) (x : ℝ) : ℝ := clamp (x - 2 * i) - clamp (x - 2 * i - 1)

theorem tent_nonneg (i : ℕ) (x : ℝ) : 0 ≤ tent i x :=
  sub_nonneg.2 (clamp_mono (by linarith))

theorem tent_le_one (i : ℕ) (x : ℝ) : tent i x ≤ 1 := by
  unfold tent; linarith [clamp_le_one (x - 2 * i), clamp_nonneg (x - 2 * i - 1)]

theorem sum_tent_le (n : ℕ) (x : ℝ) : ∑ i ∈ Finset.range n, tent i x ≤ 1 := by
  have h : ∀ i ∈ Finset.range n, tent i x ≤ clamp (x - 2 * i) - clamp (x - 2 * ((i + 1 : ℕ) : ℝ)) := by
    intro i _
    unfold tent
    have : clamp (x - 2 * ((i + 1 : ℕ) : ℝ)) ≤ clamp (x - 2 * i - 1) :=
      clamp_mono (by push_cast; linarith)
    linarith
  refine (Finset.sum_le_sum h).trans ?_
  rw [Finset.sum_range_sub' (fun i : ℕ => clamp (x - 2 * (i : ℝ)))]
  simp only [Nat.cast_zero, mul_zero, sub_zero]
  linarith [clamp_le_one x, clamp_nonneg (x - 2 * (n : ℝ))]

/-- The telescoping identity. -/
theorem lcApprox_succ_sub (N : ℕ) (t : ℝ≥0) (ω : WienerSeq) {n : ℕ}
    (hn : ⌊(2 : ℝ) ^ N * t⌋₊ + 1 ≤ n) :
    lcApprox (N + 1) t ω - lcApprox N t ω =
      lcAmp N * ∑ i ∈ Finset.range n, ω (N + 1, i) * tent i ((2 : ℝ) ^ (N + 1) * t) := by
  set y : ℝ := (2 : ℝ) ^ N * t with hy
  have hx : (2 : ℝ) ^ (N + 1) * t = 2 * y := by rw [hy, pow_succ]; ring
  have h1 : ⌊(2 : ℝ) ^ (N + 1) * t⌋₊ + 1 ≤ 2 * n := by
    rw [hx]
    have : ⌊2 * y⌋₊ < 2 * ⌊y⌋₊ + 2 := (Nat.floor_lt' (by omega)).2 (by
      push_cast; linarith [Nat.lt_floor_add_one y])
    omega
  unfold lcApprox
  rw [interp_eq_sum _ _ _ h1, interp_eq_sum _ _ _ hn, sum_range_two_mul, ← Finset.sum_sub_distrib,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => ?_
  have hc : clamp (y - i) = (clamp (2 * y - 2 * i) + clamp (2 * y - 2 * i - 1)) / 2 := by
    have := clamp_half (2 * y - 2 * i)
    rwa [show (2 * y - 2 * i) / 2 = y - i by ring] at this
  rw [lcIncr_even, lcIncr_odd, hc, hx]
  unfold tent
  push_cast
  rw [show 2 * y - (2 * (i : ℝ) + 1) = 2 * y - 2 * i - 1 by ring]
  ring

theorem lcAmp_le_two_pow (N : ℕ) : lcAmp N ≤ (2 : ℝ) ^ (-(N : ℝ) / 2) := by
  unfold lcAmp
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)

/-- `ε_N = 2^{N/3}`, the cut-off of the pointwise inequality `|y| ≤ ε + y⁴/ε³`. -/
def lcEps (N : ℕ) : ℝ := (2 : ℝ) ^ ((N : ℝ) / 3)

theorem lcEps_pos (N : ℕ) : 0 < lcEps N := Real.rpow_pos_of_pos (by norm_num) _

theorem lcEps_cube (N : ℕ) : lcEps N ^ 3 = 2 ^ N := by
  unfold lcEps
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  rw [show (N : ℝ) / 3 * ((3 : ℕ) : ℝ) = (N : ℕ) by push_cast; ring, Real.rpow_natCast]

theorem abs_le_add_pow_four_div (y : ℝ) {ε : ℝ} (hε : 0 < ε) : |y| ≤ ε + y ^ 4 / ε ^ 3 := by
  have h4 : 0 ≤ y ^ 4 / ε ^ 3 := by positivity
  by_cases h : |y| ≤ ε
  · linarith
  · push Not at h
    have : |y| * ε ^ 3 ≤ y ^ 4 := by
      have e : y ^ 4 = |y| ^ 4 := by
        rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
      rw [e]
      have h1 : ε ^ 3 ≤ |y| ^ 3 := pow_le_pow_left₀ hε.le h.le 3
      calc |y| * ε ^ 3 ≤ |y| * |y| ^ 3 := mul_le_mul_of_nonneg_left h1 (abs_nonneg _)
        _ = |y| ^ 4 := by ring
    have : |y| ≤ y ^ 4 / ε ^ 3 := by rw [le_div_iff₀ (by positivity)]; exact this
    linarith

/-- The random bound on `sup_{[0,L]} |X^{N+1} - X^N| / lcAmp N`. -/
def lcBound (N L : ℕ) (ω : WienerSeq) : ℝ :=
  lcEps N + ∑ i ∈ Finset.range (L * 2 ^ N + 1), ω (N + 1, i) ^ 4 / lcEps N ^ 3

theorem lcBound_nonneg (N L : ℕ) (ω : WienerSeq) : 0 ≤ lcBound N L ω := by
  have := lcEps_pos N
  unfold lcBound; positivity

theorem measurable_lcBound (N L : ℕ) : Measurable (lcBound N L) := by
  unfold lcBound
  exact measurable_const.add (Finset.measurable_sum _ fun i _ =>
    (((measurable_pi_apply (N + 1, i)).pow_const 4).div_const _))

theorem abs_le_lcBound (N L : ℕ) (t : ℝ≥0) (ht : t ≤ L) (ω : WienerSeq) :
    |lcApprox (N + 1) t ω - lcApprox N t ω| ≤ lcAmp N * lcBound N L ω := by
  have hε := lcEps_pos N
  have hn : ⌊(2 : ℝ) ^ N * t⌋₊ + 1 ≤ L * 2 ^ N + 1 := by
    have : ⌊(2 : ℝ) ^ N * t⌋₊ ≤ L * 2 ^ N := by
      apply Nat.floor_le_of_le
      have : (t : ℝ) ≤ L := by exact_mod_cast ht
      push_cast
      nlinarith [pow_pos (two_pos : (0 : ℝ) < 2) N]
    omega
  rw [lcApprox_succ_sub N t ω hn, abs_mul, abs_of_pos (lcAmp_pos N)]
  refine mul_le_mul_of_nonneg_left ?_ (lcAmp_pos N).le
  set x : ℝ := (2 : ℝ) ^ (N + 1) * t
  set n := L * 2 ^ N + 1
  calc |∑ i ∈ Finset.range n, ω (N + 1, i) * tent i x|
      ≤ ∑ i ∈ Finset.range n, |ω (N + 1, i) * tent i x| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i ∈ Finset.range n, (lcEps N * tent i x + ω (N + 1, i) ^ 4 / lcEps N ^ 3) := by
        refine Finset.sum_le_sum fun i _ => ?_
        rw [abs_mul, abs_of_nonneg (tent_nonneg i x)]
        have := abs_le_add_pow_four_div (ω (N + 1, i)) hε
        have h1 := tent_nonneg i x
        have h2 := tent_le_one i x
        have h3 : 0 ≤ ω (N + 1, i) ^ 4 / lcEps N ^ 3 := by positivity
        nlinarith
    _ = lcEps N * ∑ i ∈ Finset.range n, tent i x +
          ∑ i ∈ Finset.range n, ω (N + 1, i) ^ 4 / lcEps N ^ 3 := by
        rw [Finset.sum_add_distrib, Finset.mul_sum]
    _ ≤ lcBound N L ω := by
        unfold lcBound
        have := sum_tent_le n x
        nlinarith

theorem integral_coord_pow_four (c : ℕ × ℕ) :
    ∫ ω, ω c ^ 4 ∂wienerMeasure = 3 := by
  have h := (hasLaw_coord c).integral_comp (f := fun x : ℝ => x ^ 4) (by fun_prop)
  rw [integral_pow_four_gaussianReal_zero] at h
  simpa using h

theorem integrable_coord_pow_four (c : ℕ × ℕ) :
    Integrable (fun ω : WienerSeq => ω c ^ 4) wienerMeasure := by
  have hint : Integrable (fun x : ℝ => x ^ 4) (gaussianReal 0 1) := by
    have h := (memLp_id_gaussianReal (μ := 0) (v := 1) 4).integrable_norm_pow (p := 4) (by norm_num)
    refine h.congr (Filter.Eventually.of_forall fun x => ?_)
    simp only [id, Real.norm_eq_abs]
    rw [show (4 : ℕ) = 2 * 2 from rfl, pow_mul, pow_mul, sq_abs]
  exact (hasLaw_coord c).integrable_comp hint

theorem integrable_lcBound (N L : ℕ) : Integrable (lcBound N L) wienerMeasure := by
  unfold lcBound
  exact (integrable_const _).add (integrable_finsetSum _ fun i _ =>
    (integrable_coord_pow_four (N + 1, i)).div_const _)

theorem integral_lcBound (N L : ℕ) :
    ∫ ω, lcBound N L ω ∂wienerMeasure = lcEps N + ((L * 2 ^ N + 1 : ℕ) : ℝ) * (3 / lcEps N ^ 3) := by
  unfold lcBound
  rw [integral_add (integrable_const _) (integrable_finsetSum _ fun i _ =>
    (integrable_coord_pow_four (N + 1, i)).div_const _), integral_const,
    integral_finsetSum _ fun i _ => (integrable_coord_pow_four (N + 1, i)).div_const _]
  simp [integral_div, integral_coord_pow_four]

/-- The geometric rate `2^{-1/6}` dominating all series below. -/
def lcRate : ℝ := (2 : ℝ) ^ (-(1 : ℝ) / 6)

theorem lcRate_pos : 0 < lcRate := Real.rpow_pos_of_pos (by norm_num) _

theorem lcRate_lt_one : lcRate < 1 :=
  Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by norm_num)

theorem lcRate_pow (N : ℕ) : lcRate ^ N = (2 : ℝ) ^ (-(N : ℝ) / 6) := by
  unfold lcRate
  rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
  congr 1; ring

theorem lcAmp_le_lcRate_pow (N : ℕ) : lcAmp N ≤ lcRate ^ N := by
  rw [lcRate_pow]
  unfold lcAmp
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])

theorem lcAmp_mul_lcEps_le (N : ℕ) : lcAmp N * lcEps N ≤ lcRate ^ N := by
  rw [lcRate_pow]
  unfold lcAmp lcEps
  rw [← Real.rpow_add (by norm_num)]
  exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith [(Nat.cast_nonneg N : (0 : ℝ) ≤ N)])

theorem summable_lcAmp_mul_integral (L : ℕ) :
    Summable fun N => lcAmp N * ∫ ω, lcBound N L ω ∂wienerMeasure := by
  have hg : Summable fun N : ℕ => (1 + 3 * ((L : ℝ) + 1)) * lcRate ^ N :=
    (summable_geometric_of_lt_one lcRate_pos.le lcRate_lt_one).mul_left _
  refine Summable.of_nonneg_of_le (fun N => ?_) (fun N => ?_) hg
  · rw [integral_lcBound]
    have := lcAmp_pos N; have := lcEps_pos N
    positivity
  · rw [integral_lcBound, lcEps_cube, mul_add]
    have h1 := lcAmp_mul_lcEps_le N
    have h2 := lcAmp_le_lcRate_pow N
    have h3 : ((L * 2 ^ N + 1 : ℕ) : ℝ) * (3 / 2 ^ N) ≤ 3 * ((L : ℝ) + 1) := by
      have hp : (1 : ℝ) ≤ 2 ^ N := one_le_pow₀ (by norm_num)
      push_cast
      rw [mul_div_assoc', div_le_iff₀ (by positivity)]
      have : (3 : ℝ) ≤ 3 * 2 ^ N := by nlinarith
      nlinarith [(Nat.cast_nonneg L : (0 : ℝ) ≤ L)]
    have h4 : lcAmp N * (((L * 2 ^ N + 1 : ℕ) : ℝ) * (3 / 2 ^ N)) ≤ 3 * ((L : ℝ) + 1) * lcRate ^ N := by
      calc _ ≤ lcAmp N * (3 * ((L : ℝ) + 1)) := mul_le_mul_of_nonneg_left h3 (lcAmp_pos N).le
        _ = 3 * ((L : ℝ) + 1) * lcAmp N := by ring
        _ ≤ _ := mul_le_mul_of_nonneg_left h2 (by positivity)
    nlinarith

/-! ### A.4 Almost-sure uniform convergence, continuity, the limit process -/

theorem ae_summable_lcBound_fixed (L : ℕ) :
    ∀ᵐ ω ∂wienerMeasure, Summable fun N => lcAmp N * lcBound N L ω := by
  set g : ℕ → WienerSeq → ℝ := fun N ω => lcAmp N * lcBound N L ω with hg
  have hgm : ∀ N, Measurable (g N) := fun N => measurable_const.mul (measurable_lcBound N L)
  have hgi : ∀ N, Integrable (g N) wienerMeasure := fun N =>
    (integrable_lcBound N L).const_mul _
  have hg0 : ∀ N ω, 0 ≤ g N ω := fun N ω => mul_nonneg (lcAmp_pos N).le (lcBound_nonneg N L ω)
  have hF : ∀ N, ∫⁻ ω, ENNReal.ofReal (g N ω) ∂wienerMeasure =
      ENNReal.ofReal (lcAmp N * ∫ ω, lcBound N L ω ∂wienerMeasure) := by
    intro N
    rw [← ofReal_integral_eq_lintegral_ofReal (hgi N) (Filter.Eventually.of_forall (hg0 N)),
      hg]
    simp only
    rw [integral_const_mul]
  have hnn : ∀ N, 0 ≤ lcAmp N * ∫ ω, lcBound N L ω ∂wienerMeasure := fun N =>
    mul_nonneg (lcAmp_pos N).le (integral_nonneg (lcBound_nonneg N L))
  have hsum : ∑' N, ENNReal.ofReal (lcAmp N * ∫ ω, lcBound N L ω ∂wienerMeasure) ≠ ∞ := by
    rw [← ENNReal.ofReal_tsum_of_nonneg hnn (summable_lcAmp_mul_integral L)]
    exact ENNReal.ofReal_ne_top
  have hlint : ∫⁻ ω, ∑' N, ENNReal.ofReal (g N ω) ∂wienerMeasure ≠ ∞ := by
    have := lintegral_tsum (μ := wienerMeasure) (f := fun N ω => ENNReal.ofReal (g N ω))
      (fun N => (ENNReal.measurable_ofReal.comp (hgm N)).aemeasurable)
    rw [this]
    simp_rw [hF]; exact hsum
  have hae := ae_lt_top (Measurable.tsum fun N => ENNReal.measurable_ofReal.comp (hgm N))
    hlint
  filter_upwards [hae] with ω hω
  have := ENNReal.summable_toReal hω.ne
  refine this.congr fun N => ?_
  exact ENNReal.toReal_ofReal (hg0 N ω)

/-- The a.s. summability of the bounds, for every `L` simultaneously. -/
theorem ae_summable_lcBound :
    ∀ᵐ ω ∂wienerMeasure, ∀ L : ℕ, Summable fun N => lcAmp N * lcBound N L ω :=
  ae_all_iff.2 ae_summable_lcBound_fixed

/-- The raw limit (junk off the good set). -/
def lcLimit (t : ℝ≥0) (ω : WienerSeq) : ℝ := limUnder atTop fun N => lcApprox N t ω

theorem measurable_lcLimit (t : ℝ≥0) : Measurable (lcLimit t) :=
  (StronglyMeasurable.limUnder fun N => (measurable_lcApprox N t).stronglyMeasurable).measurable

theorem tendstoUniformlyOn_lcApprox {ω : WienerSeq}
    (h : ∀ L : ℕ, Summable fun N => lcAmp N * lcBound N L ω) (L : ℕ) :
    TendstoUniformlyOn (fun N (t : ℝ≥0) => lcApprox N t ω) (fun t => lcLimit t ω) atTop
      (Set.Icc 0 (L : ℝ≥0)) := by
  set u : ℕ → ℝ≥0 → ℝ := fun K t => lcApprox (K + 1) t ω - lcApprox K t ω with hu
  have hM := tendstoUniformlyOn_tsum_nat (f := u) (s := Set.Icc 0 (L : ℝ≥0)) (h L) (by
    intro K t ht
    rw [Real.norm_eq_abs]
    exact abs_le_lcBound K L t ht.2 ω)
  have hsplit : ∀ N t, lcApprox N t ω = lcApprox 0 t ω + ∑ K ∈ Finset.range N, u K t := by
    intro N t
    rw [hu]; simp only
    rw [Finset.sum_range_sub (fun K => lcApprox K t ω)]; ring
  have hlim : ∀ t ∈ Set.Icc 0 (L : ℝ≥0),
      lcLimit t ω = lcApprox 0 t ω + ∑' K, u K t := by
    intro t ht
    have := hM.tendsto_at ht
    have h2 : Tendsto (fun N => lcApprox N t ω) atTop (𝓝 (lcApprox 0 t ω + ∑' K, u K t)) := by
      have e : (fun N => lcApprox N t ω) =
          fun N => lcApprox 0 t ω + ∑ K ∈ Finset.range N, u K t := funext fun N => hsplit N t
      rw [e]
      exact tendsto_const_nhds.add this
    exact h2.limUnder_eq
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  filter_upwards [Metric.tendstoUniformlyOn_iff.1 hM ε hε] with N hN t ht
  rw [hlim t ht, hsplit N t, dist_add_left]
  exact hN t ht

theorem ae_continuous_lcLimit : ∀ᵐ ω ∂wienerMeasure, Continuous fun t => lcLimit t ω := by
  filter_upwards [ae_summable_lcBound] with ω hω
  rw [continuous_iff_continuousAt]
  intro t
  set L : ℕ := ⌈(t : ℝ)⌉₊ + 1
  have hco : ContinuousOn (fun t => lcLimit t ω) (Set.Icc 0 (L : ℝ≥0)) :=
    (tendstoUniformlyOn_lcApprox hω L).continuousOn (Filter.Eventually.frequently
      (Filter.Eventually.of_forall fun N => (continuous_lcApprox N ω).continuousOn))
  have hnhds : Set.Icc 0 (L : ℝ≥0) ∈ 𝓝 t := by
    have : Set.Icc (0 : ℝ≥0) (L : ℝ≥0) = Set.Iic (L : ℝ≥0) := by
      ext s; simp
    rw [this]
    refine Iic_mem_nhds ?_
    rw [← NNReal.coe_lt_coe]
    push_cast
    have := Nat.le_ceil (t : ℝ)
    simp only [L]; push_cast; linarith
  exact hco.continuousAt hnhds

theorem lcLimit_grid (N k : ℕ) (ω : WienerSeq) :
    lcLimit ((k : ℝ≥0) / 2 ^ N) ω = ∑ i ∈ Finset.range k, lcIncr N i ω := by
  have : Tendsto (fun M => lcApprox M ((k : ℝ≥0) / 2 ^ N) ω) atTop
      (𝓝 (∑ i ∈ Finset.range k, lcIncr N i ω)) := by
    refine tendsto_const_nhds.congr' ?_
    refine Filter.eventually_atTop.2 ⟨N, fun M hM => ?_⟩
    obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hM
    show ∑ i ∈ Finset.range k, lcIncr N i ω = lcApprox (N + m) ((k : ℝ≥0) / 2 ^ N) ω
    rw [lcApprox_grid_pow, lcApprox_grid]
  exact this.limUnder_eq

theorem lcLimit_zero (ω : WienerSeq) : lcLimit 0 ω = 0 := by
  have := lcLimit_grid 0 0 ω
  simpa using this

/-- The everywhere continuous, measurable modification (before centring). -/
def wienerPathAux : ℝ≥0 → WienerSeq → ℝ :=
  Classical.choose (exists_continuous_modification wienerMeasure lcLimit measurable_lcLimit
    ae_continuous_lcLimit)

theorem measurable_wienerPathAux (t : ℝ≥0) : Measurable (wienerPathAux t) :=
  (Classical.choose_spec (exists_continuous_modification wienerMeasure lcLimit measurable_lcLimit
    ae_continuous_lcLimit)).1 t

theorem continuous_wienerPathAux (ω : WienerSeq) : Continuous fun t => wienerPathAux t ω :=
  (Classical.choose_spec (exists_continuous_modification wienerMeasure lcLimit measurable_lcLimit
    ae_continuous_lcLimit)).2.1 ω

theorem ae_wienerPathAux_eq : ∀ᵐ ω ∂wienerMeasure, ∀ t, wienerPathAux t ω = lcLimit t ω :=
  (Classical.choose_spec (exists_continuous_modification wienerMeasure lcLimit measurable_lcLimit
    ae_continuous_lcLimit)).2.2

/-- The Lévy–Ciesielski process (everywhere continuous, `W 0 = 0`). -/
def wienerPath : ℝ≥0 → WienerSeq → ℝ := fun t ω => wienerPathAux t ω - wienerPathAux 0 ω

theorem wienerPath_zero (ω : WienerSeq) : wienerPath 0 ω = 0 := by
  simp [wienerPath]

theorem continuous_wienerPath (ω : WienerSeq) : Continuous fun t => wienerPath t ω :=
  (continuous_wienerPathAux ω).sub continuous_const

theorem measurable_wienerPath (t : ℝ≥0) : Measurable (wienerPath t) :=
  (measurable_wienerPathAux t).sub (measurable_wienerPathAux 0)

theorem ae_wienerPath_eq : ∀ᵐ ω ∂wienerMeasure, ∀ t, wienerPath t ω = lcLimit t ω := by
  filter_upwards [ae_wienerPathAux_eq] with ω h t
  simp only [wienerPath, h t, h 0, lcLimit_zero, sub_zero]

theorem ae_wienerPath_grid (N k : ℕ) :
    ∀ᵐ ω ∂wienerMeasure, wienerPath ((k : ℝ≥0) / 2 ^ N) ω = ∑ i ∈ Finset.range k, lcIncr N i ω := by
  filter_upwards [ae_wienerPath_eq] with ω h
  rw [h, lcLimit_grid]

/-! ### A.5 Finite-dimensional laws -/

theorem sum_range_ite_lt (n m : ℕ) (f : ℕ → ℝ) (h : m ≤ n) :
    ∑ i ∈ Finset.range n, (if i < m then f i else 0) = ∑ i ∈ Finset.range m, f i := by
  rw [← Finset.sum_subset (Finset.range_mono h)]
  · exact Finset.sum_congr rfl fun i hi => by simp [Finset.mem_range.1 hi]
  · intro i _ hi
    simp [show ¬ i < m from fun h' => hi (Finset.mem_range.2 h')]

theorem hasLaw_wienerPath_dyadic (I : Finset ℝ≥0) (θ : I → ℝ) (N : ℕ) :
    HasLaw (fun ω => ∑ t : I, θ t * wienerPath (dyadicFloor N t) ω)
      (gaussianReal 0 (Real.toNNReal (∑ s : I, ∑ t : I,
        θ s * θ t * min (dyadicFloor N s : ℝ) (dyadicFloor N t)))) wienerMeasure := by
  set k : I → ℕ := fun t => ⌊((t : ℝ≥0) : ℝ) * 2 ^ N⌋₊ with hk
  set n : ℕ := ∑ t, k t with hn
  have hkn : ∀ t, k t ≤ n := fun t =>
    Finset.single_le_sum (f := k) (fun _ _ => Nat.zero_le _) (Finset.mem_univ t)
  set ϑ : ℕ → ℝ := fun i => ∑ t : I, if i < k t then θ t else 0 with hϑ
  have h1 := hasLaw_lcIncr_sum N n ϑ
  have hdf : ∀ t : I, dyadicFloor N t = ((k t : ℕ) : ℝ≥0) / 2 ^ N := fun t => rfl
  have hae : ∀ᵐ ω ∂wienerMeasure, ∀ t : I,
      wienerPath (dyadicFloor N t) ω = ∑ i ∈ Finset.range (k t), lcIncr N i ω :=
    ae_all_iff.2 fun t => by rw [hdf]; exact ae_wienerPath_grid N (k t)
  have hvar : (2 : ℝ)⁻¹ ^ N * ∑ i ∈ Finset.range n, ϑ i ^ 2 =
      ∑ s : I, ∑ t : I, θ s * θ t * min (dyadicFloor N s : ℝ) (dyadicFloor N t) := by
    have e1 : ∀ i, ϑ i ^ 2 = ∑ s : I, ∑ t : I,
        (if i < min (k s) (k t) then θ s * θ t else 0) := by
      intro i
      rw [hϑ]; simp only
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      by_cases h1 : i < k s <;> by_cases h2 : i < k t <;> simp [h1, h2, lt_min_iff]
    simp_rw [e1]
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun s _ => ?_
    rw [Finset.sum_comm, Finset.mul_sum]
    refine Finset.sum_congr rfl fun t _ => ?_
    have hmn : min (k s) (k t) ≤ n := (min_le_left _ _).trans (hkn s)
    rw [sum_range_ite_lt n _ (fun _ => θ s * θ t) hmn]
    simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
    rw [hdf s, hdf t]
    simp only [NNReal.coe_div, NNReal.coe_natCast, NNReal.coe_pow, NNReal.coe_ofNat]
    rw [Nat.cast_min, min_div_div_right (by positivity)]
    have : (2 : ℝ)⁻¹ ^ N = 1 / 2 ^ N := by rw [one_div, inv_pow]
    rw [this]
    field_simp
  rw [← hvar]
  refine h1.congr ?_
  filter_upwards [hae] with ω hω
  simp only [hω]
  have e2 : ∀ t : I, θ t * ∑ i ∈ Finset.range (k t), lcIncr N i ω =
      ∑ i ∈ Finset.range n, (if i < k t then θ t else 0) * lcIncr N i ω := by
    intro t
    have := sum_range_ite_lt n (k t) (fun i => θ t * lcIncr N i ω) (hkn t)
    rw [Finset.mul_sum, ← this]
    exact Finset.sum_congr rfl fun i _ => by split_ifs <;> simp
  rw [Finset.sum_congr rfl fun t _ => e2 t, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [hϑ]; simp only [Finset.sum_mul]

/-- Pointwise convergence of random variables gives convergence of characteristic functions. -/
theorem tendsto_charFun_map {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (Z : ℕ → Ω → ℝ) (Z' : Ω → ℝ) (hm : ∀ N, Measurable (Z N)) (hm' : Measurable Z')
    (h : ∀ ω, Tendsto (fun N => Z N ω) atTop (𝓝 (Z' ω))) (u : ℝ) :
    Tendsto (fun N => charFun (P.map (Z N)) u) atTop (𝓝 (charFun (P.map Z') u)) := by
  have e : ∀ f : Ω → ℝ, Measurable f → charFun (P.map f) u =
      ∫ ω, Complex.exp (((u * f ω : ℝ) : ℂ) * Complex.I) ∂P := by
    intro f hf
    rw [charFun_apply_real, integral_map hf.aemeasurable (by fun_prop)]
    simp only [Complex.ofReal_mul]
  simp_rw [e _ (hm _), e _ hm']
  refine tendsto_integral_of_dominated_convergence (fun _ => 1) (fun N => ?_) (integrable_const _)
    (fun N => Filter.Eventually.of_forall fun ω => ?_) (Filter.Eventually.of_forall fun ω => ?_)
  · exact (by have := hm N; fun_prop : Measurable fun ω => Complex.exp (((u * Z N ω : ℝ) : ℂ) * Complex.I)).aestronglyMeasurable
  · rw [Complex.norm_exp_ofReal_mul_I]
  · exact (Complex.continuous_exp.tendsto _).comp
      (((Complex.continuous_ofReal.tendsto _).comp (tendsto_const_nhds.mul (h ω))).mul_const _)

theorem hasLaw_wienerPath_comb (I : Finset ℝ≥0) (θ : I → ℝ) :
    HasLaw (fun ω => ∑ t : I, θ t * wienerPath t ω)
      (gaussianReal 0 (Real.toNNReal (∑ s : I, ∑ t : I, θ s * θ t * min ((s : ℝ≥0) : ℝ) (t : ℝ≥0))))
      wienerMeasure := by
  set Z : WienerSeq → ℝ := fun ω => ∑ t : I, θ t * wienerPath t ω with hZ
  set ZN : ℕ → WienerSeq → ℝ := fun N ω => ∑ t : I, θ t * wienerPath (dyadicFloor N t) ω with hZN
  set vN : ℕ → ℝ := fun N => ∑ s : I, ∑ t : I,
    θ s * θ t * min (dyadicFloor N s : ℝ) (dyadicFloor N t) with hvN
  set v : ℝ := ∑ s : I, ∑ t : I, θ s * θ t * min ((s : ℝ≥0) : ℝ) (t : ℝ≥0) with hv
  have hZm : Measurable Z :=
    Finset.measurable_sum _ fun t _ => measurable_const.mul (measurable_wienerPath t)
  have hZNm : ∀ N, Measurable (ZN N) := fun N =>
    Finset.measurable_sum _ fun t _ => measurable_const.mul (measurable_wienerPath _)
  have hconv : ∀ ω, Tendsto (fun N => ZN N ω) atTop (𝓝 (Z ω)) := by
    intro ω
    refine tendsto_finsetSum _ fun t _ => tendsto_const_nhds.mul ?_
    exact ((continuous_wienerPath ω).tendsto _).comp (tendsto_dyadicFloor t)
  have hvlim : Tendsto vN atTop (𝓝 v) := by
    refine tendsto_finsetSum _ fun s _ => tendsto_finsetSum _ fun t _ =>
      tendsto_const_nhds.mul ?_
    exact (NNReal.tendsto_coe.2 (tendsto_dyadicFloor s)).min
      (NNReal.tendsto_coe.2 (tendsto_dyadicFloor t))
  refine ⟨hZm.aemeasurable, ?_⟩
  refine Measure.ext_of_charFun ?_
  funext u
  have h1 := tendsto_charFun_map wienerMeasure ZN Z hZNm hZm hconv u
  have h2 : ∀ N, charFun (wienerMeasure.map (ZN N)) u =
      charFun (gaussianReal 0 (vN N).toNNReal) u := fun N => by
    rw [(hasLaw_wienerPath_dyadic I θ N).map_eq]
  have hG : Continuous fun x : ℝ => charFun (gaussianReal 0 x.toNNReal) u := by
    simp only [charFun_gaussianReal]
    fun_prop
  have h3 : Tendsto (fun N => charFun (wienerMeasure.map (ZN N)) u) atTop
      (𝓝 (charFun (gaussianReal 0 v.toNNReal) u)) := by
    simp_rw [h2]
    exact (hG.tendsto v).comp hvlim
  exact tendsto_nhds_unique h1 h3

theorem isPreBrownianReal_wienerPath : IsPreBrownianReal wienerPath wienerMeasure := by
  refine ⟨fun I => ?_⟩
  set F : WienerSeq → EuclideanSpace ℝ I := fun ω => WithLp.toLp 2 (fun t : I => wienerPath t ω)
    with hF
  have hFm : Measurable F := (MeasurableEquiv.toLp 2 (I → ℝ)).measurable.comp
    (Measurable.of_eval fun t => measurable_wienerPath t)
  have hmap : wienerMeasure.map F = multivariateGaussian 0 (BrownianReal.covMatrix I) := by
    refine Measure.ext_of_charFun ?_
    funext θ
    rw [charFun_multivariateGaussian (BrownianReal.posSemidef_covMatrix I)]
    have hcomb := hasLaw_wienerPath_comb I (fun t => θ t)
    have hq : dotProduct θ.ofLp (Matrix.mulVec (BrownianReal.covMatrix I) θ.ofLp) =
        ∑ s : I, ∑ t : I, θ s * θ t * min ((s : ℝ≥0) : ℝ) (t : ℝ≥0) := by
      simp only [dotProduct, Matrix.mulVec, BrownianReal.covMatrix_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun s _ => Finset.sum_congr rfl fun t _ => ?_
      rw [NNReal.coe_min]; ring
    have hZm : Measurable fun ω => ∑ t : I, θ t * wienerPath t ω :=
      Finset.measurable_sum _ fun t _ => measurable_const.mul (measurable_wienerPath t)
    have hL : charFun (wienerMeasure.map F) θ =
        charFun (wienerMeasure.map (fun ω => ∑ t : I, θ t * wienerPath t ω)) 1 := by
      rw [charFun_apply, charFun_apply_real, integral_map hFm.aemeasurable (by fun_prop),
        integral_map hZm.aemeasurable (by fun_prop)]
      congr 1; funext ω
      have : inner ℝ (F ω) θ = ∑ t : I, θ t * wienerPath t ω := by
        simp [F, PiLp.inner_apply, mul_comm]
      rw [this]; simp
    have hnn : 0 ≤ ∑ s : I, ∑ t : I, θ s * θ t * min ((s : ℝ≥0) : ℝ) (t : ℝ≥0) := by
      rw [← hq]
      simpa using (BrownianReal.posSemidef_covMatrix I).dotProduct_mulVec_nonneg θ.ofLp
    rw [hL, hcomb.map_eq, charFun_gaussianReal, Real.coe_toNNReal _ hnn, ← hq]
    simp
  have hmap2 : wienerMeasure.map (fun ω => I.restrict (wienerPath · ω)) =
      BrownianReal.projectiveFamily I := by
    have : (fun ω => I.restrict (wienerPath · ω)) = WithLp.ofLp ∘ F := rfl
    rw [this, ← Measure.map_map (by fun_prop) hFm, hmap,
      (BrownianReal.measurePreserving_ofLp_multivariateGaussian I).map_eq]
  have hm : Measurable fun ω => I.restrict (wienerPath · ω) :=
    Measurable.of_eval fun t => measurable_wienerPath t
  exact ⟨hm.aemeasurable, hmap2⟩

theorem isBrownianReal_wienerPath : IsBrownianReal wienerPath wienerMeasure :=
  ⟨isPreBrownianReal_wienerPath, Filter.Eventually.of_forall continuous_wienerPath⟩

/-- (A2) for the CLT consumer, universe 0. -/
theorem exists_isBrownianReal :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (β : ℝ≥0 → Ω → ℝ), IsBrownianReal β P ∧ (∀ t, Measurable (β t)) ∧
      (∀ ω, Continuous fun t => β t ω) ∧ ∀ ω, β 0 ω = 0 :=
  ⟨WienerSeq, inferInstance, wienerMeasure, inferInstance, wienerPath, isBrownianReal_wienerPath,
    measurable_wienerPath, continuous_wienerPath, wienerPath_zero⟩

/-! ### A.6 Products and enlargement -/

/-- Transport of `IsBrownianReal` along a measure-preserving map (paths everywhere continuous). -/
theorem IsBrownianReal.comp_measurePreserving {Ω Ω' : Type*} [MeasurableSpace Ω]
    [MeasurableSpace Ω'] {P : Measure Ω} {P' : Measure Ω'} {f : Ω' → Ω}
    (hf : MeasurePreserving f P' P) {B : ℝ≥0 → Ω → ℝ} (hB : IsPreBrownianReal B P)
    (hc : ∀ ω, Continuous fun t => B t ω) :
    IsBrownianReal (fun t ω' => B t (f ω')) P' :=
  ⟨⟨fun I => (hB.hasLaw I).comp hf.hasLaw⟩, Filter.Eventually.of_forall fun ω' => hc (f ω')⟩

/-- Transport of joint independence along a measure-preserving map. -/
theorem iIndepFun_comp_measurePreserving {ι Ω Ω' 𝓧 : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MeasurableSpace Ω'] [MeasurableSpace 𝓧] {P : Measure Ω} {P' : Measure Ω'}
    [IsProbabilityMeasure P] [IsProbabilityMeasure P'] {f : Ω' → Ω}
    (hf : MeasurePreserving f P' P) {X : ι → Ω → 𝓧} (hX : ∀ i, Measurable (X i))
    (h : iIndepFun X P) : iIndepFun (fun i ω' => X i (f ω')) P' := by
  rw [iIndepFun_iff_map_fun_eq_pi_map (f := fun i ω' => X i (f ω'))
    (fun i => ((hX i).comp hf.measurable).aemeasurable)]
  have h1 := (iIndepFun_iff_map_fun_eq_pi_map (fun i => (hX i).aemeasurable)).1 h
  have hXm : Measurable fun ω i => X i ω := Measurable.of_eval hX
  have e1 : P'.map (fun ω' i => X i (f ω')) = P.map (fun ω i => X i ω) := by
    rw [← hf.map_eq, Measure.map_map hXm hf.measurable]; rfl
  have e2 : ∀ i, P'.map (fun ω' => X i (f ω')) = P.map (X i) := fun i => by
    rw [← hf.map_eq, Measure.map_map (hX i) hf.measurable]; rfl
  rw [e1, h1]
  simp_rw [e2]

/-- Brownian filtration generated by everywhere-continuous coordinatewise Brownian motions and an
independent datum (the tail of `exists_isBrownianFiltration`, without modification). -/
theorem isBrownianFiltration_generated {Ω E ι : Type*} [Fintype ι] [MeasurableSpace Ω]
    [MeasurableSpace E] (P : Measure Ω) [IsProbabilityMeasure P] (W : ℝ≥0 → Ω → ι → ℝ)
    (hW : ∀ t, Measurable (W t))
    (hB : ∀ k, IsBrownianReal (fun t ω => W t ω k) P)
    (hind : iIndepFun (fun (k : ι) ω => fun t : ℝ≥0 => W t ω k) P) (h0 : ∀ ω, W 0 ω = 0)
    (hc : ∀ ω, Continuous fun t => W t ω) (X₀ : Ω → E) (hX₀ : Measurable X₀)
    (hX₀W : IndepFun X₀ (fun ω => fun t => W t ω) P) :
    IsBrownianFiltration P (generatedFiltration P X₀ hX₀ W hW) W := by
  refine ⟨generatedFiltration_isComplete P X₀ hX₀ W hW,
    fun t => generatedFiltration_measurable_W P X₀ hX₀ W hW t t le_rfl, h0, hc,
    fun s t hst => indep_incr_generated P W hW hB hind X₀ hX₀ hX₀W s t hst, ?_⟩
  intro s t hst
  have hlaw : ∀ k, HasLaw (fun ω => W t ω k - W s ω k) (gaussianReal 0 (t - s)) P := fun k => by
    have h := (hB k).toIsPreBrownianReal.hasLaw_sub t s
    convert h using 2
    apply NNReal.eq
    rw [coe_nndist, NNReal.coe_sub hst, Real.dist_eq, abs_of_nonneg]
    · rfl
    · simp [hst]
  have hi : iIndepFun (fun (k : ι) ω => W t ω k - W s ω k) P :=
    hind.comp (fun _ (p : ℝ≥0 → ℝ) => p t - p s)
      (fun _ => ((measurable_pi_apply t).sub (measurable_pi_apply s)))
  exact (iIndepFun_iff_hasLaw_pi_pi hlaw).1 hi

/-- (A3): enlargement of a probability space `(E, μ)` in `Type` by `card ι` independent Brownian
motions, independent of the identity of `E`.  `Ω' = E × (ι → WienerSeq)`. -/
theorem exists_enlargement (ι : Type) [Fintype ι] (E : Type) [MeasurableSpace E] (μ : Measure E)
    [IsProbabilityMeasure μ] :
    ∃ (W : ℝ≥0 → E × (ι → WienerSeq) → ι → ℝ) (hW : ∀ t, Measurable (W t)),
      Measure.map Prod.fst (μ.prod (Measure.pi fun _ : ι => wienerMeasure)) = μ ∧
      (∀ ω, W 0 ω = 0) ∧ (∀ ω, Continuous fun t => W t ω) ∧
      IsBrownianFiltration (μ.prod (Measure.pi fun _ : ι => wienerMeasure))
        (generatedFiltration (μ.prod (Measure.pi fun _ : ι => wienerMeasure))
          Prod.fst measurable_fst W hW) W := by
  set ν : Measure (ι → WienerSeq) := Measure.pi fun _ : ι => wienerMeasure with hν
  set W : ℝ≥0 → E × (ι → WienerSeq) → ι → ℝ := fun t p k => wienerPath t (p.2 k) with hWdef
  have hW : ∀ t, Measurable (W t) := fun t =>
    Measurable.of_eval fun k => (measurable_wienerPath t).comp
      ((measurable_pi_apply k).comp measurable_snd)
  have hW0 : ∀ ω, W 0 ω = 0 := fun ω => funext fun k => wienerPath_zero _
  have hWc : ∀ ω, Continuous fun t => W t ω := fun ω =>
    continuous_pi fun k => continuous_wienerPath _
  refine ⟨W, hW, ?_, hW0, hWc, ?_⟩
  · rw [Measure.map_fst_prod, measure_univ, one_smul]
  · have hsnd : MeasurePreserving (fun p : E × (ι → WienerSeq) => p.2) (μ.prod ν) ν :=
      measurePreserving_snd
    have hev : ∀ k : ι, MeasurePreserving (fun p : E × (ι → WienerSeq) => p.2 k) (μ.prod ν)
        wienerMeasure := fun k =>
      (measurePreserving_eval (fun _ : ι => wienerMeasure) k).comp hsnd
    have hB : ∀ k, IsBrownianReal (fun t p => W t p k) (μ.prod ν) := fun k =>
      IsBrownianReal.comp_measurePreserving (hev k) isPreBrownianReal_wienerPath
        continuous_wienerPath
    have hpath : Measurable fun (ω : WienerSeq) (t : ℝ≥0) => wienerPath t ω :=
      Measurable.of_eval measurable_wienerPath
    have hind0 : iIndepFun (fun (k : ι) (ω : ι → WienerSeq) => fun t : ℝ≥0 => wienerPath t (ω k)) ν :=
      iIndepFun_pi (μ := fun _ : ι => wienerMeasure) (X := fun _ => fun ω t => wienerPath t ω)
        (fun _ => hpath.aemeasurable)
    have hind : iIndepFun (fun (k : ι) (p : E × (ι → WienerSeq)) => fun t : ℝ≥0 => W t p k)
        (μ.prod ν) :=
      iIndepFun_comp_measurePreserving hsnd (X := fun (k : ι) (ω : ι → WienerSeq) =>
        fun t : ℝ≥0 => wienerPath t (ω k))
        (fun k => Measurable.of_eval fun t => (measurable_wienerPath t).comp (measurable_pi_apply k))
        hind0
    have hX₀W : IndepFun Prod.fst (fun p : E × (ι → WienerSeq) => fun t => W t p) (μ.prod ν) :=
      indepFun_prod (μ := μ) (ν := ν) (X := id)
        (Y := fun (ω : ι → WienerSeq) (t : ℝ≥0) (k : ι) => wienerPath t (ω k)) measurable_id
        (Measurable.of_eval fun t => Measurable.of_eval fun k =>
          (measurable_wienerPath t).comp (measurable_pi_apply k))
    exact isBrownianFiltration_generated (μ.prod ν) W hW hB hind hW0 hWc Prod.fst measurable_fst
      hX₀W

/-- (A1): `card ι` independent Brownian motions with their completed natural filtration. -/
theorem exists_isBrownianFiltration_type (ι : Type) [Fintype ι] :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ℱ : Filtration ℝ _) (W : ℝ≥0 → Ω → ι → ℝ), IsBrownianFiltration P ℱ W := by
  obtain ⟨W, hW, -, -, -, h⟩ := exists_enlargement ι Unit (Measure.dirac ())
  exact ⟨Unit × (ι → WienerSeq), inferInstance, _, inferInstance, _, W, h⟩
