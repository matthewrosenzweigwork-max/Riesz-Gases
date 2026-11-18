import Mathlib

/-!
# EQ-STRONG, chaining: a maximal second-moment bound from a fourth-moment increment bound

Scalar dyadic chaining.  If `g : ℝ → Ω → ℝ` has measurable time slices, continuous paths on `[0,T]` a.s.
and `E (g t - g s)^4 ≤ B (t-s)^2` for `s,t ∈ [0,T]`, then for every `U ⊆ [0,T]`
`E sup_{t ∈ U} g_t^2 ≤ 2 E g_0^2 + K √B T` with an absolute constant `K`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal BigOperators

namespace HRS.MD.EQStrong

/-- the dyadic grid point `j T / 2^k` -/
def gp (T : ℝ) (k j : ℕ) : ℝ := (j : ℝ) * T / 2 ^ k

lemma gp_double (T : ℝ) (n i : ℕ) : gp T (n + 1) (2 * i) = gp T n i := by
  unfold gp; push_cast; rw [pow_succ]; field_simp

lemma gp_nonneg {T : ℝ} (hT : 0 ≤ T) (k j : ℕ) : 0 ≤ gp T k j := by
  unfold gp; positivity

lemma gp_le {T : ℝ} (hT : 0 ≤ T) {k j : ℕ} (hj : j ≤ 2 ^ k) : gp T k j ≤ T := by
  unfold gp
  rw [div_le_iff₀ (by positivity)]
  have : (j : ℝ) ≤ 2 ^ k := by exact_mod_cast hj
  nlinarith

lemma gp_succ_sub (T : ℝ) (k j : ℕ) : gp T k (j + 1) - gp T k j = T / 2 ^ k := by
  unfold gp; push_cast; ring

lemma nonempty_fin_pow (k : ℕ) : (Finset.univ : Finset (Fin (2 ^ k))).Nonempty :=
  ⟨⟨0, by positivity⟩, Finset.mem_univ _⟩

/-- the largest increment of `g` over the `2^k` dyadic intervals of level `k` -/
def gridMax (g : ℝ → ℝ) (T : ℝ) (k : ℕ) : ℝ :=
  (Finset.univ : Finset (Fin (2 ^ k))).sup' (nonempty_fin_pow k)
    fun j => |g (gp T k ((j : ℕ) + 1)) - g (gp T k j)|

lemma gridMax_nonneg (g : ℝ → ℝ) (T : ℝ) (k : ℕ) : 0 ≤ gridMax g T k :=
  le_trans (abs_nonneg _) (Finset.le_sup' (fun j : Fin (2 ^ k) =>
    |g (gp T k ((j : ℕ) + 1)) - g (gp T k j)|) (Finset.mem_univ ⟨0, by positivity⟩))

lemma abs_le_gridMax (g : ℝ → ℝ) (T : ℝ) (k j : ℕ) (hj : j < 2 ^ k) :
    |g (gp T k (j + 1)) - g (gp T k j)| ≤ gridMax g T k :=
  Finset.le_sup' (fun j : Fin (2 ^ k) => |g (gp T k ((j : ℕ) + 1)) - g (gp T k j)|)
    (Finset.mem_univ (⟨j, hj⟩ : Fin (2 ^ k)))

/-- deterministic dyadic chaining -/
theorem grid_bound (g : ℝ → ℝ) (T : ℝ) : ∀ n : ℕ, ∀ j : ℕ, j ≤ 2 ^ n →
    |g (gp T n j) - g 0| ≤ ∑ k ∈ Finset.range (n + 1), gridMax g T k := by
  intro n
  induction n with
  | zero =>
    intro j hj
    simp only [pow_zero] at hj
    have hsum : ∑ k ∈ Finset.range (0 + 1), gridMax g T k = gridMax g T 0 := by simp
    rw [hsum]
    interval_cases j
    · have : gp T 0 0 = 0 := by simp [gp]
      rw [this]; simpa using gridMax_nonneg g T 0
    · have := abs_le_gridMax g T 0 0 (by norm_num)
      have e : gp T 0 0 = 0 := by simp [gp]
      rw [e] at this
      simpa using this
  | succ n ih =>
    intro j hj
    rw [Finset.sum_range_succ]
    obtain ⟨i, rfl | rfl⟩ := Nat.even_or_odd' j
    · have hi : i ≤ 2 ^ n := by rw [pow_succ] at hj; omega
      rw [gp_double]
      exact (ih i hi).trans (le_add_of_nonneg_right (gridMax_nonneg g T (n + 1)))
    · have hi : i < 2 ^ n := by rw [pow_succ] at hj; omega
      have h1 := abs_le_gridMax g T (n + 1) (2 * i) (by rw [pow_succ]; omega)
      rw [gp_double] at h1
      have h2 := ih i hi.le
      have h3 : |g (gp T (n + 1) (2 * i + 1)) - g 0| ≤
          |g (gp T (n + 1) (2 * i + 1)) - g (gp T n i)| + |g (gp T n i) - g 0| :=
        abs_sub_le _ _ _
      linarith

lemma grid_dense {T : ℝ} (hT : 0 < T) :
    Set.Icc 0 T ⊆ closure {y : ℝ | ∃ n j : ℕ, j ≤ 2 ^ n ∧ y = gp T n j} := by
  intro x hx
  rw [Metric.mem_closure_iff]
  intro ε hε
  obtain ⟨n, hn⟩ : ∃ n : ℕ, T / ε < 2 ^ n := pow_unbounded_of_one_lt _ one_lt_two
  have hP : (0 : ℝ) < 2 ^ n := by positivity
  set a : ℝ := x * 2 ^ n / T with ha
  have ha0 : 0 ≤ a := by rw [ha]; have := hx.1; positivity
  have haT : a ≤ 2 ^ n := by
    rw [ha, div_le_iff₀ hT]; nlinarith [hx.2]
  have hf1 : (⌊a⌋₊ : ℝ) ≤ a := Nat.floor_le ha0
  have hf2 : a < ⌊a⌋₊ + 1 := Nat.lt_floor_add_one a
  have hfle : ⌊a⌋₊ ≤ 2 ^ n := by
    apply Nat.floor_le_of_le
    exact_mod_cast haT
  refine ⟨gp T n ⌊a⌋₊, ⟨n, ⌊a⌋₊, hfle, rfl⟩, ?_⟩
  have e1 : (⌊a⌋₊ : ℝ) * T ≤ x * 2 ^ n := by
    have := (le_div_iff₀ hT).1 (by rwa [ha] at hf1 : (⌊a⌋₊ : ℝ) ≤ x * 2 ^ n / T)
    exact this
  have e2 : x * 2 ^ n < ((⌊a⌋₊ : ℝ) + 1) * T := by
    have := (div_lt_iff₀ hT).1 (by rwa [ha] at hf2 : x * 2 ^ n / T < (⌊a⌋₊ : ℝ) + 1)
    exact this
  have e3 : T < ε * 2 ^ n := by
    have := (div_lt_iff₀ hε).1 hn
    linarith
  rw [Real.dist_eq, abs_lt]
  unfold gp
  have hQ : (⌊a⌋₊ : ℝ) * T / 2 ^ n ≤ x := by rw [div_le_iff₀ hP]; exact e1
  have hQ2 : x < ((⌊a⌋₊ : ℝ) * T + ε * 2 ^ n) / 2 ^ n := by
    rw [lt_div_iff₀ hP]; nlinarith
  have hQ3 : ((⌊a⌋₊ : ℝ) * T + ε * 2 ^ n) / 2 ^ n = (⌊a⌋₊ : ℝ) * T / 2 ^ n + ε := by
    field_simp
  constructor <;> linarith

lemma le_of_grid {T : ℝ} (hT : 0 < T) {h : ℝ → ℝ} (hc : ContinuousOn h (Set.Icc 0 T)) {s : ℝ}
    (hg : ∀ n j : ℕ, j ≤ 2 ^ n → h (gp T n j) ≤ s) : ∀ x ∈ Set.Icc (0 : ℝ) T, h x ≤ s := by
  have hcl : IsClosed (Set.Icc (0 : ℝ) T ∩ h ⁻¹' Set.Iic s) :=
    hc.preimage_isClosed_of_isClosed isClosed_Icc isClosed_Iic
  have hsub : {y : ℝ | ∃ n j : ℕ, j ≤ 2 ^ n ∧ y = gp T n j} ⊆
      Set.Icc (0 : ℝ) T ∩ h ⁻¹' Set.Iic s := by
    rintro y ⟨n, j, hj, rfl⟩
    exact ⟨⟨gp_nonneg hT.le n j, gp_le hT.le hj⟩, hg n j hj⟩
  intro x hx
  exact (closure_minimal hsub hcl (grid_dense hT hx)).2

lemma sq_le_amgm {x l : ℝ} (hl : 0 < l) : x ^ 2 ≤ l / 2 + x ^ 4 / (2 * l) := by
  rw [← sub_nonneg]
  have : l / 2 + x ^ 4 / (2 * l) - x ^ 2 = (l - x ^ 2) ^ 2 / (2 * l) := by
    field_simp; ring
  rw [this]; positivity

section Prob

variable {Ω : Type*} [MeasurableSpace Ω]

lemma measurable_gridMax (g : ℝ → Ω → ℝ) (hg : ∀ t, Measurable (g t)) (T : ℝ) (k : ℕ) :
    Measurable fun ω => gridMax (fun t => g t ω) T k := by
  have := Finset.measurable_sup' (s := (Finset.univ : Finset (Fin (2 ^ k)))) (nonempty_fin_pow k)
    (f := fun (j : Fin (2 ^ k)) ω => |g (gp T k ((j : ℕ) + 1)) ω - g (gp T k j) ω|)
    (fun j _ => ((hg _).sub (hg _)).abs)
  convert this using 1
  funext ω
  simp [gridMax, Finset.sup'_apply]

lemma gridMax_pow4_le (g : ℝ → ℝ) (T : ℝ) (k : ℕ) :
    gridMax g T k ^ 4 ≤ ∑ j : Fin (2 ^ k), (g (gp T k ((j : ℕ) + 1)) - g (gp T k j)) ^ 4 := by
  obtain ⟨j, -, hj⟩ := Finset.exists_mem_eq_sup' (nonempty_fin_pow k)
    (fun j : Fin (2 ^ k) => |g (gp T k ((j : ℕ) + 1)) - g (gp T k j)|)
  have e : gridMax g T k = |g (gp T k ((j : ℕ) + 1)) - g (gp T k j)| := hj
  have h4 : ∀ x : ℝ, |x| ^ 4 = x ^ 4 := fun x => by
    rw [← abs_pow, abs_of_nonneg (by positivity)]
  rw [e, h4]
  exact Finset.single_le_sum (f := fun j : Fin (2 ^ k) =>
    (g (gp T k ((j : ℕ) + 1)) - g (gp T k j)) ^ 4) (fun i _ => by positivity) (Finset.mem_univ j)

variable (P : Measure Ω) [IsProbabilityMeasure P]

lemma lintegral_gridMax_sq_le (g : ℝ → Ω → ℝ) (hg : ∀ t, Measurable (g t))
    {T B : ℝ} (hT : 0 < T) (hB : 0 ≤ B)
    (hinc : ∀ s t, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      ∫⁻ ω, ENNReal.ofReal ((g t ω - g s ω) ^ 4) ∂P ≤ ENNReal.ofReal (B * (t - s) ^ 2))
    (k : ℕ) {l : ℝ} (hl : 0 < l) :
    ∫⁻ ω, ENNReal.ofReal (gridMax (fun t => g t ω) T k ^ 2) ∂P ≤
      ENNReal.ofReal (l / 2 + B * T ^ 2 / (2 ^ k * (2 * l))) := by
  set Δ : Fin (2 ^ k) → Ω → ℝ := fun j ω =>
    (g (gp T k ((j : ℕ) + 1)) ω - g (gp T k j) ω) ^ 4 with hΔ
  have hΔm : ∀ j, Measurable (Δ j) := fun j => ((hg _).sub (hg _)).pow_const 4
  have hΔ0 : ∀ j ω, 0 ≤ Δ j ω := fun j ω => by simp only [hΔ]; positivity
  have hpt : ∀ ω, ENNReal.ofReal (gridMax (fun t => g t ω) T k ^ 2) ≤
      ENNReal.ofReal (l / 2) + ENNReal.ofReal (1 / (2 * l)) *
        ∑ j : Fin (2 ^ k), ENNReal.ofReal (Δ j ω) := by
    intro ω
    have h1 := sq_le_amgm (x := gridMax (fun t => g t ω) T k) hl
    have h2 := gridMax_pow4_le (fun t => g t ω) T k
    have h2' : gridMax (fun t => g t ω) T k ^ 4 / (2 * l) ≤ (∑ j, Δ j ω) / (2 * l) :=
      div_le_div_of_nonneg_right h2 (by positivity)
    have e : 1 / (2 * l) * ∑ j, Δ j ω = (∑ j, Δ j ω) / (2 * l) := by ring
    have h3 : gridMax (fun t => g t ω) T k ^ 2 ≤ l / 2 + 1 / (2 * l) * ∑ j, Δ j ω := by
      rw [e]; linarith
    calc ENNReal.ofReal (gridMax (fun t => g t ω) T k ^ 2)
        ≤ ENNReal.ofReal (l / 2 + 1 / (2 * l) * ∑ j, Δ j ω) := ENNReal.ofReal_le_ofReal h3
      _ = _ := by
        rw [ENNReal.ofReal_add (by positivity) (mul_nonneg (by positivity)
          (Finset.sum_nonneg fun j _ => hΔ0 j ω)),
          ENNReal.ofReal_mul (by positivity),
          ENNReal.ofReal_sum_of_nonneg fun j _ => hΔ0 j ω]
  calc ∫⁻ ω, ENNReal.ofReal (gridMax (fun t => g t ω) T k ^ 2) ∂P
      ≤ ∫⁻ ω, (ENNReal.ofReal (l / 2) + ENNReal.ofReal (1 / (2 * l)) *
          ∑ j : Fin (2 ^ k), ENNReal.ofReal (Δ j ω)) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal (l / 2) + ENNReal.ofReal (1 / (2 * l)) *
          ∑ j : Fin (2 ^ k), ∫⁻ ω, ENNReal.ofReal (Δ j ω) ∂P := by
        rw [lintegral_add_left measurable_const, lintegral_const, measure_univ, mul_one,
          lintegral_const_mul _ (Finset.measurable_sum _ fun j _ => (hΔm j).ennreal_ofReal),
          lintegral_finset_sum _ fun j _ => (hΔm j).ennreal_ofReal]
    _ ≤ ENNReal.ofReal (l / 2) + ENNReal.ofReal (1 / (2 * l)) *
          ∑ j : Fin (2 ^ k), ENNReal.ofReal (B * (T / 2 ^ k) ^ 2) := by
        gcongr with j _
        have hj : (j : ℕ) < 2 ^ k := j.2
        have h := hinc (gp T k j) (gp T k ((j : ℕ) + 1))
          ⟨gp_nonneg hT.le _ _, gp_le hT.le hj.le⟩
          ⟨gp_nonneg hT.le _ _, gp_le hT.le (by omega)⟩
        rw [gp_succ_sub] at h
        exact h
    _ = ENNReal.ofReal (l / 2 + B * T ^ 2 / (2 ^ k * (2 * l))) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_natCast, ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_mul (by positivity),
          ← ENNReal.ofReal_add (by positivity) (by positivity)]
        congr 1
        push_cast
        field_simp

lemma lintegral_gridMax_sq_le' (g : ℝ → Ω → ℝ) (hg : ∀ t, Measurable (g t))
    {T B : ℝ} (hT : 0 < T) (hB : 0 < B)
    (hinc : ∀ s t, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      ∫⁻ ω, ENNReal.ofReal ((g t ω - g s ω) ^ 4) ∂P ≤ ENNReal.ofReal (B * (t - s) ^ 2))
    {b : ℝ} (hb : 0 < b) (hb8 : b ^ 8 = 1 / 2) (k : ℕ) :
    ∫⁻ ω, ENNReal.ofReal (gridMax (fun t => g t ω) T k ^ 2) ∂P ≤
      ENNReal.ofReal (Real.sqrt B * T * (b ^ k) ^ 4) := by
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  have hl : 0 < Real.sqrt B * T * (b ^ k) ^ 4 := by positivity
  refine (lintegral_gridMax_sq_le P g hg hT hB.le hinc k hl).trans (le_of_eq ?_)
  congr 1
  have e8 : (b ^ k) ^ 8 = (1 / 2) ^ k := by rw [← pow_mul, mul_comm, pow_mul, hb8]
  have h2k : (2 : ℝ) ^ k = 1 / (b ^ k) ^ 8 := by
    rw [e8]; simp [one_div, inv_pow]
  have hBs : B = Real.sqrt B ^ 2 := (Real.sq_sqrt hB.le).symm
  have hx : 0 < b ^ k := by positivity
  rw [h2k]
  set s := Real.sqrt B
  set x := b ^ k
  rw [hBs]
  field_simp
  ring

lemma geom_le {x : ℝ} (h0 : 0 ≤ x) (h1 : x < 1) (s : Finset ℕ) :
    ∑ k ∈ s, x ^ k ≤ (1 - x)⁻¹ := by
  have := (summable_geometric_of_lt_one h0 h1).sum_le_tsum s (fun i _ => pow_nonneg h0 i)
  rwa [tsum_geometric_of_lt_one h0 h1] at this

lemma lintegral_partial_sq_le (g : ℝ → Ω → ℝ) (hg : ∀ t, Measurable (g t))
    {T B : ℝ} (hT : 0 < T) (hB : 0 < B)
    (hinc : ∀ s t, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      ∫⁻ ω, ENNReal.ofReal ((g t ω - g s ω) ^ 4) ∂P ≤ ENNReal.ofReal (B * (t - s) ^ 2))
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) (hb8 : b ^ 8 = 1 / 2) (n : ℕ) :
    ∫⁻ ω, ENNReal.ofReal ((∑ k ∈ Finset.range (n + 1), gridMax (fun t => g t ω) T k) ^ 2) ∂P ≤
      ENNReal.ofReal (Real.sqrt B * T / (1 - b ^ 2) ^ 2) := by
  set D : ℕ → Ω → ℝ := fun k ω => gridMax (fun t => g t ω) T k with hD
  have hDm : ∀ k, Measurable (D k) := fun k => measurable_gridMax g hg T k
  have hD0 : ∀ k ω, 0 ≤ D k ω := fun k ω => gridMax_nonneg _ _ _
  have hb2 : b ^ 2 < 1 := by nlinarith
  have hb20 : 0 ≤ b ^ 2 := by positivity
  have hsB : 0 < Real.sqrt B := Real.sqrt_pos.2 hB
  set c : ℝ := (1 - b ^ 2)⁻¹ with hc
  have hc0 : 0 ≤ c := by rw [hc]; exact inv_nonneg.2 (by linarith)
  have hpt : ∀ ω, ENNReal.ofReal ((∑ k ∈ Finset.range (n + 1), D k ω) ^ 2) ≤
      ENNReal.ofReal c * ∑ k ∈ Finset.range (n + 1),
        ENNReal.ofReal (1 / (b ^ k) ^ 2) * ENNReal.ofReal (D k ω ^ 2) := by
    intro ω
    have hcs := Finset.sum_mul_sq_le_sq_mul_sq (Finset.range (n + 1)) (fun k => b ^ k)
      (fun k => D k ω / b ^ k)
    have e1 : ∑ k ∈ Finset.range (n + 1), b ^ k * (D k ω / b ^ k) =
        ∑ k ∈ Finset.range (n + 1), D k ω :=
      Finset.sum_congr rfl fun k _ => by field_simp
    rw [e1] at hcs
    have hA : ∑ k ∈ Finset.range (n + 1), (b ^ k) ^ 2 ≤ c := by
      have : ∀ k : ℕ, (b ^ k) ^ 2 = (b ^ 2) ^ k := fun k => by rw [← pow_mul, mul_comm, pow_mul]
      simp_rw [this]; exact geom_le hb20 hb2 _
    have hB0 : 0 ≤ ∑ k ∈ Finset.range (n + 1), (D k ω / b ^ k) ^ 2 :=
      Finset.sum_nonneg fun k _ => by positivity
    have e2 : ∑ k ∈ Finset.range (n + 1), (D k ω / b ^ k) ^ 2 =
        ∑ k ∈ Finset.range (n + 1), (1 / (b ^ k) ^ 2) * D k ω ^ 2 :=
      Finset.sum_congr rfl fun k _ => by rw [div_pow]; ring
    have h1 : (∑ k ∈ Finset.range (n + 1), D k ω) ^ 2 ≤
        c * ∑ k ∈ Finset.range (n + 1), (1 / (b ^ k) ^ 2) * D k ω ^ 2 := by
      refine hcs.trans ?_
      rw [e2] at hB0 ⊢
      exact mul_le_mul_of_nonneg_right hA hB0
    calc _ ≤ ENNReal.ofReal (c * ∑ k ∈ Finset.range (n + 1), (1 / (b ^ k) ^ 2) * D k ω ^ 2) :=
          ENNReal.ofReal_le_ofReal h1
      _ = _ := by
        rw [ENNReal.ofReal_mul hc0, ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity]
        congr 1
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [ENNReal.ofReal_mul (by positivity)]
  have hmeasD : ∀ k, Measurable fun ω => ENNReal.ofReal (D k ω ^ 2) :=
    fun k => ((hDm k).pow_const 2).ennreal_ofReal
  calc ∫⁻ ω, ENNReal.ofReal ((∑ k ∈ Finset.range (n + 1), D k ω) ^ 2) ∂P
      ≤ ∫⁻ ω, ENNReal.ofReal c * ∑ k ∈ Finset.range (n + 1),
          ENNReal.ofReal (1 / (b ^ k) ^ 2) * ENNReal.ofReal (D k ω ^ 2) ∂P := lintegral_mono hpt
    _ = ENNReal.ofReal c * ∑ k ∈ Finset.range (n + 1),
          ENNReal.ofReal (1 / (b ^ k) ^ 2) * ∫⁻ ω, ENNReal.ofReal (D k ω ^ 2) ∂P := by
        rw [lintegral_const_mul _ (Finset.measurable_sum _ fun k _ => (hmeasD k).const_mul _),
          lintegral_finset_sum _ fun k _ => (hmeasD k).const_mul _]
        congr 1
        exact Finset.sum_congr rfl fun k _ => lintegral_const_mul _ (hmeasD k)
    _ ≤ ENNReal.ofReal c * ∑ k ∈ Finset.range (n + 1),
          ENNReal.ofReal (Real.sqrt B * T * (b ^ 2) ^ k) := by
        gcongr with k _
        calc ENNReal.ofReal (1 / (b ^ k) ^ 2) * ∫⁻ ω, ENNReal.ofReal (D k ω ^ 2) ∂P
            ≤ ENNReal.ofReal (1 / (b ^ k) ^ 2) *
                ENNReal.ofReal (Real.sqrt B * T * (b ^ k) ^ 4) := by
              gcongr
              exact lintegral_gridMax_sq_le' P g hg hT hB hinc hb hb8 k
          _ = ENNReal.ofReal (Real.sqrt B * T * (b ^ 2) ^ k) := by
              rw [← ENNReal.ofReal_mul (by positivity)]
              congr 1
              have : (b ^ 2) ^ k = (b ^ k) ^ 2 := by rw [← pow_mul, mul_comm, pow_mul]
              rw [this]
              have hx : 0 < b ^ k := by positivity
              field_simp
    _ ≤ ENNReal.ofReal (Real.sqrt B * T / (1 - b ^ 2) ^ 2) := by
        rw [← ENNReal.ofReal_sum_of_nonneg fun k _ => by positivity,
          ← ENNReal.ofReal_mul hc0]
        refine ENNReal.ofReal_le_ofReal ?_
        have h1 : ∑ k ∈ Finset.range (n + 1), Real.sqrt B * T * (b ^ 2) ^ k ≤
            Real.sqrt B * T * c := by
          rw [← Finset.mul_sum]
          exact mul_le_mul_of_nonneg_left (geom_le hb20 hb2 _) (by positivity)
        calc c * ∑ k ∈ Finset.range (n + 1), Real.sqrt B * T * (b ^ 2) ^ k
            ≤ c * (Real.sqrt B * T * c) := mul_le_mul_of_nonneg_left h1 hc0
          _ = Real.sqrt B * T / (1 - b ^ 2) ^ 2 := by
              rw [hc]
              have : (1 - b ^ 2) ≠ 0 := by linarith
              field_simp

lemma lintegral_iSup_partial (g : ℝ → Ω → ℝ) (hg : ∀ t, Measurable (g t))
    {T B : ℝ} (hT : 0 < T) (hB : 0 < B)
    (hinc : ∀ s t, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      ∫⁻ ω, ENNReal.ofReal ((g t ω - g s ω) ^ 4) ∂P ≤ ENNReal.ofReal (B * (t - s) ^ 2))
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) (hb8 : b ^ 8 = 1 / 2) :
    ∫⁻ ω, ⨆ n : ℕ, ENNReal.ofReal
      ((∑ k ∈ Finset.range (n + 1), gridMax (fun t => g t ω) T k) ^ 2) ∂P ≤
      ENNReal.ofReal (Real.sqrt B * T / (1 - b ^ 2) ^ 2) := by
  have hm : ∀ n : ℕ, Measurable fun ω => ENNReal.ofReal
      ((∑ k ∈ Finset.range (n + 1), gridMax (fun t => g t ω) T k) ^ 2) := fun n =>
    ((Finset.measurable_sum _ fun k _ => measurable_gridMax g hg T k).pow_const 2).ennreal_ofReal
  have hmono : Monotone fun (n : ℕ) ω => ENNReal.ofReal
      ((∑ k ∈ Finset.range (n + 1), gridMax (fun t => g t ω) T k) ^ 2) := by
    intro n m hnm ω
    apply ENNReal.ofReal_le_ofReal
    apply pow_le_pow_left₀ (Finset.sum_nonneg fun _ _ => gridMax_nonneg _ _ _)
    exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
      (fun _ _ _ => gridMax_nonneg _ _ _)
  rw [lintegral_iSup hm hmono]
  exact iSup_le fun n => lintegral_partial_sq_le P g hg hT hB hinc hb hb1 hb8 n

lemma chain_aux (g : ℝ → Ω → ℝ) (hg : ∀ t, Measurable (g t))
    {T B : ℝ} (hT0 : 0 ≤ T) (hB : 0 < B)
    (hinc : ∀ s t, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      ∫⁻ ω, ENNReal.ofReal ((g t ω - g s ω) ^ 4) ∂P ≤ ENNReal.ofReal (B * (t - s) ^ 2))
    (hcont : ∀ᵐ ω ∂P, ContinuousOn (fun t => g t ω) (Set.Icc 0 T))
    {b : ℝ} (hb : 0 < b) (hb1 : b < 1) (hb8 : b ^ 8 = 1 / 2) (U : Set ℝ) (hU : U ⊆ Set.Icc 0 T) :
    ∫⁻ ω, ⨆ t ∈ U, ENNReal.ofReal (g t ω ^ 2) ∂P ≤
      2 * ∫⁻ ω, ENNReal.ofReal (g 0 ω ^ 2) ∂P +
        ENNReal.ofReal (2 / (1 - b ^ 2) ^ 2 * Real.sqrt B * T) := by
  have hg0 : Measurable fun ω => ENNReal.ofReal (g 0 ω ^ 2) := ((hg 0).pow_const 2).ennreal_ofReal
  rcases hT0.eq_or_lt with hT | hT
  · subst hT
    have hpt : ∀ ω, ⨆ t ∈ U, ENNReal.ofReal (g t ω ^ 2) ≤ ENNReal.ofReal (g 0 ω ^ 2) := by
      intro ω
      refine iSup₂_le fun t ht => ?_
      have : t = 0 := le_antisymm (hU ht).2 (hU ht).1
      subst this; exact le_rfl
    calc _ ≤ ∫⁻ ω, ENNReal.ofReal (g 0 ω ^ 2) ∂P := lintegral_mono hpt
      _ ≤ 2 * ∫⁻ ω, ENNReal.ofReal (g 0 ω ^ 2) ∂P :=
          le_mul_of_one_le_left (by simp) one_le_two
      _ ≤ _ := le_self_add
  · set S : Ω → ℝ≥0∞ := fun ω => ⨆ n : ℕ, ENNReal.ofReal
      ((∑ k ∈ Finset.range (n + 1), gridMax (fun t => g t ω) T k) ^ 2) with hS
    have hSm : Measurable S := Measurable.iSup fun n =>
      ((Finset.measurable_sum _ fun k _ => measurable_gridMax g hg T k).pow_const 2).ennreal_ofReal
    have hpt : ∀ᵐ ω ∂P, ⨆ t ∈ U, ENNReal.ofReal (g t ω ^ 2) ≤
        2 * ENNReal.ofReal (g 0 ω ^ 2) + 2 * S ω := by
      filter_upwards [hcont] with ω hω
      have hh : ContinuousOn (fun x => (g x ω - g 0 ω) ^ 2) (Set.Icc 0 T) :=
        (hω.sub continuousOn_const).pow 2
      have key : ∀ x ∈ Set.Icc (0 : ℝ) T, ENNReal.ofReal ((g x ω - g 0 ω) ^ 2) ≤ S ω := by
        intro x hx
        by_cases hTop : S ω = ⊤
        · rw [hTop]; exact le_top
        · have hgrid : ∀ n j : ℕ, j ≤ 2 ^ n →
              (fun x => (g x ω - g 0 ω) ^ 2) (gp T n j) ≤ (S ω).toReal := by
            intro n j hj
            have h1 := grid_bound (fun t => g t ω) T n j hj
            have h2 : (g (gp T n j) ω - g 0 ω) ^ 2 ≤
                (∑ k ∈ Finset.range (n + 1), gridMax (fun t => g t ω) T k) ^ 2 :=
              sq_le_sq.2 (h1.trans (le_abs_self _))
            have h3 : ENNReal.ofReal
                ((∑ k ∈ Finset.range (n + 1), gridMax (fun t => g t ω) T k) ^ 2) ≤ S ω :=
              le_iSup (fun n : ℕ => ENNReal.ofReal
                ((∑ k ∈ Finset.range (n + 1), gridMax (fun t => g t ω) T k) ^ 2)) n
            exact h2.trans ((ENNReal.ofReal_le_iff_le_toReal hTop).1 h3)
          have := le_of_grid hT hh hgrid x hx
          calc ENNReal.ofReal ((g x ω - g 0 ω) ^ 2) ≤ ENNReal.ofReal (S ω).toReal :=
                ENNReal.ofReal_le_ofReal this
            _ = S ω := ENNReal.ofReal_toReal hTop
      refine iSup₂_le fun t ht => ?_
      have h1 : g t ω ^ 2 ≤ 2 * g 0 ω ^ 2 + 2 * (g t ω - g 0 ω) ^ 2 := by
        nlinarith [sq_nonneg (g t ω - 2 * g 0 ω)]
      calc ENNReal.ofReal (g t ω ^ 2) ≤ ENNReal.ofReal (2 * g 0 ω ^ 2 + 2 * (g t ω - g 0 ω) ^ 2) :=
            ENNReal.ofReal_le_ofReal h1
        _ = 2 * ENNReal.ofReal (g 0 ω ^ 2) + 2 * ENNReal.ofReal ((g t ω - g 0 ω) ^ 2) := by
            rw [ENNReal.ofReal_add (by positivity) (by positivity),
              ENNReal.ofReal_mul (by norm_num), ENNReal.ofReal_mul (by norm_num)]
            simp
        _ ≤ _ := by gcongr; exact key t (hU ht)
    calc ∫⁻ ω, ⨆ t ∈ U, ENNReal.ofReal (g t ω ^ 2) ∂P
        ≤ ∫⁻ ω, (2 * ENNReal.ofReal (g 0 ω ^ 2) + 2 * S ω) ∂P := lintegral_mono_ae hpt
      _ = 2 * ∫⁻ ω, ENNReal.ofReal (g 0 ω ^ 2) ∂P + 2 * ∫⁻ ω, S ω ∂P := by
          rw [lintegral_add_left (hg0.const_mul _), lintegral_const_mul _ hg0,
            lintegral_const_mul _ hSm]
      _ ≤ 2 * ∫⁻ ω, ENNReal.ofReal (g 0 ω ^ 2) ∂P +
            2 * ENNReal.ofReal (Real.sqrt B * T / (1 - b ^ 2) ^ 2) := by
          gcongr
          exact lintegral_iSup_partial P g hg hT hB hinc hb hb1 hb8
      _ = _ := by
          congr 1
          rw [show (2 : ℝ≥0∞) = ENNReal.ofReal 2 by simp, ← ENNReal.ofReal_mul (by norm_num)]
          congr 1
          ring

end Prob

theorem chain_scalar : ∃ K : ℝ, 0 < K ∧ ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    [IsProbabilityMeasure P] (g : ℝ → Ω → ℝ), (∀ t, Measurable (g t)) →
    ∀ {T B : ℝ}, 0 ≤ T → 0 < B →
    (∀ s t, s ∈ Set.Icc 0 T → t ∈ Set.Icc 0 T →
      ∫⁻ ω, ENNReal.ofReal ((g t ω - g s ω) ^ 4) ∂P ≤ ENNReal.ofReal (B * (t - s) ^ 2)) →
    (∀ᵐ ω ∂P, ContinuousOn (fun t => g t ω) (Set.Icc 0 T)) →
    ∀ U : Set ℝ, U ⊆ Set.Icc 0 T →
    ∫⁻ ω, ⨆ t ∈ U, ENNReal.ofReal (g t ω ^ 2) ∂P ≤
      2 * ∫⁻ ω, ENNReal.ofReal (g 0 ω ^ 2) ∂P + ENNReal.ofReal (K * Real.sqrt B * T) := by
  obtain ⟨b, hb, hb1, hb8⟩ : ∃ b : ℝ, 0 < b ∧ b < 1 ∧ b ^ 8 = 1 / 2 := by
    refine ⟨(1 / 2 : ℝ) ^ ((1 : ℝ) / 8), by positivity, ?_, ?_⟩
    · exact Real.rpow_lt_one (by norm_num) (by norm_num) (by norm_num)
    · rw [← Real.rpow_natCast, ← Real.rpow_mul (by norm_num)]
      norm_num
  have hb2 : b ^ 2 < 1 := by nlinarith
  refine ⟨2 / (1 - b ^ 2) ^ 2, by
    have : 0 < 1 - b ^ 2 := by linarith
    positivity, ?_⟩
  intro Ω _ P _ g hg T B hT hB hinc hcont U hU
  exact chain_aux P g hg hT hB hinc hcont hb hb1 hb8 U hU

end HRS.MD.EQStrong
