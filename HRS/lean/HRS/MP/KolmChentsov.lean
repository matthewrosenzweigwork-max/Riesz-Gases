import HRS.Whole.AppendixALemmas2
import HRS.MP.PathTightCrit

/-!
# Kolmogorov-Chentsov with a uniform modulus: proof of `kolmogorov_modulus_tightness`
-/

open MeasureTheory Filter Topology
open HRS.Whole.AppendixALemmas
open scoped ENNReal NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace HRS.MP.KC

section Det

variable {E : Type*} [NormedAddCommGroup E]

/-- Increment hypothesis on dyadic grid values. -/
def mkc_Inc (x : ℕ → ℕ → E) (lam r : ℝ) : Prop :=
  ∀ n k : ℕ, k < 2 ^ n → ‖x n (k + 1) - x n k‖ ≤ lam * r ^ n

/-- Consistency of the dyadic grids. -/
def mkc_Cons (x : ℕ → ℕ → E) : Prop := ∀ n k : ℕ, x (n + 1) (2 * k) = x n k

theorem mkc_chain {x : ℕ → ℕ → E} {lam r : ℝ} (hc : mkc_Cons x) (hi : mkc_Inc x lam r) (m : ℕ) :
    ∀ (j k : ℕ), k ≤ 2 ^ (m + j) →
      ‖x (m + j) k - x m (k / 2 ^ j)‖ ≤ ∑ i ∈ Finset.range j, lam * r ^ (m + 1 + i) := by
  intro j
  induction j with
  | zero => intro k hk; simp
  | succ j ih =>
    intro k hk
    have hQ : 2 ^ (m + (j + 1)) = 2 * 2 ^ (m + j) := by ring
    rw [hQ] at hk
    have h1 : k / 2 ≤ 2 ^ (m + j) := by omega
    have ih' := ih (k / 2) h1
    have hdiv : k / 2 ^ (j + 1) = k / 2 / 2 ^ j := by
      rw [Nat.div_div_eq_div_mul, pow_succ']
    rw [hdiv, Finset.sum_range_succ]
    have hstep : ‖x (m + (j + 1)) k - x (m + j) (k / 2)‖ ≤ lam * r ^ (m + 1 + j) := by
      have hmj : m + (j + 1) = m + j + 1 := by ring
      have hpow : r ^ (m + 1 + j) = r ^ (m + j + 1) := by ring_nf
      rw [hmj, hpow]
      rcases Nat.even_or_odd' k with ⟨k', hk' | hk'⟩
      · have : k / 2 = k' := by omega
        rw [this, hk', hc (m + j) k']
        simp only [sub_self, norm_zero]
        have := hi (m + j + 1) 0 (by positivity)
        have h0 : 0 ≤ ‖x (m + j + 1) (0 + 1) - x (m + j + 1) 0‖ := norm_nonneg _
        linarith
      · have : k / 2 = k' := by omega
        rw [this, hk']
        have h2 : 2 * k' < 2 ^ (m + j + 1) := by
          have : 2 ^ (m + j + 1) = 2 * 2 ^ (m + j) := by ring
          omega
        have := hi (m + j + 1) (2 * k') h2
        rw [← hc (m + j) k']
        exact this
    calc ‖x (m + (j + 1)) k - x m (k / 2 / 2 ^ j)‖
        = ‖(x (m + (j + 1)) k - x (m + j) (k / 2)) + (x (m + j) (k / 2) - x m (k / 2 / 2 ^ j))‖ := by
          congr 1; abel
      _ ≤ _ := norm_add_le _ _
      _ ≤ lam * r ^ (m + 1 + j) + ∑ i ∈ Finset.range j, lam * r ^ (m + 1 + i) := add_le_add hstep ih'
      _ = _ := add_comm _ _

theorem mkc_geom_le {lam r : ℝ} (hlam : 0 ≤ lam) (hr0 : 0 ≤ r) (hr1 : r < 1) (m j : ℕ) :
    ∑ i ∈ Finset.range j, lam * r ^ (m + 1 + i) ≤ lam * r ^ (m + 1) / (1 - r) := by
  have h1r : 0 < 1 - r := by linarith
  have e : ∑ i ∈ Finset.range j, lam * r ^ (m + 1 + i) =
      lam * r ^ (m + 1) * ∑ i ∈ Finset.range j, r ^ i := by
    rw [Finset.mul_sum]; exact Finset.sum_congr rfl fun i _ => by ring
  rw [e, div_eq_mul_one_div (lam * r ^ (m + 1))]
  refine mul_le_mul_of_nonneg_left ?_ (mul_nonneg hlam (pow_nonneg hr0 _))
  have hg : (∑ i ∈ Finset.range j, r ^ i) * (1 - r) = 1 - r ^ j := geom_sum_mul_neg r j
  rw [le_div_iff₀ h1r, hg]
  have := pow_nonneg hr0 j
  linarith

/-- The constant of the chaining estimate. -/
def mkc_c (r : ℝ) : ℝ := 1 + 2 * r / (1 - r)

theorem mkc_incr {x : ℕ → ℕ → E} {lam r : ℝ} (hc : mkc_Cons x) (hi : mkc_Inc x lam r)
    (hlam : 0 ≤ lam) (hr0 : 0 ≤ r) (hr1 : r < 1) (m j k l : ℕ)
    (hk : k ≤ 2 ^ (m + j)) (hl : l ≤ 2 ^ (m + j)) (hkl : k ≤ l + 2 ^ j) (hlk : l ≤ k + 2 ^ j) :
    ‖x (m + j) k - x (m + j) l‖ ≤ mkc_c r * (lam * r ^ m) := by
  have h1r : 0 < 1 - r := by linarith
  have hpos : 0 < 2 ^ j := by positivity
  have hb : ∀ q, q ≤ 2 ^ (m + j) →
      ‖x (m + j) q - x m (q / 2 ^ j)‖ ≤ lam * r ^ (m + 1) / (1 - r) := fun q hq =>
    (mkc_chain hc hi m j q hq).trans (mkc_geom_le hlam hr0 hr1 m j)
  have hk' : k / 2 ^ j ≤ 2 ^ m := by
    apply Nat.div_le_of_le_mul
    rw [pow_add] at hk
    linarith
  have hl' : l / 2 ^ j ≤ 2 ^ m := by
    apply Nat.div_le_of_le_mul
    rw [pow_add] at hl
    linarith
  have hkl' : k / 2 ^ j ≤ l / 2 ^ j + 1 := by
    calc k / 2 ^ j ≤ (l + 2 ^ j) / 2 ^ j := Nat.div_le_div_right hkl
      _ = l / 2 ^ j + 1 := by rw [Nat.add_div_right _ hpos]
  have hlk' : l / 2 ^ j ≤ k / 2 ^ j + 1 := by
    calc l / 2 ^ j ≤ (k + 2 ^ j) / 2 ^ j := Nat.div_le_div_right hlk
      _ = k / 2 ^ j + 1 := by rw [Nat.add_div_right _ hpos]
  have hmid : ‖x m (k / 2 ^ j) - x m (l / 2 ^ j)‖ ≤ lam * r ^ m := by
    rcases Nat.lt_trichotomy (k / 2 ^ j) (l / 2 ^ j) with h | h | h
    · have e : l / 2 ^ j = k / 2 ^ j + 1 := by omega
      rw [e, norm_sub_rev]
      exact hi m (k / 2 ^ j) (by omega)
    · rw [h]; simp only [sub_self, norm_zero]; positivity
    · have e : k / 2 ^ j = l / 2 ^ j + 1 := by omega
      rw [e]
      exact hi m (l / 2 ^ j) (by omega)
  calc ‖x (m + j) k - x (m + j) l‖
      = ‖(x (m + j) k - x m (k / 2 ^ j)) + (x m (k / 2 ^ j) - x m (l / 2 ^ j)) -
          (x (m + j) l - x m (l / 2 ^ j))‖ := by congr 1; abel
    _ ≤ ‖(x (m + j) k - x m (k / 2 ^ j)) + (x m (k / 2 ^ j) - x m (l / 2 ^ j))‖ +
          ‖x (m + j) l - x m (l / 2 ^ j)‖ := norm_sub_le _ _
    _ ≤ ‖x (m + j) k - x m (k / 2 ^ j)‖ + ‖x m (k / 2 ^ j) - x m (l / 2 ^ j)‖ +
          ‖x (m + j) l - x m (l / 2 ^ j)‖ := by gcongr; exact norm_add_le _ _
    _ ≤ lam * r ^ (m + 1) / (1 - r) + lam * r ^ m + lam * r ^ (m + 1) / (1 - r) := by
        gcongr
        · exact hb k hk
        · exact hb l hl
    _ = mkc_c r * (lam * r ^ m) := by
        unfold mkc_c; field_simp; ring

/-! Dyadic index of a point. -/

/-- The grid point `T k / 2^n`. -/
def mkc_pt (T : ℝ) (n k : ℕ) : ℝ := T * k / 2 ^ n

/-- The index of the grid point of level `n` just below `t`. -/
def mkc_idx (T : ℝ) (n : ℕ) (t : ℝ) : ℕ := ⌊t * 2 ^ n / T⌋₊

theorem mkc_idx_le {T : ℝ} (hT : 0 < T) {t : ℝ} (ht : t ≤ T) (n : ℕ) : mkc_idx T n t ≤ 2 ^ n := by
  unfold mkc_idx
  apply Nat.floor_le_of_le
  rw [div_le_iff₀ hT]
  push_cast
  have : (0 : ℝ) < 2 ^ n := by positivity
  nlinarith

theorem mkc_idx_div {T : ℝ} (hT : 0 < T) (t : ℝ) (n j : ℕ) :
    mkc_idx T (n + j) t / 2 ^ j = mkc_idx T n t := by
  unfold mkc_idx
  have : t * 2 ^ n / T = (t * 2 ^ (n + j) / T) / ((2 ^ j : ℕ) : ℝ) := by
    push_cast
    rw [pow_add]; field_simp
  rw [this, Nat.floor_div_natCast]

theorem mkc_pt_idx {T : ℝ} (hT : 0 < T) {t : ℝ} (ht0 : 0 ≤ t) (n : ℕ) :
    mkc_pt T n (mkc_idx T n t) ≤ t ∧ t < mkc_pt T n (mkc_idx T n t) + T / 2 ^ n := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have ha : 0 ≤ t * 2 ^ n / T := by positivity
  have h1 := Nat.floor_le ha
  have h3 := Nat.lt_floor_add_one (t * 2 ^ n / T)
  unfold mkc_pt mkc_idx
  constructor
  · rw [div_le_iff₀ h2]
    calc T * (⌊t * 2 ^ n / T⌋₊ : ℝ) ≤ T * (t * 2 ^ n / T) := by gcongr
      _ = t * 2 ^ n := by field_simp
  · rw [← sub_pos]
    have : (T * (⌊t * 2 ^ n / T⌋₊ : ℝ) / 2 ^ n + T / 2 ^ n) - t =
        (T / 2 ^ n) * ((⌊t * 2 ^ n / T⌋₊ : ℝ) + 1 - t * 2 ^ n / T) := by
      field_simp
    have h4 : 0 < T / 2 ^ n := by positivity
    rw [this]
    exact mul_pos h4 (by linarith)

theorem mkc_idx_add {T : ℝ} (hT : 0 < T) {t s : ℝ} (hs : 0 ≤ s) (m j : ℕ) (hts : t ≤ s + T / 2 ^ m) :
    mkc_idx T (m + j) t ≤ mkc_idx T (m + j) s + 2 ^ j := by
  unfold mkc_idx
  have h2 : (0 : ℝ) < 2 ^ (m + j) := by positivity
  have ha : 0 ≤ s * 2 ^ (m + j) / T := by positivity
  have e : (s + T / 2 ^ m) * 2 ^ (m + j) / T = s * 2 ^ (m + j) / T + ((2 ^ j : ℕ) : ℝ) := by
    push_cast; rw [pow_add]; field_simp
  calc ⌊t * 2 ^ (m + j) / T⌋₊ ≤ ⌊(s + T / 2 ^ m) * 2 ^ (m + j) / T⌋₊ := by
        apply Nat.floor_le_floor
        gcongr
    _ = ⌊s * 2 ^ (m + j) / T⌋₊ + 2 ^ j := by rw [e, Nat.floor_add_natCast ha]

theorem mkc_limit [CompleteSpace E] {x : ℕ → ℕ → E} {lam r : ℝ} (hc : mkc_Cons x)
    (hi : mkc_Inc x lam r) (hlam : 0 ≤ lam) (hr0 : 0 ≤ r) (hr1 : r < 1) {T : ℝ} (hT : 0 < T)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    ∃ L : E, Tendsto (fun n => x n (mkc_idx T n t)) atTop (𝓝 L) ∧
      ∀ n, ‖x n (mkc_idx T n t) - L‖ ≤ lam * r ^ (n + 1) / (1 - r) := by
  have h1r : 0 < 1 - r := by linarith
  have hb : ∀ n j : ℕ, ‖x (n + j) (mkc_idx T (n + j) t) - x n (mkc_idx T n t)‖ ≤
      lam * r ^ (n + 1) / (1 - r) := by
    intro n j
    have := mkc_chain hc hi n j (mkc_idx T (n + j) t) (mkc_idx_le hT ht.2 _)
    rw [mkc_idx_div hT] at this
    exact this.trans (mkc_geom_le hlam hr0 hr1 n j)
  have hcau : CauchySeq (fun n => x n (mkc_idx T n t)) := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    have hlim : Tendsto (fun n : ℕ => lam * r ^ (n + 1) / (1 - r)) atTop (𝓝 0) := by
      have := ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).comp
        (tendsto_add_atTop_nat 1)).const_mul lam |>.div_const (1 - r)
      simpa using this
    obtain ⟨N, hN⟩ := (hlim.eventually (gt_mem_nhds hε)).exists
    refine ⟨N, fun n hn => ?_⟩
    obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
    rw [dist_eq_norm]
    exact (hb N j).trans_lt hN
  obtain ⟨L, hL⟩ := cauchySeq_tendsto_of_complete hcau
  refine ⟨L, hL, fun n => ?_⟩
  have : Tendsto (fun n' => ‖x n' (mkc_idx T n' t) - x n (mkc_idx T n t)‖) atTop
      (𝓝 ‖L - x n (mkc_idx T n t)‖) := (hL.sub_const _).norm
  rw [norm_sub_rev]
  refine le_of_tendsto this (eventually_atTop.2 ⟨n, fun n' hn' => ?_⟩)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn'
  exact hb n j

theorem mkc_modulus {x : ℕ → ℕ → E} {lam r : ℝ} (hc : mkc_Cons x)
    (hi : mkc_Inc x lam r) (hlam : 0 ≤ lam) (hr0 : 0 ≤ r) (hr1 : r < 1) {T : ℝ} (hT : 0 < T)
    {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (hs : s ∈ Set.Icc (0 : ℝ) T) (m : ℕ)
    (hts : |t - s| ≤ T / 2 ^ m) {Lt Ls : E}
    (hLt : Tendsto (fun n => x n (mkc_idx T n t)) atTop (𝓝 Lt))
    (hLs : Tendsto (fun n => x n (mkc_idx T n s)) atTop (𝓝 Ls)) :
    ‖Lt - Ls‖ ≤ mkc_c r * (lam * r ^ m) := by
  have h1 := (abs_le.1 hts)
  have : Tendsto (fun n => ‖x n (mkc_idx T n t) - x n (mkc_idx T n s)‖) atTop (𝓝 ‖Lt - Ls‖) :=
    (hLt.sub hLs).norm
  refine le_of_tendsto this (eventually_atTop.2 ⟨m, fun n hn => ?_⟩)
  obtain ⟨j, rfl⟩ := Nat.exists_eq_add_of_le hn
  exact mkc_incr hc hi hlam hr0 hr1 m j _ _ (mkc_idx_le hT ht.2 _) (mkc_idx_le hT hs.2 _)
    (mkc_idx_add hT hs.1 m j (by linarith)) (mkc_idx_add hT ht.1 m j (by linarith))

end Det

section Prob

variable {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
  [SecondCountableTopology E]
variable {Ω : Type*} [MeasurableSpace Ω]

/-- Markov's inequality for `‖d‖^p`. -/
theorem mkc_markov (μ : Measure Ω) {d : Ω → E} (hd : Measurable d) {p : ℝ} (hp : 0 < p)
    {c M : ℝ} (hc : 0 < c) (hM : ∫⁻ ζ, ‖d ζ‖ₑ ^ p ∂μ ≤ ENNReal.ofReal M) :
    μ {ζ | c < ‖d ζ‖} ≤ ENNReal.ofReal (M / c ^ p) := by
  have hcp : 0 < c ^ p := Real.rpow_pos_of_pos hc p
  have hsub : {ζ | c < ‖d ζ‖} ⊆ {ζ | ENNReal.ofReal (c ^ p) ≤ ‖d ζ‖ₑ ^ p} := by
    intro ζ hζ
    simp only [Set.mem_ofPred_eq] at hζ ⊢
    rw [← ENNReal.ofReal_rpow_of_nonneg hc.le hp.le]
    exact ENNReal.rpow_le_rpow (by rw [← ofReal_norm]; exact ENNReal.ofReal_le_ofReal hζ.le)
      hp.le
  have hmeas : AEMeasurable (fun ζ => ‖d ζ‖ₑ ^ p) μ :=
    (hd.enorm.pow_const p).aemeasurable
  calc μ {ζ | c < ‖d ζ‖} ≤ μ {ζ | ENNReal.ofReal (c ^ p) ≤ ‖d ζ‖ₑ ^ p} := measure_mono hsub
    _ ≤ (∫⁻ ζ, ‖d ζ‖ₑ ^ p ∂μ) / ENNReal.ofReal (c ^ p) :=
        meas_ge_le_lintegral_div hmeas (by simpa using hcp) ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal M / ENNReal.ofReal (c ^ p) := by gcongr
    _ = ENNReal.ofReal (M / c ^ p) := (ENNReal.ofReal_div_of_pos hcp).symm

variable (X : ℝ → Ω → E) (T r : ℝ)

/-- The dyadic grid values of `X` along the sample point `ζ`. -/
def mkc_xs (ζ : Ω) : ℕ → ℕ → E := fun n k => X (mkc_pt T n k) ζ

theorem mkc_cons_xs (ζ : Ω) : mkc_Cons (mkc_xs X T ζ) := by
  intro n k
  have : mkc_pt T (n + 1) (2 * k) = mkc_pt T n k := by
    unfold mkc_pt; push_cast; rw [pow_succ]; field_simp
  simp only [mkc_xs, this]

/-- The good event `{sup_n r^{-n} Δ_n ≤ lam}`. -/
def mkc_G (lam : ℝ) : Set Ω := {ζ | mkc_Inc (mkc_xs X T ζ) lam r}

/-- The event `{K < ∞}`. -/
def mkc_Gs : Set Ω := ⋃ m : ℕ, mkc_G X T r (m : ℝ)

theorem mkc_G_mono (hr : 0 ≤ r) {a b : ℝ} (hab : a ≤ b) : mkc_G X T r a ⊆ mkc_G X T r b := by
  intro ζ hζ n k hk
  exact (hζ n k hk).trans (by gcongr)

theorem mkc_G_meas (hX : ∀ t, Measurable (X t)) (lam : ℝ) : MeasurableSet (mkc_G X T r lam) := by
  have : mkc_G X T r lam = ⋂ n : ℕ, ⋂ k : ℕ,
      {ζ | k < 2 ^ n → ‖X (mkc_pt T n (k + 1)) ζ - X (mkc_pt T n k) ζ‖ ≤ lam * r ^ n} := by
    ext ζ; simp [mkc_G, mkc_Inc, mkc_xs]
  rw [this]
  refine MeasurableSet.iInter fun n => MeasurableSet.iInter fun k => ?_
  by_cases h : k < 2 ^ n
  · simp only [h, forall_const]
    exact measurableSet_le (((hX _).sub (hX _)).norm) measurable_const
  · simp [h]

theorem mkc_Gs_meas (hX : ∀ t, Measurable (X t)) : MeasurableSet (mkc_Gs X T r) :=
  MeasurableSet.iUnion fun m => mkc_G_meas X T r hX _

theorem mkc_pt_mem {T : ℝ} (hT : 0 < T) (n k : ℕ) (hk : k ≤ 2 ^ n) :
    mkc_pt T n k ∈ Set.Icc (0 : ℝ) T := by
  unfold mkc_pt
  constructor
  · positivity
  · rw [div_le_iff₀ (by positivity)]
    have : (k : ℝ) ≤ 2 ^ n := by exact_mod_cast hk
    nlinarith

theorem mkc_pt_succ_sub (n k : ℕ) : mkc_pt T n (k + 1) - mkc_pt T n k = T / 2 ^ n := by
  unfold mkc_pt; push_cast; ring

theorem mkc_real_bound {T β p r q lam Cp : ℝ} (hT : 0 < T) (hCp : 0 ≤ Cp)
    (hr0 : 0 < r) (hqr : 1 ≤ q * 2 ^ β * r ^ p) (hq0 : 0 < q) (hlam : 0 < lam) (n : ℕ) :
    (2 : ℝ) ^ n * (Cp * (T / 2 ^ n) ^ (1 + β) / (lam * r ^ n) ^ p) ≤
      Cp * T ^ (1 + β) * lam ^ (-p) * q ^ n := by
  have h2 : (0 : ℝ) < 2 ^ n := by positivity
  have e1 : (T / 2 ^ n) ^ (1 + β) = T ^ (1 + β) / (2 ^ n * ((2 : ℝ) ^ β) ^ n) := by
    rw [Real.div_rpow hT.le h2.le, Real.rpow_add h2, Real.rpow_one,
      Real.rpow_pow_comm (by norm_num) β n]
  have e2 : (lam * r ^ n) ^ p = lam ^ p * (r ^ p) ^ n := by
    rw [Real.mul_rpow hlam.le (pow_nonneg hr0.le n), Real.rpow_pow_comm hr0.le p n]
  have hlp : 0 < lam ^ p := Real.rpow_pos_of_pos hlam p
  have hrp : 0 < r ^ p := Real.rpow_pos_of_pos hr0 p
  have h2b : 0 < (2 : ℝ) ^ β := Real.rpow_pos_of_pos (by norm_num) β
  set A : ℝ := ((2 : ℝ) ^ β) ^ n * (r ^ p) ^ n with hA
  have hApos : 0 < A := by positivity
  set Kc : ℝ := Cp * T ^ (1 + β) / lam ^ p with hKc
  have hKc0 : 0 ≤ Kc := by
    have : 0 ≤ T ^ (1 + β) := Real.rpow_nonneg hT.le _
    positivity
  have hL : (2 : ℝ) ^ n * (Cp * (T / 2 ^ n) ^ (1 + β) / (lam * r ^ n) ^ p) = Kc / A := by
    rw [e1, e2, hKc, hA]
    field_simp
  have hR : Cp * T ^ (1 + β) * lam ^ (-p) * q ^ n = Kc * q ^ n := by
    rw [Real.rpow_neg hlam.le, hKc]
    field_simp
  rw [hL, hR, div_le_iff₀ hApos]
  have h1 : 1 ≤ (q * 2 ^ β * r ^ p) ^ n := one_le_pow₀ hqr
  have h3 : (q * 2 ^ β * r ^ p) ^ n = q ^ n * A := by
    rw [hA, mul_assoc, mul_pow, mul_pow]
  rw [h3] at h1
  calc Kc = Kc * 1 := (mul_one _).symm
    _ ≤ Kc * (q ^ n * A) := by gcongr
    _ = Kc * q ^ n * A := by ring

theorem mkc_prob_bound (μ : Measure Ω) (hX : ∀ t, Measurable (X t)) {p β C q : ℝ}
    (hT : 0 < T) (hp : 0 < p)
    (hmom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖X t ζ - X s ζ‖ₑ ^ p ∂μ ≤ ENNReal.ofReal (C * |t - s| ^ (1 + β)))
    (hr0 : 0 < r) (hq0 : 0 < q) (hq1 : q < 1) (hqr : 1 ≤ q * 2 ^ β * r ^ p)
    {lam : ℝ} (hlam : 0 < lam) :
    μ (mkc_G X T r lam)ᶜ ≤
      ENNReal.ofReal (max C 0 * T ^ (1 + β) * lam ^ (-p) / (1 - q)) := by
  set Kc : ℝ := max C 0 * T ^ (1 + β) * lam ^ (-p) with hKc
  have hKc0 : 0 ≤ Kc := by
    have : 0 ≤ T ^ (1 + β) := Real.rpow_nonneg hT.le _
    have : 0 ≤ lam ^ (-p) := Real.rpow_nonneg hlam.le _
    positivity
  have hsub : (mkc_G X T r lam)ᶜ ⊆ ⋃ n : ℕ, ⋃ k ∈ Finset.range (2 ^ n),
      {ζ | lam * r ^ n < ‖X (mkc_pt T n (k + 1)) ζ - X (mkc_pt T n k) ζ‖} := by
    intro ζ hζ
    simp only [mkc_G, mkc_Inc, mkc_xs, Set.mem_compl_iff, Set.mem_ofPred_eq, not_forall,
      not_le] at hζ
    obtain ⟨n, k, hk, h⟩ := hζ
    simp only [Set.mem_iUnion]
    exact ⟨n, k, Finset.mem_range.2 hk, h⟩
  have hterm : ∀ n : ℕ, μ (⋃ k ∈ Finset.range (2 ^ n),
      {ζ | lam * r ^ n < ‖X (mkc_pt T n (k + 1)) ζ - X (mkc_pt T n k) ζ‖}) ≤
      ENNReal.ofReal (Kc * q ^ n) := by
    intro n
    refine (measure_biUnion_finset_le _ _).trans ?_
    have hk : ∀ k ∈ Finset.range (2 ^ n),
        μ {ζ | lam * r ^ n < ‖X (mkc_pt T n (k + 1)) ζ - X (mkc_pt T n k) ζ‖} ≤
          ENNReal.ofReal (max C 0 * (T / 2 ^ n) ^ (1 + β) / (lam * r ^ n) ^ p) := by
      intro k hk
      have hk' : k < 2 ^ n := Finset.mem_range.1 hk
      refine mkc_markov μ ((hX _).sub (hX _)) hp (by positivity) ?_
      refine (hmom _ (mkc_pt_mem hT n k hk'.le) _ (mkc_pt_mem hT n (k + 1) hk')).trans
        (ENNReal.ofReal_le_ofReal ?_)
      rw [mkc_pt_succ_sub, abs_of_pos (by positivity)]
      exact mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (by positivity) _)
    calc ∑ k ∈ Finset.range (2 ^ n),
          μ {ζ | lam * r ^ n < ‖X (mkc_pt T n (k + 1)) ζ - X (mkc_pt T n k) ζ‖}
        ≤ ∑ k ∈ Finset.range (2 ^ n),
          ENNReal.ofReal (max C 0 * (T / 2 ^ n) ^ (1 + β) / (lam * r ^ n) ^ p) :=
          Finset.sum_le_sum hk
      _ = ENNReal.ofReal ((2 : ℝ) ^ n *
          (max C 0 * (T / 2 ^ n) ^ (1 + β) / (lam * r ^ n) ^ p)) := by
          rw [ENNReal.ofReal_mul (by positivity)]
          simp [ENNReal.ofReal_pow]
      _ ≤ ENNReal.ofReal (Kc * q ^ n) := by
          apply ENNReal.ofReal_le_ofReal
          have := mkc_real_bound (T := T) (β := β) (p := p) (r := r) (q := q) (lam := lam)
            (Cp := max C 0) hT (le_max_right _ _) hr0 hqr hq0 hlam n
          simpa [hKc, mul_assoc] using this
  have hsum : Summable fun n : ℕ => Kc * q ^ n :=
    (summable_geometric_of_lt_one hq0.le hq1).mul_left _
  calc μ (mkc_G X T r lam)ᶜ ≤ μ (⋃ n : ℕ, ⋃ k ∈ Finset.range (2 ^ n),
        {ζ | lam * r ^ n < ‖X (mkc_pt T n (k + 1)) ζ - X (mkc_pt T n k) ζ‖}) := measure_mono hsub
    _ ≤ ∑' n : ℕ, μ (⋃ k ∈ Finset.range (2 ^ n),
        {ζ | lam * r ^ n < ‖X (mkc_pt T n (k + 1)) ζ - X (mkc_pt T n k) ζ‖}) :=
        measure_iUnion_le _
    _ ≤ ∑' n : ℕ, ENNReal.ofReal (Kc * q ^ n) := ENNReal.tsum_le_tsum hterm
    _ = ENNReal.ofReal (∑' n : ℕ, Kc * q ^ n) :=
        (ENNReal.ofReal_tsum_of_nonneg (fun n => by positivity) hsum).symm
    _ = ENNReal.ofReal (Kc / (1 - q)) := by
        rw [tsum_mul_left, tsum_geometric_of_lt_one hq0.le hq1, div_eq_mul_inv]

open Classical in
/-- The continuous version: on `{K < ∞}` the limit of the dyadic approximations, `0` elsewhere. -/
def mkc_Zc (t : ℝ) (ζ : Ω) : E :=
  if ζ ∈ mkc_Gs X T r then
    limUnder atTop (fun n => X (mkc_pt T n (mkc_idx T n (max 0 (min t T)))) ζ)
  else 0

theorem mkc_G_sub_Gs (hr : 0 ≤ r) {lam : ℝ} (hlam : 0 ≤ lam) : mkc_G X T r lam ⊆ mkc_Gs X T r := by
  intro ζ hζ
  exact Set.mem_iUnion.2 ⟨⌈lam⌉₊, mkc_G_mono X T r hr (Nat.le_ceil lam) hζ⟩

theorem mkc_Zc_of_notMem {ζ : Ω} (hζ : ζ ∉ mkc_Gs X T r) (t : ℝ) : mkc_Zc X T r t ζ = 0 := by
  simp [mkc_Zc, hζ]

variable [CompleteSpace E]

theorem mkc_Zc_tendsto (hT : 0 < T) (hr0 : 0 ≤ r) (hr1 : r < 1) {lam : ℝ} (hlam : 0 ≤ lam) {ζ : Ω}
    (hζ : ζ ∈ mkc_G X T r lam) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    Tendsto (fun n => X (mkc_pt T n (mkc_idx T n t)) ζ) atTop (𝓝 (mkc_Zc X T r t ζ)) := by
  obtain ⟨L, hL, -⟩ := mkc_limit (mkc_cons_xs X T ζ) hζ hlam hr0 hr1 hT ht
  have hclip : max 0 (min t T) = t := by
    rw [min_eq_left ht.2, max_eq_right ht.1]
  have : mkc_Zc X T r t ζ = L := by
    simp only [mkc_Zc, mkc_G_sub_Gs X T r hr0 hlam hζ, ite_true, hclip]
    exact hL.limUnder_eq
  rw [this]
  exact hL

theorem mkc_Zc_dist_le (hT : 0 < T) (hr0 : 0 ≤ r) (hr1 : r < 1) {lam : ℝ} (hlam : 0 ≤ lam) {ζ : Ω}
    (hζ : ζ ∈ mkc_G X T r lam) {t s : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (hs : s ∈ Set.Icc (0 : ℝ) T)
    (m : ℕ) (hts : |t - s| ≤ T / 2 ^ m) :
    ‖mkc_Zc X T r t ζ - mkc_Zc X T r s ζ‖ ≤ mkc_c r * (lam * r ^ m) :=
  mkc_modulus (mkc_cons_xs X T ζ) hζ hlam hr0 hr1 hT ht hs m hts
    (mkc_Zc_tendsto X T r hT hr0 hr1 hlam hζ ht) (mkc_Zc_tendsto X T r hT hr0 hr1 hlam hζ hs)

theorem mkc_small {c lam : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) {ε : ℝ} (hε : 0 < ε) :
    ∃ m : ℕ, c * (lam * r ^ m) < ε := by
  have : Tendsto (fun m : ℕ => c * (lam * r ^ m)) atTop (𝓝 (c * (lam * 0))) :=
    ((tendsto_pow_atTop_nhds_zero_of_lt_one hr0 hr1).const_mul lam).const_mul c
  rw [mul_zero, mul_zero] at this
  exact (this.eventually (gt_mem_nhds hε)).exists

theorem mkc_omegaE_le (hT : 0 < T) (hr0 : 0 ≤ r) (hr1 : r < 1) {lam : ℝ} (hlam : 0 ≤ lam) {ζ : Ω}
    (hζ : ζ ∈ mkc_G X T r lam) (m : ℕ) {δ : ℝ} (hδ : δ ≤ T / 2 ^ m) :
    omegaE (fun t => mkc_Zc X T r t ζ) T δ ≤ ENNReal.ofReal (mkc_c r * (lam * r ^ m)) := by
  unfold omegaE
  refine iSup₂_le fun s hs => iSup₂_le fun t ht => iSup_le fun hst => ?_
  rw [← ofReal_norm]
  exact ENNReal.ofReal_le_ofReal
    (mkc_Zc_dist_le X T r hT hr0 hr1 hlam hζ ht hs m (hst.trans hδ))

theorem mkc_continuous (hT : 0 < T) (hr0 : 0 ≤ r) (hr1 : r < 1) (ζ : Ω) :
    Continuous fun t : Set.Icc (0 : ℝ) T => mkc_Zc X T r t ζ := by
  by_cases hζ : ζ ∈ mkc_Gs X T r
  · obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hζ
    rw [Metric.continuous_iff]
    intro b ε hε
    obtain ⟨m', hm'⟩ := mkc_small (c := mkc_c r) (lam := (m : ℝ)) r hr0 hr1 hε
    refine ⟨T / 2 ^ m', by positivity, fun a ha => ?_⟩
    rw [Subtype.dist_eq, Real.dist_eq] at ha
    rw [dist_eq_norm]
    exact (mkc_Zc_dist_le X T r hT hr0 hr1 (Nat.cast_nonneg m) hm a.2 b.2 m' ha.le).trans_lt hm'
  · have : (fun t : Set.Icc (0 : ℝ) T => mkc_Zc X T r t ζ) = fun _ => 0 := by
      funext t; exact mkc_Zc_of_notMem X T r hζ _
    rw [this]; exact continuous_const

theorem mkc_Zc_meas (hT : 0 < T) (hr0 : 0 ≤ r) (hr1 : r < 1) (hX : ∀ t, Measurable (X t))
    (t : ℝ) : Measurable (mkc_Zc X T r t) := by
  have hf : ∀ n : ℕ, Measurable ((mkc_Gs X T r).indicator
      (fun ζ => X (mkc_pt T n (mkc_idx T n (max 0 (min t T)))) ζ)) :=
    fun n => (hX _).indicator (mkc_Gs_meas X T r hX)
  have htc : max 0 (min t T) ∈ Set.Icc (0 : ℝ) T :=
    ⟨le_max_left _ _, max_le hT.le (min_le_right _ _)⟩
  refine measurable_of_tendsto_metrizable hf (tendsto_pi_nhds.2 fun ζ => ?_)
  by_cases hζ : ζ ∈ mkc_Gs X T r
  · obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hζ
    have h := mkc_Zc_tendsto X T r hT hr0 hr1 (Nat.cast_nonneg m) hm htc
    have e : mkc_Zc X T r t ζ = mkc_Zc X T r (max 0 (min t T)) ζ := by
      have hclip : max 0 (min (max 0 (min t T)) T) = max 0 (min t T) := by
        rw [min_eq_left htc.2, max_eq_right htc.1]
      simp only [mkc_Zc, hζ, ite_true, hclip]
    rw [e]
    simpa [Set.indicator_of_mem hζ, mkc_Zc, hζ, htc] using h
  · simp only [Set.indicator_of_notMem hζ, mkc_Zc_of_notMem X T r hζ]
    exact tendsto_const_nhds

theorem mkc_tail_tendsto {p : ℝ} (hp : 0 < p) (K q : ℝ) :
    Tendsto (fun lam : ℝ => ENNReal.ofReal (K * lam ^ (-p) / (1 - q))) atTop (𝓝 0) := by
  have h : Tendsto (fun lam : ℝ => K * lam ^ (-p) / (1 - q)) atTop (𝓝 (K * 0 / (1 - q))) :=
    ((tendsto_rpow_neg_atTop hp).const_mul K).div_const _
  rw [mul_zero, zero_div] at h
  simpa using ENNReal.tendsto_ofReal h

theorem mkc_Gs_null (μ : Measure Ω) (hX : ∀ t, Measurable (X t)) {p β C q : ℝ}
    (hT : 0 < T) (hp : 0 < p)
    (hmom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖X t ζ - X s ζ‖ₑ ^ p ∂μ ≤ ENNReal.ofReal (C * |t - s| ^ (1 + β)))
    (hr0 : 0 < r) (hq0 : 0 < q) (hq1 : q < 1) (hqr : 1 ≤ q * 2 ^ β * r ^ p) :
    μ (mkc_Gs X T r)ᶜ = 0 := by
  refine le_antisymm ?_ zero_le
  refine ge_of_tendsto (mkc_tail_tendsto hp (max C 0 * T ^ (1 + β)) q)
    (eventually_atTop.2 ⟨1, fun lam hlam => ?_⟩)
  have hl : 0 < lam := lt_of_lt_of_le one_pos hlam
  refine le_trans (measure_mono ?_) (mkc_prob_bound X T r μ hX hT hp hmom hr0 hq0 hq1 hqr hl)
  exact Set.compl_subset_compl.2 (mkc_G_sub_Gs X T r hr0.le hl.le)

theorem mkc_omega_prob (μ : Measure Ω) (hX : ∀ t, Measurable (X t)) {p β C q : ℝ}
    (hT : 0 < T) (hp : 0 < p)
    (hmom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖X t ζ - X s ζ‖ₑ ^ p ∂μ ≤ ENNReal.ofReal (C * |t - s| ^ (1 + β)))
    (hr0 : 0 < r) (hr1 : r < 1) (hq0 : 0 < q) (hq1 : q < 1) (hqr : 1 ≤ q * 2 ^ β * r ^ p)
    {lam : ℝ} (hlam : 0 < lam) {ε : ℝ} (m : ℕ) (hm : mkc_c r * (lam * r ^ m) ≤ ε)
    {δ : ℝ} (hδ : δ ≤ T / 2 ^ m) :
    μ {ζ | ENNReal.ofReal ε < omegaE (fun t => mkc_Zc X T r t ζ) T δ} ≤
      ENNReal.ofReal (max C 0 * T ^ (1 + β) * lam ^ (-p) / (1 - q)) := by
  refine le_trans (measure_mono ?_) (mkc_prob_bound X T r μ hX hT hp hmom hr0 hq0 hq1 hqr hlam)
  intro ζ hζ hG
  have := mkc_omegaE_le X T r hT hr0.le hr1 hlam.le hG m hδ
  exact absurd (lt_of_lt_of_le hζ (this.trans (ENNReal.ofReal_le_ofReal hm))) (lt_irrefl _)

theorem mkc_Zc_ae_eq (μ : Measure Ω) [IsFiniteMeasure μ] (hX : ∀ t, Measurable (X t)) {p β C q : ℝ}
    (hT : 0 < T) (hp : 0 < p) (hβ : 0 < β)
    (hmom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖X t ζ - X s ζ‖ₑ ^ p ∂μ ≤ ENNReal.ofReal (C * |t - s| ^ (1 + β)))
    (hr0 : 0 < r) (hr1 : r < 1) (hq0 : 0 < q) (hq1 : q < 1) (hqr : 1 ≤ q * 2 ^ β * r ^ p)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) :
    mkc_Zc X T r t =ᵐ[μ] X t := by
  have hnull := mkc_Gs_null X T r μ hX hT hp hmom hr0 hq0 hq1 hqr
  have hae : ∀ᵐ ζ ∂μ, ζ ∈ mkc_Gs X T r := by
    exact ae_iff.2 hnull
  set f : ℕ → Ω → E := fun n ζ => X (mkc_pt T n (mkc_idx T n t)) ζ with hf
  have h1 : TendstoInMeasure μ f atTop (X t) := by
    refine tendstoInMeasure_of_ne_top fun ε hε hεt => ?_
    set e : ℝ := ε.toReal with he
    have hepos : 0 < e := ENNReal.toReal_pos hε.ne' hεt
    have hεe : ε = ENNReal.ofReal e := (ENNReal.ofReal_toReal hεt).symm
    have hbound : ∀ n : ℕ, μ {ζ | ε ≤ edist (f n ζ) (X t ζ)} ≤
        ENNReal.ofReal (max C 0 * (T / 2 ^ n) ^ (1 + β) / (e / 2) ^ p) := by
      intro n
      have hmem : mkc_pt T n (mkc_idx T n t) ∈ Set.Icc (0 : ℝ) T :=
        mkc_pt_mem hT n _ (mkc_idx_le hT ht.2 n)
      have hpt := mkc_pt_idx hT ht.1 n
      refine le_trans (measure_mono ?_) (mkc_markov μ
        (d := fun ζ => X (mkc_pt T n (mkc_idx T n t)) ζ - X t ζ) ((hX _).sub (hX _)) hp
        (c := e / 2) (by positivity) (M := max C 0 * (T / 2 ^ n) ^ (1 + β)) ?_)
      · intro ζ hζ
        simp only [Set.mem_ofPred_eq, edist_eq_enorm_sub, hεe] at hζ ⊢
        rw [← ofReal_norm, ENNReal.ofReal_le_ofReal_iff (norm_nonneg _)] at hζ
        have h' : e ≤ ‖X (mkc_pt T n (mkc_idx T n t)) ζ - X t ζ‖ := hζ
        show e / 2 < ‖X (mkc_pt T n (mkc_idx T n t)) ζ - X t ζ‖
        linarith
      · refine (hmom t ht _ hmem).trans (ENNReal.ofReal_le_ofReal ?_)
        have habs : |mkc_pt T n (mkc_idx T n t) - t| ≤ T / 2 ^ n := by
          rw [abs_sub_comm, abs_of_nonneg (by linarith [hpt.1])]
          linarith [hpt.2]
        calc C * |mkc_pt T n (mkc_idx T n t) - t| ^ (1 + β)
            ≤ max C 0 * |mkc_pt T n (mkc_idx T n t) - t| ^ (1 + β) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg (abs_nonneg _) _)
          _ ≤ max C 0 * (T / 2 ^ n) ^ (1 + β) := by
              apply mul_le_mul_of_nonneg_left _ (le_max_right _ _)
              exact Real.rpow_le_rpow (abs_nonneg _) habs (by linarith)
    have hlim : Tendsto (fun n : ℕ => max C 0 * (T / 2 ^ n) ^ (1 + β) / (e / 2) ^ p) atTop
        (𝓝 0) := by
      have h0 : Tendsto (fun n : ℕ => T / 2 ^ n) atTop (𝓝 0) := by
        have := (tendsto_pow_atTop_nhds_zero_of_lt_one (by norm_num : (0 : ℝ) ≤ 1 / 2)
          (by norm_num)).const_mul T
        rw [mul_zero] at this
        simpa [div_eq_mul_inv, one_div, inv_pow] using this
      have h1 : Tendsto (fun n : ℕ => (T / 2 ^ n) ^ (1 + β)) atTop (𝓝 (0 ^ (1 + β))) :=
        ((Real.continuousAt_rpow_const 0 (1 + β) (Or.inr (by linarith))).tendsto).comp h0
      rw [Real.zero_rpow (by linarith)] at h1
      have := (h1.const_mul (max C 0)).div_const ((e / 2) ^ p)
      simpa using this
    exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds
      (by simpa using ENNReal.tendsto_ofReal hlim) (fun _ => zero_le) hbound
  have h2 : ∀ᵐ ζ ∂μ, Tendsto (fun n => f n ζ) atTop (𝓝 (mkc_Zc X T r t ζ)) := by
    filter_upwards [hae] with ζ hζ
    obtain ⟨m, hm⟩ := Set.mem_iUnion.1 hζ
    exact mkc_Zc_tendsto X T r hT hr0.le hr1 (Nat.cast_nonneg m) hm ht
  have h3 : TendstoInMeasure μ f atTop (mkc_Zc X T r t) :=
    tendstoInMeasure_of_tendsto_ae (fun n => (hX _).aestronglyMeasurable) h2
  exact tendstoInMeasure_ae_unique h3 h1

end Prob

section Final

theorem mkc_consts {β p : ℝ} (hβ : 0 < β) (hp : 0 < p) :
    ∃ r q : ℝ, 0 < r ∧ r < 1 ∧ 0 < q ∧ q < 1 ∧ 1 ≤ q * 2 ^ β * r ^ p := by
  set q : ℝ := (2 : ℝ) ^ (-(β / 2)) with hq
  have hq0 : 0 < q := Real.rpow_pos_of_pos (by norm_num) _
  have hq1 : q < 1 := Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set r : ℝ := q ^ (1 / p) with hr
  have hr0 : 0 < r := Real.rpow_pos_of_pos hq0 _
  have hr1 : r < 1 := Real.rpow_lt_one hq0.le hq1 (by positivity)
  have hrp : r ^ p = q := by
    rw [hr, ← Real.rpow_mul hq0.le, one_div_mul_cancel hp.ne', Real.rpow_one]
  refine ⟨r, q, hr0, hr1, hq0, hq1, le_of_eq ?_⟩
  rw [hrp, hq, ← Real.rpow_add (by norm_num), ← Real.rpow_add (by norm_num)]
  rw [show -(β / 2) + β + -(β / 2) = 0 by ring, Real.rpow_zero]

theorem mkc_contPathOf_apply {E : Type*} [NormedAddCommGroup E] [MeasurableSpace E] [BorelSpace E]
    [SecondCountableTopology E] [CompleteSpace E] {Ω : Type*} [MeasurableSpace Ω]
    (X : ℝ → Ω → E) {T : ℝ} (hT : 0 < T) {r : ℝ} (hr0 : 0 ≤ r) (hr1 : r < 1) (ζ : Ω)
    (s : Set.Icc (0 : ℝ) T) :
    contPathOf T (fun t => mkc_Zc X T r t ζ) s = mkc_Zc X T r s ζ := by
  unfold contPathOf
  rw [dif_pos (mkc_continuous X T r hT hr0 hr1 ζ)]
  rfl

/-- Kolmogorov-Chentsov with a uniform modulus: statement copied verbatim from
`HRS.Whole.AppendixALemmas.kolmogorov_modulus_tightness`. -/
theorem kolmogorov_modulus_tightness_proof {E : Type*} [NormedAddCommGroup E]
    [InnerProductSpace ℝ E]
    [CompleteSpace E] [TopologicalSpace.SeparableSpace E] [MeasurableSpace E] [BorelSpace E]
    (T : ℝ) (hT : 0 < T) {Ω : ℕ → Type*} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (Z : ∀ N, ℝ → Ω N → E)
    (hZmeas : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Z N t)) (p β C : ℝ) (hp : 0 < p) (hβ : 0 < β)
    (hmom : ∀ N : ℕ, 1 ≤ N → ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ ζ, ‖Z N t ζ - Z N s ζ‖ₑ ^ p ∂(P N) ≤ ENNReal.ofReal (C * |t - s| ^ (1 + β))) :
    ∃ Zc : ∀ N, ℝ → Ω N → E, ContVersionTight T P Z Zc := by
  obtain ⟨r, q, hr0, hr1, hq0, hq1, hqr⟩ := mkc_consts hβ hp
  have hmod : ∀ ε : ℝ, 0 < ε → Tendsto (fun δ : ℝ =>
      ⨆ N : ℕ, ⨆ (_ : 1 ≤ N),
        P N {ζ | ENNReal.ofReal ε < omegaE (fun t => mkc_Zc (Z N) T r t ζ) T δ})
      (𝓝[>] 0) (𝓝 0) := by
    intro ε hε
    refine ENNReal.tendsto_nhds_zero.2 fun η hη => ?_
    obtain ⟨η', hη'pos, hη'le⟩ : ∃ η' : ℝ, 0 < η' ∧ ENNReal.ofReal η' ≤ η := by
      by_cases ht : η = ⊤
      · exact ⟨1, one_pos, by simp [ht]⟩
      · exact ⟨η.toReal, ENNReal.toReal_pos hη.ne' ht, by rw [ENNReal.ofReal_toReal ht]⟩
    have hη'pos' : (0 : ℝ≥0∞) < ENNReal.ofReal η' := ENNReal.ofReal_pos.2 hη'pos
    obtain ⟨lam, hlamb, hlam⟩ :=
      (((mkc_tail_tendsto hp (max C 0 * T ^ (1 + β)) q).eventually (gt_mem_nhds hη'pos')).and
        (eventually_gt_atTop (0 : ℝ))).exists
    obtain ⟨m, hm⟩ := mkc_small (c := mkc_c r) (lam := lam) r hr0.le hr1 hε
    have hpos : (0 : ℝ) < T / 2 ^ m := by positivity
    filter_upwards [Ioo_mem_nhdsGT hpos] with δ hδ
    refine iSup₂_le fun N hN => ?_
    refine le_trans ?_ hη'le
    refine le_trans (mkc_omega_prob (Z N) T r (P N) (hZmeas N hN) hT hp (hmom N hN) hr0 hr1 hq0 hq1
      hqr hlam m hm.le hδ.2.le) hlamb.le
  have hcont : ∀ N : ℕ, 1 ≤ N → ∀ᵐ ζ ∂(P N),
      Continuous fun t : Set.Icc (0 : ℝ) T => mkc_Zc (Z N) T r t ζ :=
    fun N _ => ae_of_all _ (mkc_continuous (Z N) T r hT hr0.le hr1)
  have hZc : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (mkc_Zc (Z N) T r t) :=
    fun N hN t => mkc_Zc_meas (Z N) T r hT hr0.le hr1 (hZmeas N hN) t
  have hpath : ∀ N : ℕ, 1 ≤ N →
      Measurable fun ζ => contPathOf T (fun t => mkc_Zc (Z N) T r t ζ) := by
    intro N hN
    refine ContinuousMap.measurable_iff_eval.2 fun s => ?_
    have : (fun ζ => contPathOf T (fun t => mkc_Zc (Z N) T r t ζ) s) =
        fun ζ => mkc_Zc (Z N) T r s ζ := by
      funext ζ; exact mkc_contPathOf_apply (Z N) hT hr0.le hr1 ζ s
    rw [this]
    exact hZc N hN s
  have hae : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∀ᵐ ζ ∂(P N), mkc_Zc (Z N) T r t ζ = Z N t ζ :=
    fun N hN t ht => mkc_Zc_ae_eq (Z N) T r (P N) (hZmeas N hN) hT hp hβ (hmom N hN) hr0 hr1 hq0
      hq1 hqr ht
  refine ⟨fun N t ζ => mkc_Zc (Z N) T r t ζ, hae, hcont, hpath, hmod, fun htight => ?_⟩
  refine HRS.MP.PathTight.path_tightness_criterion_proof T hT P
    (fun N t ζ => mkc_Zc (Z N) T r t ζ) hZc hcont hpath (Set.Icc (0 : ℝ) T) subset_rfl
    subset_closure ?_ hmod
  intro t ht
  have hset : {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (fun ζ => mkc_Zc (Z N) T r t ζ)} =
      {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (P N).map (Z N t)} := by
    ext μ
    constructor
    · rintro ⟨N, hN, rfl⟩
      exact ⟨N, hN, Measure.map_congr (hae N hN t ht)⟩
    · rintro ⟨N, hN, rfl⟩
      exact ⟨N, hN, (Measure.map_congr (hae N hN t ht)).symm⟩
  rw [hset]
  exact htight t ht

example := (@kolmogorov_modulus_tightness_proof :
  type_of% @HRS.Whole.AppendixALemmas.kolmogorov_modulus_tightness)

end Final

end HRS.MP.KC
