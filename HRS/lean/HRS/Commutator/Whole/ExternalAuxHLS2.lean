import HRS.Commutator.Whole.ExternalAuxHLS1

/-!
# Hedberg's pointwise inequality for the Riesz potential (packet X-HLS, part 2)

`I_σ F (x) = ∫ |x-y|^{σ-d} F(y) dy` is split into dyadic shells; near shells are bounded by the
dyadic maximal function, far shells by Hölder.
-/

open MeasureTheory Metric Set Filter
open scoped ENNReal NNReal

noncomputable section

namespace HRS.Commutator.Whole

variable {d : ℕ}

local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- The Riesz kernel `|z|^{σ-d}` (as an extended nonnegative number). -/
def cmxHLS_k (σ : ℝ) (z : 𝔼) : ℝ≥0∞ := ENNReal.ofReal (‖z‖ ^ (σ - (d : ℝ)))

/-- The Riesz potential of a nonnegative function. -/
def cmxHLS_I (σ : ℝ) (F : 𝔼 → ℝ≥0∞) (x : 𝔼) : ℝ≥0∞ := ∫⁻ y, cmxHLS_k σ (x - y) * F y

/-- The dyadic shell `2^j ≤ |x-y| < 2^{j+1}`. -/
def cmxHLS_S (x : 𝔼) (j : ℤ) : Set 𝔼 := {y | (2 : ℝ) ^ j ≤ ‖x - y‖ ∧ ‖x - y‖ < (2 : ℝ) ^ (j + 1)}

lemma cmxHLS_S_meas (x : 𝔼) (j : ℤ) : MeasurableSet (cmxHLS_S x j) := by
  have hm : Measurable fun y : 𝔼 => ‖x - y‖ := measurable_norm.comp (measurable_const.sub measurable_id)
  have h1 : MeasurableSet {y : 𝔼 | (2 : ℝ) ^ j ≤ ‖x - y‖} := measurableSet_le measurable_const hm
  have h2 : MeasurableSet {y : 𝔼 | ‖x - y‖ < (2 : ℝ) ^ (j + 1)} := measurableSet_lt hm measurable_const
  exact h1.inter h2

lemma cmxHLS_S_sub (x : 𝔼) (j : ℤ) : cmxHLS_S x j ⊆ closedBall x ((2 : ℝ) ^ (j + 1)) := by
  intro y hy
  rw [mem_closedBall, dist_comm, dist_eq_norm]
  exact hy.2.le

lemma cmxHLS_k_zero {σ : ℝ} (hσd : σ < d) : cmxHLS_k σ (0 : 𝔼) = 0 := by
  unfold cmxHLS_k
  rw [norm_zero, Real.zero_rpow (by linarith : σ - (d : ℝ) ≠ 0)]
  simp

lemma cmxHLS_k_le {σ : ℝ} (hσd : σ < d) (x : 𝔼) (j : ℤ) {y : 𝔼} (hy : y ∈ cmxHLS_S x j) :
    cmxHLS_k σ (x - y) ≤ ENNReal.ofReal (((2 : ℝ) ^ j) ^ (σ - (d : ℝ))) := by
  unfold cmxHLS_k
  apply ENNReal.ofReal_le_ofReal
  exact Real.rpow_le_rpow_of_nonpos (zpow_pos (by norm_num) _) hy.1 (by linarith)

lemma cmxHLS_alg1 {σ : ℝ} {r : ℝ} (hr : 0 < r) :
    r ^ (σ - (d : ℝ)) * (2 * r) ^ d = 2 ^ d * r ^ σ := by
  rw [mul_pow, Real.rpow_sub hr, Real.rpow_natCast]
  have : r ^ d ≠ 0 := by positivity
  field_simp

lemma cmxHLS_near_shell {σ : ℝ} (hσd : σ < d) (F : 𝔼 → ℝ≥0∞) (x : 𝔼) (j : ℤ) :
    ∫⁻ y in cmxHLS_S x j, cmxHLS_k σ (x - y) * F y ≤
      ENNReal.ofReal (2 ^ d * ((2 : ℝ) ^ j) ^ σ) * volume (closedBall (0 : 𝔼) 1) *
        cmxHLS_Md F x := by
  set r : ℝ := (2 : ℝ) ^ j with hr
  have hr0 : 0 < r := zpow_pos (by norm_num) _
  have hr1 : (2 : ℝ) ^ (j + 1) = 2 * r := by
    rw [hr, zpow_add_one₀ (by norm_num), mul_comm]
  calc ∫⁻ y in cmxHLS_S x j, cmxHLS_k σ (x - y) * F y
      ≤ ∫⁻ y in cmxHLS_S x j, ENNReal.ofReal (r ^ (σ - (d : ℝ))) * F y :=
        setLIntegral_mono' (cmxHLS_S_meas x j) fun y hy =>
          mul_le_mul_left (cmxHLS_k_le hσd x j hy) _
    _ = ENNReal.ofReal (r ^ (σ - (d : ℝ))) * ∫⁻ y in cmxHLS_S x j, F y :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (r ^ (σ - (d : ℝ))) * ∫⁻ y in closedBall x ((2 : ℝ) ^ (j + 1)), F y :=
        mul_le_mul_right (lintegral_mono_set (cmxHLS_S_sub x j)) _
    _ ≤ ENNReal.ofReal (r ^ (σ - (d : ℝ))) *
          (volume (closedBall x ((2 : ℝ) ^ (j + 1))) * cmxHLS_Md F x) :=
        mul_le_mul_right (cmxHLS_lintegral_le F x (j + 1)) _
    _ = ENNReal.ofReal (2 ^ d * r ^ σ) * volume (closedBall (0 : 𝔼) 1) * cmxHLS_Md F x := by
        rw [hr1, cmxHLS_vol_closedBall x (by positivity), ← cmxHLS_alg1 hr0,
          ENNReal.ofReal_mul (by positivity)]
        ring


lemma cmxHLS_alg2 {σ p q : ℝ} (hpq : p.HolderConjugate q) {r : ℝ} (hr : 0 < r) :
    r ^ (σ - (d : ℝ)) * ((2 * r) ^ d) ^ (1 / q) =
      2 ^ ((d : ℝ) / q) * r ^ (σ - (d : ℝ) / p) := by
  have h1 : ((2 * r) ^ d) ^ (1 / q) = (2 * r) ^ ((d : ℝ) * (1 / q)) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
  rw [h1, Real.mul_rpow (by norm_num) hr.le, ← mul_assoc, mul_comm (r ^ (σ - (d : ℝ))),
    mul_assoc, ← Real.rpow_add hr]
  have h2 : (d : ℝ) / p = d - d * (1 / q) := by
    have := hpq.inv_add_inv_eq_one
    have h3 : (1 : ℝ) / p = 1 - 1 / q := by
      rw [one_div, one_div]; linarith
    rw [div_eq_mul_one_div, h3]; ring
  have h4 : σ - (d : ℝ) + (d : ℝ) * (1 / q) = σ - (d : ℝ) / p := by rw [h2]; ring
  have h5 : (d : ℝ) * (1 / q) = (d : ℝ) / q := by ring
  rw [h4, h5]

lemma cmxHLS_far_shell {σ p q : ℝ} (hσd : σ < d) (hpq : p.HolderConjugate q) {F : 𝔼 → ℝ≥0∞}
    (hF : Measurable F) (x : 𝔼) (j : ℤ) :
    ∫⁻ y in cmxHLS_S x j, cmxHLS_k σ (x - y) * F y ≤
      ENNReal.ofReal (2 ^ ((d : ℝ) / q) * ((2 : ℝ) ^ j) ^ (σ - (d : ℝ) / p)) *
        volume (closedBall (0 : 𝔼) 1) ^ (1 / q) * (∫⁻ y, F y ^ p) ^ (1 / p) := by
  set r : ℝ := (2 : ℝ) ^ j with hr
  have hr0 : 0 < r := zpow_pos (by norm_num) _
  have hr1 : (2 : ℝ) ^ (j + 1) = 2 * r := by
    rw [hr, zpow_add_one₀ (by norm_num), mul_comm]
  have hq0 : 0 ≤ 1 / q := by have := hpq.symm.pos; positivity
  have hp0 : 0 ≤ 1 / p := by have := hpq.pos; positivity
  have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq (volume.restrict (cmxHLS_S x j)) hpq
    (f := F) (g := fun _ => (1 : ℝ≥0∞)) hF.aemeasurable aemeasurable_const
  have hH' : ∫⁻ y in cmxHLS_S x j, F y ≤
      (∫⁻ y, F y ^ p) ^ (1 / p) * volume (cmxHLS_S x j) ^ (1 / q) := by
    simp only [Pi.mul_apply, mul_one, ENNReal.one_rpow, lintegral_const, Measure.restrict_apply_univ,
      one_mul] at hH
    exact hH.trans (mul_le_mul_left (ENNReal.rpow_le_rpow (setLIntegral_le_lintegral _ _) hp0) _)
  have hV : volume (cmxHLS_S x j) ≤ ENNReal.ofReal ((2 * r) ^ d) * volume (closedBall (0 : 𝔼) 1) := by
    rw [← cmxHLS_vol_closedBall x (by positivity), ← hr1]
    exact measure_mono (cmxHLS_S_sub x j)
  calc ∫⁻ y in cmxHLS_S x j, cmxHLS_k σ (x - y) * F y
      ≤ ∫⁻ y in cmxHLS_S x j, ENNReal.ofReal (r ^ (σ - (d : ℝ))) * F y :=
        setLIntegral_mono' (cmxHLS_S_meas x j) fun y hy =>
          mul_le_mul_left (cmxHLS_k_le hσd x j hy) _
    _ = ENNReal.ofReal (r ^ (σ - (d : ℝ))) * ∫⁻ y in cmxHLS_S x j, F y :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (r ^ (σ - (d : ℝ))) *
          ((∫⁻ y, F y ^ p) ^ (1 / p) * volume (cmxHLS_S x j) ^ (1 / q)) :=
        mul_le_mul_right hH' _
    _ ≤ ENNReal.ofReal (r ^ (σ - (d : ℝ))) *
          ((∫⁻ y, F y ^ p) ^ (1 / p) *
            (ENNReal.ofReal ((2 * r) ^ d) * volume (closedBall (0 : 𝔼) 1)) ^ (1 / q)) := by
        gcongr
    _ = ENNReal.ofReal (2 ^ ((d : ℝ) / q) * r ^ (σ - (d : ℝ) / p)) *
          volume (closedBall (0 : 𝔼) 1) ^ (1 / q) * (∫⁻ y, F y ^ p) ^ (1 / p) := by
        rw [← cmxHLS_alg2 hpq hr0, ENNReal.mul_rpow_of_nonneg _ _ hq0,
          ENNReal.ofReal_rpow_of_nonneg (by positivity) hq0,
          ENNReal.ofReal_mul (by positivity)]
        ring


lemma cmxHLS_cover {σ : ℝ} (hσd : σ < d) (F : 𝔼 → ℝ≥0∞) (x : 𝔼) (m : ℤ) :
    cmxHLS_I σ F x ≤
      (∑' i : ℕ, ∫⁻ y in cmxHLS_S x (m - 1 - i), cmxHLS_k σ (x - y) * F y) +
      ∑' i : ℕ, ∫⁻ y in cmxHLS_S x (m + i), cmxHLS_k σ (x - y) * F y := by
  have hsupp : Function.support (fun y => cmxHLS_k σ (x - y) * F y) ⊆
      (⋃ i : ℕ, cmxHLS_S x (m - 1 - i)) ∪ (⋃ i : ℕ, cmxHLS_S x (m + i)) := by
    intro y hy
    have hy' : cmxHLS_k σ (x - y) * F y ≠ 0 := hy
    have hk : cmxHLS_k σ (x - y) ≠ 0 := left_ne_zero_of_mul hy'
    have hxy : x - y ≠ 0 := fun h => hk (by rw [h]; exact cmxHLS_k_zero hσd)
    have hpos : 0 < ‖x - y‖ := norm_pos_iff.2 hxy
    obtain ⟨n, hn⟩ := exists_mem_Ico_zpow hpos (by norm_num : (1 : ℝ) < 2)
    have hyS : y ∈ cmxHLS_S x n := hn
    by_cases hnm : n < m
    · left
      refine mem_iUnion.2 ⟨(m - 1 - n).toNat, ?_⟩
      have : m - 1 - ((m - 1 - n).toNat : ℤ) = n := by
        rw [Int.toNat_of_nonneg (by omega)]; ring
      rw [this]; exact hyS
    · right
      refine mem_iUnion.2 ⟨(n - m).toNat, ?_⟩
      have : m + ((n - m).toNat : ℤ) = n := by
        rw [Int.toNat_of_nonneg (by omega)]; ring
      rw [this]; exact hyS
  unfold cmxHLS_I
  rw [← setLIntegral_eq_of_support_subset (μ := volume) hsupp]
  refine (lintegral_union_le _ _ _).trans (add_le_add (lintegral_iUnion_le _ _)
    (lintegral_iUnion_le _ _))

lemma cmxHLS_zpow_rpow (m k : ℤ) (e : ℝ) :
    ((2 : ℝ) ^ (m + k)) ^ e = ((2 : ℝ) ^ m) ^ e * ((2 : ℝ) ^ e) ^ k := by
  rw [zpow_add₀ (by norm_num), Real.mul_rpow (zpow_pos (by norm_num) _).le
    (zpow_pos (by norm_num) _).le]
  congr 1
  rw [← Real.rpow_intCast, ← Real.rpow_mul (by norm_num), ← Real.rpow_intCast,
    ← Real.rpow_mul (by norm_num), mul_comm]

lemma cmxHLS_near_sum {σ : ℝ} (hσ : 0 < σ) (hσd : σ < d) (F : 𝔼 → ℝ≥0∞) (x : 𝔼) (m : ℤ) :
    ∑' i : ℕ, ∫⁻ y in cmxHLS_S x (m - 1 - i), cmxHLS_k σ (x - y) * F y ≤
      ENNReal.ofReal (2 ^ d) * volume (closedBall (0 : 𝔼) 1) *
        (1 - ENNReal.ofReal (((2 : ℝ) ^ σ)⁻¹))⁻¹ *
        (ENNReal.ofReal (((2 : ℝ) ^ m) ^ σ) * cmxHLS_Md F x) := by
  set ρ : ℝ := ((2 : ℝ) ^ σ)⁻¹ with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hρ1 : ρ ≤ 1 := by
    rw [hρ]; exact inv_le_one_of_one_le₀ (Real.one_le_rpow (by norm_num) hσ.le)
  have hterm : ∀ i : ℕ, ∫⁻ y in cmxHLS_S x (m - 1 - i), cmxHLS_k σ (x - y) * F y ≤
      (ENNReal.ofReal (2 ^ d) * volume (closedBall (0 : 𝔼) 1) *
        (ENNReal.ofReal (((2 : ℝ) ^ m) ^ σ) * cmxHLS_Md F x)) * ENNReal.ofReal ρ ^ i := by
    intro i
    refine (cmxHLS_near_shell hσd F x (m - 1 - i)).trans ?_
    have h1 : ((2 : ℝ) ^ (m - 1 - (i : ℤ))) ^ σ = ((2 : ℝ) ^ m) ^ σ * ρ ^ (i + 1) := by
      have := cmxHLS_zpow_rpow m (-((i : ℤ) + 1)) σ
      rw [show m - 1 - (i : ℤ) = m + (-((i : ℤ) + 1)) by ring, this, zpow_neg, ← inv_zpow,
        ← hρ]
      norm_cast
    have h2 : ρ ^ (i + 1) ≤ ρ ^ i := pow_le_pow_of_le_one hρ0 hρ1 (Nat.le_succ i)
    rw [h1]
    have h3 : ENNReal.ofReal (2 ^ d * (((2 : ℝ) ^ m) ^ σ * ρ ^ (i + 1))) ≤
        ENNReal.ofReal (2 ^ d) * ENNReal.ofReal (((2 : ℝ) ^ m) ^ σ) * ENNReal.ofReal ρ ^ i := by
      rw [← ENNReal.ofReal_pow hρ0, ← ENNReal.ofReal_mul (by positivity),
        ← ENNReal.ofReal_mul (by positivity)]
      apply ENNReal.ofReal_le_ofReal
      have : 0 ≤ (2 : ℝ) ^ d * ((2 : ℝ) ^ m) ^ σ := by positivity
      calc (2 : ℝ) ^ d * (((2 : ℝ) ^ m) ^ σ * ρ ^ (i + 1))
          = ((2 : ℝ) ^ d * ((2 : ℝ) ^ m) ^ σ) * ρ ^ (i + 1) := by ring
        _ ≤ ((2 : ℝ) ^ d * ((2 : ℝ) ^ m) ^ σ) * ρ ^ i := by gcongr
    calc ENNReal.ofReal (2 ^ d * (((2 : ℝ) ^ m) ^ σ * ρ ^ (i + 1))) *
          volume (closedBall (0 : 𝔼) 1) * cmxHLS_Md F x
        ≤ (ENNReal.ofReal (2 ^ d) * ENNReal.ofReal (((2 : ℝ) ^ m) ^ σ) * ENNReal.ofReal ρ ^ i) *
          volume (closedBall (0 : 𝔼) 1) * cmxHLS_Md F x := by gcongr
      _ = _ := by ring
  calc ∑' i : ℕ, ∫⁻ y in cmxHLS_S x (m - 1 - i), cmxHLS_k σ (x - y) * F y
      ≤ ∑' i : ℕ, (ENNReal.ofReal (2 ^ d) * volume (closedBall (0 : 𝔼) 1) *
        (ENNReal.ofReal (((2 : ℝ) ^ m) ^ σ) * cmxHLS_Md F x)) * ENNReal.ofReal ρ ^ i :=
        ENNReal.tsum_le_tsum hterm
    _ = _ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        ring

lemma cmxHLS_far_sum {σ p q : ℝ} (hσd : σ < d) (hpq : p.HolderConjugate q)
    (hτ : σ - (d : ℝ) / p < 0) {F : 𝔼 → ℝ≥0∞} (hF : Measurable F) (x : 𝔼) (m : ℤ) :
    ∑' i : ℕ, ∫⁻ y in cmxHLS_S x (m + i), cmxHLS_k σ (x - y) * F y ≤
      ENNReal.ofReal (2 ^ ((d : ℝ) / q)) * volume (closedBall (0 : 𝔼) 1) ^ (1 / q) *
        (1 - ENNReal.ofReal ((2 : ℝ) ^ (σ - (d : ℝ) / p)))⁻¹ *
        (ENNReal.ofReal (((2 : ℝ) ^ m) ^ (σ - (d : ℝ) / p)) * (∫⁻ y, F y ^ p) ^ (1 / p)) := by
  set e : ℝ := σ - (d : ℝ) / p with he
  set ρ : ℝ := (2 : ℝ) ^ e with hρ
  have hρ0 : 0 ≤ ρ := by positivity
  have hterm : ∀ i : ℕ, ∫⁻ y in cmxHLS_S x (m + i), cmxHLS_k σ (x - y) * F y ≤
      (ENNReal.ofReal (2 ^ ((d : ℝ) / q)) * volume (closedBall (0 : 𝔼) 1) ^ (1 / q) *
        (ENNReal.ofReal (((2 : ℝ) ^ m) ^ e) * (∫⁻ y, F y ^ p) ^ (1 / p))) *
          ENNReal.ofReal ρ ^ i := by
    intro i
    refine (cmxHLS_far_shell hσd hpq hF x (m + i)).trans ?_
    have h1 : ((2 : ℝ) ^ (m + (i : ℤ))) ^ e = ((2 : ℝ) ^ m) ^ e * ρ ^ i := by
      have := cmxHLS_zpow_rpow m (i : ℤ) e
      rw [this, zpow_natCast]
    have h3 : ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / q) * (((2 : ℝ) ^ m) ^ e * ρ ^ i)) =
        ENNReal.ofReal ((2 : ℝ) ^ ((d : ℝ) / q)) * ENNReal.ofReal (((2 : ℝ) ^ m) ^ e) *
          ENNReal.ofReal ρ ^ i := by
      rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul (by positivity),
        ENNReal.ofReal_pow hρ0, mul_assoc]
    rw [← he, h1, h3]
    apply le_of_eq; ring
  calc ∑' i : ℕ, ∫⁻ y in cmxHLS_S x (m + i), cmxHLS_k σ (x - y) * F y
      ≤ ∑' i : ℕ, (ENNReal.ofReal (2 ^ ((d : ℝ) / q)) * volume (closedBall (0 : 𝔼) 1) ^ (1 / q) *
        (ENNReal.ofReal (((2 : ℝ) ^ m) ^ e) * (∫⁻ y, F y ^ p) ^ (1 / p))) *
          ENNReal.ofReal ρ ^ i := ENNReal.tsum_le_tsum hterm
    _ = _ := by
        rw [ENNReal.tsum_mul_left, ENNReal.tsum_geometric]
        ring


lemma cmxHLS_opt {σ τ α β a A : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) (hα : 0 ≤ α) (hβ : 0 ≤ β)
    (ha : 0 < a) (hA : 0 < A) :
    ∃ m : ℤ, α * (((2 : ℝ) ^ m) ^ σ * a) + β * (((2 : ℝ) ^ m) ^ (-τ) * A) ≤
      (α + β * (2 : ℝ) ^ τ) * (a ^ (1 - σ / (σ + τ)) * A ^ (σ / (σ + τ))) := by
  set ρ : ℝ := (A / a) ^ (1 / (σ + τ)) with hρ
  have hρ0 : 0 < ρ := Real.rpow_pos_of_pos (div_pos hA ha) _
  obtain ⟨m, hm⟩ := exists_mem_Ico_zpow hρ0 (by norm_num : (1 : ℝ) < 2)
  refine ⟨m, ?_⟩
  set u : ℝ := (2 : ℝ) ^ m with hu
  have hu0 : 0 < u := zpow_pos (by norm_num) _
  have hu1 : u ≤ ρ := hm.1
  have hu2 : ρ < 2 * u := by
    have := hm.2
    rw [zpow_add_one₀ (by norm_num)] at this
    rw [hu]; linarith
  have hστ : 0 < σ + τ := by linarith
  have key : ρ ^ (σ + τ) = A / a := by
    rw [hρ, ← Real.rpow_mul (div_pos hA ha).le, one_div, inv_mul_cancel₀ hστ.ne', Real.rpow_one]
  have h1 : u ^ σ ≤ ρ ^ σ := Real.rpow_le_rpow hu0.le hu1 hσ.le
  have h2 : u ^ (-τ) ≤ 2 ^ τ * ρ ^ (-τ) := by
    have hh : (ρ / 2) ≤ u := by linarith
    have := Real.rpow_le_rpow_of_nonpos (by positivity : 0 < ρ / 2) hh (by linarith : -τ ≤ 0)
    refine this.trans (le_of_eq ?_)
    rw [Real.div_rpow hρ0.le (by norm_num), Real.rpow_neg (by norm_num : (0:ℝ) ≤ 2),
      Real.rpow_neg hρ0.le]
    field_simp
  have h3 : ρ ^ (-τ) * A = ρ ^ σ * a := by
    have : ρ ^ (-τ) = ρ ^ σ * (ρ ^ (σ + τ))⁻¹ := by
      rw [← Real.rpow_neg hρ0.le, ← Real.rpow_add hρ0]; congr 1; ring
    rw [this, key]
    field_simp
  have h4 : ρ ^ σ * a = a ^ (1 - σ / (σ + τ)) * A ^ (σ / (σ + τ)) := by
    have e1 : ρ ^ σ = (A / a) ^ (σ / (σ + τ)) := by
      rw [hρ, ← Real.rpow_mul (div_pos hA ha).le]; congr 1; field_simp
    rw [e1, Real.div_rpow hA.le ha.le, Real.rpow_sub ha, Real.rpow_one]
    field_simp
  calc α * (u ^ σ * a) + β * (u ^ (-τ) * A)
      ≤ α * (ρ ^ σ * a) + β * (2 ^ τ * ρ ^ (-τ) * A) := by gcongr
    _ = (α + β * 2 ^ τ) * (ρ ^ σ * a) := by rw [mul_assoc (2 ^ τ), h3]; ring
    _ = _ := by rw [h4]


lemma cmxHLS_opt_enn {σ τ : ℝ} (hσ : 0 < σ) (hτ : 0 < τ) {α β a A : ℝ≥0∞} (hα : α ≠ ⊤)
    (hβ : β ≠ ⊤) (ha0 : a ≠ 0) (haT : a ≠ ⊤) (hA0 : A ≠ 0) (hAT : A ≠ ⊤) :
    ∃ m : ℤ, α * (ENNReal.ofReal (((2 : ℝ) ^ m) ^ σ) * a) +
        β * (ENNReal.ofReal (((2 : ℝ) ^ m) ^ (-τ)) * A) ≤
      (α + β * ENNReal.ofReal ((2 : ℝ) ^ τ)) * (a ^ (1 - σ / (σ + τ)) * A ^ (σ / (σ + τ))) := by
  obtain ⟨α', hα', rfl⟩ : ∃ α', 0 ≤ α' ∧ α = ENNReal.ofReal α' :=
    ⟨α.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hα).symm⟩
  obtain ⟨β', hβ', rfl⟩ : ∃ β', 0 ≤ β' ∧ β = ENNReal.ofReal β' :=
    ⟨β.toReal, ENNReal.toReal_nonneg, (ENNReal.ofReal_toReal hβ).symm⟩
  obtain ⟨a', ha', rfl⟩ : ∃ a', 0 < a' ∧ a = ENNReal.ofReal a' :=
    ⟨a.toReal, ENNReal.toReal_pos ha0 haT, (ENNReal.ofReal_toReal haT).symm⟩
  obtain ⟨A', hA', rfl⟩ : ∃ A', 0 < A' ∧ A = ENNReal.ofReal A' :=
    ⟨A.toReal, ENNReal.toReal_pos hA0 hAT, (ENNReal.ofReal_toReal hAT).symm⟩
  obtain ⟨m, hm⟩ := cmxHLS_opt hσ hτ hα' hβ' ha' hA'
  refine ⟨m, ?_⟩
  have hu1 : 0 ≤ ((2 : ℝ) ^ m) ^ σ := by positivity
  have hu2 : 0 ≤ ((2 : ℝ) ^ m) ^ (-τ) := by positivity
  have eL : ENNReal.ofReal (α' * (((2 : ℝ) ^ m) ^ σ * a') + β' * (((2 : ℝ) ^ m) ^ (-τ) * A')) =
      ENNReal.ofReal α' * (ENNReal.ofReal (((2 : ℝ) ^ m) ^ σ) * ENNReal.ofReal a') +
        ENNReal.ofReal β' * (ENNReal.ofReal (((2 : ℝ) ^ m) ^ (-τ)) * ENNReal.ofReal A') := by
    rw [ENNReal.ofReal_add (by positivity) (by positivity), ENNReal.ofReal_mul hα',
      ENNReal.ofReal_mul hu1, ENNReal.ofReal_mul hβ', ENNReal.ofReal_mul hu2]
  have eR : ENNReal.ofReal ((α' + β' * (2 : ℝ) ^ τ) *
        (a' ^ (1 - σ / (σ + τ)) * A' ^ (σ / (σ + τ)))) =
      (ENNReal.ofReal α' + ENNReal.ofReal β' * ENNReal.ofReal ((2 : ℝ) ^ τ)) *
        (ENNReal.ofReal a' ^ (1 - σ / (σ + τ)) * ENNReal.ofReal A' ^ (σ / (σ + τ))) := by
    rw [ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_add hα' (by positivity),
      ENNReal.ofReal_mul hβ', ENNReal.ofReal_mul (by positivity),
      ENNReal.ofReal_rpow_of_pos ha', ENNReal.ofReal_rpow_of_pos hA']
  rw [← eL, ← eR]
  exact ENNReal.ofReal_le_ofReal hm


/-- If the maximal function vanishes at a point, then `F = 0` a.e. -/
lemma cmxHLS_Md_eq_zero {F : 𝔼 → ℝ≥0∞} (hF : Measurable F) {p : ℝ} (hp : 0 < p) (x : 𝔼)
    (h0 : cmxHLS_Md F x = 0) : ∫⁻ y, F y ^ p = 0 := by
  have hz : ∀ j : ℤ, ∫⁻ y in closedBall x ((2 : ℝ) ^ j), F y = 0 := fun j => by
    have := cmxHLS_lintegral_le F x j
    rw [h0, mul_zero] at this
    exact le_antisymm this bot_le
  have hball : ∀ n : ℕ, ∫⁻ y in closedBall x ((2 : ℝ) ^ (n : ℤ)), F y ^ p = 0 := by
    intro n
    have h1 := (lintegral_eq_zero_iff' (μ := volume.restrict (closedBall x ((2 : ℝ) ^ (n : ℤ))))
      hF.aemeasurable).1 (hz n)
    have h2 : (fun y => F y ^ p) =ᵐ[volume.restrict (closedBall x ((2 : ℝ) ^ (n : ℤ)))] 0 := by
      filter_upwards [h1] with y hy
      simp [hy, ENNReal.zero_rpow_of_pos hp]
    rw [lintegral_congr_ae h2]; simp
  have hU : (⋃ n : ℕ, closedBall x ((2 : ℝ) ^ (n : ℤ))) = univ := by
    refine eq_univ_of_forall fun y => ?_
    obtain ⟨n, hn⟩ := exists_nat_gt (dist y x)
    refine mem_iUnion.2 ⟨n, ?_⟩
    rw [mem_closedBall, zpow_natCast]
    have h5 : n ≤ 2 ^ n := (Nat.lt_two_pow_self (n := n)).le
    have : (n : ℝ) ≤ 2 ^ n := by exact_mod_cast h5
    linarith
  have := lintegral_iUnion_le (μ := volume) (fun n : ℕ => closedBall x ((2 : ℝ) ^ (n : ℤ)))
    (fun y => F y ^ p)
  rw [hU, Measure.restrict_univ] at this
  have h5 : ∑' n : ℕ, ∫⁻ y in closedBall x ((2 : ℝ) ^ (n : ℤ)), F y ^ p = 0 := by
    simp only [hball]; exact tsum_zero
  exact le_antisymm (this.trans h5.le) bot_le


/-- **Hedberg's inequality** `I_σ F(x) ≲ (M F(x))^{1-σp/d} ‖F‖_p^{σp/d}` (`σ p < d`, `p > 1`). -/
theorem cmxHLS_hedberg {σ p : ℝ} (hσ : 0 < σ) (hp : 1 < p) (hσp : σ * p < d) :
    ∃ C : ℝ≥0∞, C ≠ ⊤ ∧ C ≠ 0 ∧ ∀ F : 𝔼 → ℝ≥0∞, Measurable F →
      ∫⁻ y, F y ^ p ≠ 0 → ∫⁻ y, F y ^ p ≠ ⊤ → ∀ x : 𝔼,
      cmxHLS_I σ F x ≤ C * (cmxHLS_Md F x ^ (1 - σ * p / d) *
        ((∫⁻ y, F y ^ p) ^ (1 / p)) ^ (σ * p / d)) := by
  have hp0 : 0 < p := by linarith
  set q : ℝ := p.conjExponent with hq
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hdpos : (0 : ℝ) < d := by nlinarith
  have hσd : σ < d := by nlinarith
  set τ : ℝ := (d : ℝ) / p - σ with hτdef
  have hτ : 0 < τ := by
    rw [hτdef, sub_pos, lt_div_iff₀ hp0]; exact hσp
  have hτ' : σ - (d : ℝ) / p = -τ := by rw [hτdef]; ring
  have hθ : σ / (σ + τ) = σ * p / d := by
    rw [hτdef, show σ + ((d : ℝ) / p - σ) = d / p by ring, div_div_eq_mul_div]
  have hθ1 : σ * p / d < 1 := by rw [div_lt_one hdpos]; exact hσp
  have hθ0 : 0 < σ * p / d := by positivity
  set ω : ℝ≥0∞ := volume (closedBall (0 : 𝔼) 1) with hω
  have hωt : ω ≠ ⊤ := cmxHLS_vol_closedBall_ne_top 0 1
  have hρ1 : ENNReal.ofReal (((2 : ℝ) ^ σ)⁻¹) < 1 := by
    rw [← ENNReal.ofReal_one]
    refine (ENNReal.ofReal_lt_ofReal_iff one_pos).2 ?_
    exact inv_lt_one_of_one_lt₀ (Real.one_lt_rpow (by norm_num) hσ)
  have hρ2 : ENNReal.ofReal ((2 : ℝ) ^ (-τ)) < 1 := by
    rw [← ENNReal.ofReal_one]
    refine (ENNReal.ofReal_lt_ofReal_iff one_pos).2 ?_
    exact Real.rpow_lt_one_of_one_lt_of_neg (by norm_num) (by linarith)
  set α : ℝ≥0∞ := ENNReal.ofReal (2 ^ d) * ω * (1 - ENNReal.ofReal (((2 : ℝ) ^ σ)⁻¹))⁻¹ with hα
  set β : ℝ≥0∞ := ENNReal.ofReal (2 ^ ((d : ℝ) / q)) * ω ^ (1 / q) *
    (1 - ENNReal.ofReal ((2 : ℝ) ^ (-τ)))⁻¹ with hβ
  have hαt : α ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top hωt) ?_
    exact ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hρ1).ne'
  have hq0 : 0 ≤ 1 / q := by have := hpq.symm.pos; positivity
  have hβt : β ≠ ⊤ := by
    refine ENNReal.mul_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top
      (ENNReal.rpow_ne_top_of_nonneg hq0 hωt)) ?_
    exact ENNReal.inv_ne_top.2 (tsub_pos_iff_lt.2 hρ2).ne'
  refine ⟨α + β * ENNReal.ofReal ((2 : ℝ) ^ τ) + 1, ?_,
    (lt_of_lt_of_le zero_lt_one le_add_self).ne', ?_⟩
  · refine ENNReal.add_ne_top.2 ⟨ENNReal.add_ne_top.2 ⟨hαt, ENNReal.mul_ne_top hβt
      ENNReal.ofReal_ne_top⟩, ENNReal.one_ne_top⟩
  intro F hF hA0 hAT x
  set a : ℝ≥0∞ := cmxHLS_Md F x with ha
  set A : ℝ≥0∞ := (∫⁻ y, F y ^ p) ^ (1 / p) with hA
  have hApos : A ≠ 0 := (ENNReal.rpow_pos (pos_iff_ne_zero.2 hA0) hAT).ne'
  have hAtop : A ≠ ⊤ := ENNReal.rpow_ne_top_of_nonneg (by positivity) hAT
  have hmain : ∀ m : ℤ, cmxHLS_I σ F x ≤ α * (ENNReal.ofReal (((2 : ℝ) ^ m) ^ σ) * a) +
      β * (ENNReal.ofReal (((2 : ℝ) ^ m) ^ (-τ)) * A) := by
    intro m
    refine (cmxHLS_cover hσd F x m).trans (add_le_add (cmxHLS_near_sum hσ hσd F x m) ?_)
    have := cmxHLS_far_sum hσd hpq (by linarith : σ - (d : ℝ) / p < 0) hF x m
    rwa [hτ'] at this
  by_cases haT : a = ⊤
  · rw [haT, ENNReal.top_rpow_of_pos (by linarith), ENNReal.top_mul
      (ENNReal.rpow_pos (pos_iff_ne_zero.2 hApos) hAtop).ne', ENNReal.mul_top (by simp)]
    exact le_top
  by_cases ha0 : a = 0
  · exact absurd (cmxHLS_Md_eq_zero hF hp0 x ha0) hA0
  obtain ⟨m, hm⟩ := cmxHLS_opt_enn hσ hτ hαt hβt ha0 haT hApos hAtop
  rw [hθ] at hm
  calc cmxHLS_I σ F x ≤ _ := hmain m
    _ ≤ _ := hm
    _ ≤ _ := mul_le_mul_left le_self_add _

end HRS.Commutator.Whole
