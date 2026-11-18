import HRS.MC.CepaDefs

/-!
# Packet CEPE5C, auxiliary 1: the abstract ladder estimate

Abstract (measure-theoretic) core of `cep_E5c_cauchy`: pair distances `d m n` with `d² ≤ Ec (1/m+1/n)(h m + h n)`
for `m ≤ n ≤ 8m` and `E h n ≤ C n / n^{1/3}`; chaining along `m, 8m, 64m, …, n` with Cauchy–Schwarz weights `(3/4)^j`.
-/

open MeasureTheory Set Filter

noncomputable section

namespace HRS.MC.CepE5c

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {τ : Type*}

/-- Cube root of a natural number. -/
def e5c_r (u : ℕ) : ℝ := (u : ℝ) ^ (1 / 3 : ℝ)

theorem e5c_r_cube (u : ℕ) : e5c_r u ^ 3 = u := by
  unfold e5c_r
  rw [← Real.rpow_natCast, ← Real.rpow_mul (Nat.cast_nonneg _)]
  norm_num

theorem e5c_r_nonneg (u : ℕ) : 0 ≤ e5c_r u := Real.rpow_nonneg (Nat.cast_nonneg _) _

theorem e5c_r_pos {u : ℕ} (hu : 0 < u) : 0 < e5c_r u :=
  Real.rpow_pos_of_pos (by exact_mod_cast hu) _

theorem e5c_r_le_two {u v : ℕ} (hv : v ≤ 8 * u) : e5c_r v ≤ 2 * e5c_r u := by
  have h1 : e5c_r v ^ 3 ≤ (2 * e5c_r u) ^ 3 := by
    rw [mul_pow, e5c_r_cube, e5c_r_cube]
    have : (v : ℝ) ≤ 8 * u := by exact_mod_cast hv
    linarith
  exact (pow_le_pow_iff_left₀ (e5c_r_nonneg v) (by have := e5c_r_nonneg u; positivity) (by norm_num)).1 h1

theorem e5c_r_pow (j m : ℕ) : e5c_r (8 ^ j * m) = 2 ^ j * e5c_r m := by
  have h1 : e5c_r (8 ^ j * m) ^ 3 = (2 ^ j * e5c_r m) ^ 3 := by
    rw [e5c_r_cube, mul_pow, ← pow_mul, e5c_r_cube]
    push_cast
    rw [show (2 : ℝ) ^ (j * 3) = 8 ^ j by rw [pow_mul']; norm_num]
  exact (pow_left_inj₀ (e5c_r_nonneg _) (by have := e5c_r_nonneg m; positivity) (by norm_num)).1 h1

theorem e5c_geom_le {x : ℝ} (hx0 : 0 ≤ x) (hx1 : x < 1) (K : ℕ) :
    ∑ j ∈ Finset.range K, x ^ j ≤ 1 / (1 - x) := by
  rw [geom_sum_eq hx1.ne K]
  have h1 : 0 < 1 - x := by linarith
  have e : (x ^ K - 1) / (x - 1) = (1 - x ^ K) / (1 - x) := by
    rw [← neg_sub, ← neg_sub 1 x, neg_div_neg_eq]
  rw [e]
  exact div_le_div_of_nonneg_right (by linarith [pow_nonneg hx0 K]) h1.le

/-- Expectation of the pair bound. -/
theorem e5c_pair_mean [IsProbabilityMeasure P] {h : ℕ → Ω → ℝ} {Ec C : ℝ} (hEc : 0 ≤ Ec) (hC : 0 ≤ C)
    (hint : ∀ n, 8 ≤ n → Integrable (h n) P) (hh0 : ∀ n ω, 0 ≤ h n ω)
    (hEh : ∀ n : ℕ, 8 ≤ n → ∫ ω, h n ω ∂P ≤ C * ((n : ℝ) / e5c_r n))
    {u v : ℕ} (hu : 8 ≤ u) (huv : u ≤ v) (hv : v ≤ 8 * u) :
    ∫ ω, Ec * ((1 / (u : ℝ) + 1 / (v : ℝ)) * (h u ω + h v ω)) ∂P ≤ 10 * Ec * C / e5c_r u := by
  have hv8 : 8 ≤ v := le_trans hu huv
  have hu0 : (0 : ℝ) < u := by exact_mod_cast (by omega : 0 < u)
  have hv0 : (0 : ℝ) < v := by exact_mod_cast (by omega : 0 < v)
  have hr := e5c_r_pos (by omega : 0 < u)
  have hrv := e5c_r_pos (by omega : 0 < v)
  have h3 := e5c_r_cube u
  have h3v := e5c_r_cube v
  have hr2 := e5c_r_le_two hv
  rw [integral_const_mul, integral_const_mul, integral_add (hint u hu) (hint v hv8)]
  have a1 := hEh u hu
  have a2 := hEh v hv8
  have e1 : (u : ℝ) / e5c_r u = e5c_r u ^ 2 := by
    rw [← h3]; field_simp
  have e2 : (v : ℝ) / e5c_r v = e5c_r v ^ 2 := by
    rw [← h3v]; field_simp
  rw [e1] at a1
  rw [e2] at a2
  have a3 : e5c_r v ^ 2 ≤ 4 * e5c_r u ^ 2 := by nlinarith
  have hsum : (∫ ω, h u ω ∂P) + ∫ ω, h v ω ∂P ≤ 5 * C * e5c_r u ^ 2 := by nlinarith
  have hsum0 : 0 ≤ (∫ ω, h u ω ∂P) + ∫ ω, h v ω ∂P :=
    add_nonneg (integral_nonneg (hh0 u)) (integral_nonneg (hh0 v))
  have hvu : (1 : ℝ) / v ≤ 1 / u := one_div_le_one_div_of_le hu0 (by exact_mod_cast huv)
  have h4 : (1 / (u : ℝ) + 1 / (v : ℝ)) * ((∫ ω, h u ω ∂P) + ∫ ω, h v ω ∂P) ≤
      (2 / u) * (5 * C * e5c_r u ^ 2) := by
    refine mul_le_mul (by rw [show (2 : ℝ) / u = 1 / u + 1 / u by ring]; linarith) hsum hsum0 (by positivity)
  have h5 : (2 / (u : ℝ)) * (5 * C * e5c_r u ^ 2) = 10 * C / e5c_r u := by
    rw [← h3]; field_simp; ring
  calc Ec * ((1 / (u : ℝ) + 1 / (v : ℝ)) * ((∫ ω, h u ω ∂P) + ∫ ω, h v ω ∂P)) ≤
        Ec * (10 * C / e5c_r u) := by
        refine mul_le_mul_of_nonneg_left ?_ hEc
        rw [← h5]; exact h4
    _ = 10 * Ec * C / e5c_r u := by ring

theorem e5c_ladder [IsProbabilityMeasure P]
    {d : ℕ → ℕ → Ω → τ → ℝ} {h : ℕ → Ω → ℝ} {Ec C : ℝ} (hEc : 0 ≤ Ec) (hC : 0 ≤ C)
    (hint : ∀ n, 8 ≤ n → Integrable (h n) P) (hh0 : ∀ n ω, 0 ≤ h n ω)
    (hEh : ∀ n : ℕ, 8 ≤ n → ∫ ω, h n ω ∂P ≤ C * ((n : ℝ) / e5c_r n))
    (hnn : ∀ m n ω t, 0 ≤ d m n ω t) (hself : ∀ m ω t, d m m ω t = 0)
    (htri : ∀ m k n ω t, d m n ω t ≤ d m k ω t + d k n ω t)
    (hpair : ∀ᵐ ω ∂P, ∀ m n t, 8 ≤ m → m ≤ n → n ≤ 8 * m →
      d m n ω t ^ 2 ≤ Ec * ((1 / (m : ℝ) + 1 / (n : ℝ)) * (h m ω + h n ω)))
    (m n : ℕ) (hm : 8 ≤ m) (hmn : m ≤ n) :
    ∃ V : Ω → ℝ, Integrable V P ∧ (∀ ω, 0 ≤ V ω) ∧ (∀ᵐ ω ∂P, ∀ t, d m n ω t ^ 2 ≤ V ω) ∧
      ∫ ω, V ω ∂P ≤ 120 * Ec * C / e5c_r m := by
  classical
  have hm0 : 0 < m := by omega
  set J : ℕ := Nat.log 8 (n / m) with hJ
  set x : ℕ → ℕ := fun j => if j ≤ J then 8 ^ j * m else n with hx
  have hx0 : x 0 = m := by simp [hx]
  have hxJ1 : x (J + 1) = n := by simp [hx]
  have hxle : ∀ j, j ≤ J → x j = 8 ^ j * m := fun j hj => by simp [hx, hj]
  have hJle : 8 ^ J * m ≤ n := by
    have hq : n / m ≠ 0 := by
      have : 1 ≤ n / m := (Nat.le_div_iff_mul_le hm0).2 (by omega)
      omega
    have : 8 ^ J ≤ n / m := Nat.pow_log_le_self 8 hq
    calc 8 ^ J * m ≤ (n / m) * m := Nat.mul_le_mul_right _ this
      _ ≤ n := Nat.div_mul_le_self n m
  have hJlt : n < 8 ^ (J + 1) * m := by
    have : n / m < 8 ^ (J + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    exact (Nat.div_lt_iff_lt_mul hm0).1 this
  have hxge : ∀ j, j ≤ J → 8 ≤ x j := fun j hj => by
    rw [hxle j hj]
    have : 1 ≤ 8 ^ j := Nat.one_le_pow _ _ (by norm_num)
    nlinarith
  have hxstep : ∀ j, j ≤ J → x j ≤ x (j + 1) ∧ x (j + 1) ≤ 8 * x j := fun j hj => by
    rcases Nat.lt_or_ge j J with hlt | hge
    · rw [hxle j hj, hxle (j + 1) hlt, pow_succ]
      constructor <;> nlinarith [Nat.one_le_pow j 8 (by norm_num : 0 < 8)]
    · have hjJ : j = J := le_antisymm hj hge
      rw [hjJ, hxle J le_rfl, hxJ1]
      exact ⟨hJle, by rw [pow_succ] at hJlt; nlinarith⟩
  have hxge' : ∀ j, j ≤ J + 1 → 8 ≤ x j := fun j hj => by
    rcases Nat.lt_or_ge j (J + 1) with hlt | hge
    · exact hxge j (by omega)
    · have : j = J + 1 := le_antisymm hj hge
      subst this; rw [hxJ1]; omega
  set lam : ℕ → ℝ := fun j => (3 / 4 : ℝ) ^ j with hlam
  have hlam0 : ∀ j, 0 < lam j := fun j => by simp only [hlam]; positivity
  set Lam : ℝ := ∑ j ∈ Finset.range (J + 1), lam j with hLam
  have hLam0 : 0 < Lam := Finset.sum_pos (fun j _ => hlam0 j) ⟨0, by simp⟩
  have hLam4 : Lam ≤ 4 := by
    have := e5c_geom_le (x := (3 / 4 : ℝ)) (by norm_num) (by norm_num) (J + 1)
    norm_num at this
    simpa [hLam, hlam] using this
  set Y : ℕ → Ω → ℝ := fun j ω => Ec * ((1 / (x j : ℝ) + 1 / (x (j + 1) : ℝ)) * (h (x j) ω + h (x (j + 1)) ω))
    with hY
  have hY0 : ∀ j ω, 0 ≤ Y j ω := fun j ω => by
    simp only [hY]
    have := hh0 (x j) ω
    have := hh0 (x (j + 1)) ω
    positivity
  have hYint : ∀ j, j ≤ J → Integrable (Y j) P := fun j hj => by
    simp only [hY]
    exact (((hint _ (hxge j hj)).add (hint _ (hxge' (j + 1) (by omega)))).const_mul _).const_mul _
  refine ⟨fun ω => Lam * ∑ j ∈ Finset.range (J + 1), Y j ω / lam j, ?_, ?_, ?_, ?_⟩
  · refine (integrable_finsetSum _ fun j hj => ?_).const_mul _
    exact (hYint j (by simpa [Nat.lt_succ_iff] using hj)).div_const _
  · intro ω
    exact mul_nonneg hLam0.le (Finset.sum_nonneg fun j _ => div_nonneg (hY0 j ω) (hlam0 j).le)
  · filter_upwards [hpair] with ω hω t
    have hd : ∀ j ∈ Finset.range (J + 1), d (x j) (x (j + 1)) ω t ^ 2 ≤ Y j ω := fun j hj => by
      have hjJ : j ≤ J := by simpa [Nat.lt_succ_iff] using hj
      exact hω _ _ t (hxge j hjJ) (hxstep j hjJ).1 (hxstep j hjJ).2
    have hchain : ∀ K, d (x 0) (x K) ω t ≤ ∑ j ∈ Finset.range K, d (x j) (x (j + 1)) ω t := by
      intro K
      induction K with
      | zero => simp [hself]
      | succ K ih =>
        rw [Finset.sum_range_succ]
        linarith [htri (x 0) (x K) (x (K + 1)) ω t]
    have h1 := hchain (J + 1)
    rw [hx0, hxJ1] at h1
    have h2 : d m n ω t ^ 2 ≤ (∑ j ∈ Finset.range (J + 1), d (x j) (x (j + 1)) ω t) ^ 2 :=
      pow_le_pow_left₀ (hnn _ _ _ _) h1 2
    have h3 := Finset.sq_sum_div_le_sum_sq_div (Finset.range (J + 1))
      (fun j => d (x j) (x (j + 1)) ω t) (g := lam) (fun j _ => hlam0 j)
    have h4 : ∑ j ∈ Finset.range (J + 1), d (x j) (x (j + 1)) ω t ^ 2 / lam j ≤
        ∑ j ∈ Finset.range (J + 1), Y j ω / lam j :=
      Finset.sum_le_sum fun j hj => div_le_div_of_nonneg_right (hd j hj) (hlam0 j).le
    have h5 : (∑ j ∈ Finset.range (J + 1), d (x j) (x (j + 1)) ω t) ^ 2 ≤
        Lam * ∑ j ∈ Finset.range (J + 1), Y j ω / lam j := by
      have := (div_le_iff₀ hLam0).1 (h3.trans h4)
      linarith
    exact h2.trans h5
  · -- expectation
    have hmean : ∀ j ∈ Finset.range (J + 1), ∫ ω, Y j ω / lam j ∂P ≤
        (10 * Ec * C / e5c_r m) * (2 / 3) ^ j := fun j hj => by
      have hjJ : j ≤ J := by simpa [Nat.lt_succ_iff] using hj
      have hp := e5c_pair_mean hEc hC hint hh0 hEh (hxge j hjJ) (hxstep j hjJ).1 (hxstep j hjJ).2
      rw [integral_div]
      rw [hxle j hjJ, e5c_r_pow] at hp
      have hrm := e5c_r_pos hm0
      have : ∫ ω, Y j ω ∂P ≤ 10 * Ec * C / (2 ^ j * e5c_r m) := by
        simpa [hY, hxle j hjJ] using hp
      calc (∫ ω, Y j ω ∂P) / lam j ≤ (10 * Ec * C / (2 ^ j * e5c_r m)) / lam j :=
            div_le_div_of_nonneg_right this (hlam0 j).le
        _ = (10 * Ec * C / e5c_r m) * (2 / 3) ^ j := by
            simp only [hlam]
            have e : ((2 : ℝ) ^ j * e5c_r m * (3 / 4) ^ j) = e5c_r m * (3 / 2) ^ j := by
              rw [show (3 / 2 : ℝ) ^ j = 2 ^ j * (3 / 4) ^ j by rw [← mul_pow]; norm_num]; ring
            rw [div_div, e, show (2 / 3 : ℝ) ^ j = 1 / (3 / 2) ^ j by
              rw [one_div, ← inv_pow]; norm_num]
            have := hrm.ne'
            field_simp
    rw [integral_const_mul, integral_finsetSum _ (fun j hj =>
      (hYint j (by simpa [Nat.lt_succ_iff] using hj)).div_const _)]
    have hK0 : 0 ≤ 10 * Ec * C / e5c_r m := by
      have := e5c_r_nonneg m
      positivity
    have hsum := Finset.sum_le_sum hmean
    have hg := e5c_geom_le (x := (2 / 3 : ℝ)) (by norm_num) (by norm_num) (J + 1)
    rw [← Finset.mul_sum] at hsum
    have hg3 : ∑ j ∈ Finset.range (J + 1), (2 / 3 : ℝ) ^ j ≤ 3 := by
      norm_num at hg; exact hg
    have h6 : ∑ j ∈ Finset.range (J + 1), ∫ ω, Y j ω / lam j ∂P ≤ (10 * Ec * C / e5c_r m) * 3 :=
      hsum.trans (mul_le_mul_of_nonneg_left hg3 hK0)
    have hsum0 : 0 ≤ ∑ j ∈ Finset.range (J + 1), ∫ ω, Y j ω / lam j ∂P :=
      Finset.sum_nonneg fun j _ => integral_nonneg fun ω => div_nonneg (hY0 j ω) (hlam0 j).le
    calc Lam * ∑ j ∈ Finset.range (J + 1), ∫ ω, Y j ω / lam j ∂P ≤ 4 * ((10 * Ec * C / e5c_r m) * 3) :=
          mul_le_mul hLam4 h6 hsum0 (by norm_num)
      _ = 120 * Ec * C / e5c_r m := by ring

end HRS.MC.CepE5c
