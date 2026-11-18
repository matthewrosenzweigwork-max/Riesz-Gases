import HRS.Whole.Q09AAux5
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

/-!
# Packet Q09-A, part 6: a smooth partition of unity on `ℝ^d` by translates of one bump

`th1 = S - S(· - 1)` (`S` the smooth step), `Th d N k` (tensor products, translates of `Th0`), and the
plateau cutoff `plat d N = ∑_k Th d N k` over the box `k_i ∈ [0, 2N]`, with its Lipschitz bound,
support, plateau value `1` on a ball, and the bounded overlap (`≤ 2^d`) of the supports.
-/

noncomputable section

namespace HRS.Whole.Q09A

variable {d : ℕ}

/-- the smooth step `0` on `(-∞,0]`, `1` on `[1,∞)` -/
local notation "S1" => Real.smoothTransition

/-- `th1 t = S1 t - S1 (t-1)`: smooth bump supported in `(0,2)` with `∑_n th1 (t - n) = 1` -/
def th1 (t : ℝ) : ℝ := S1 t - S1 (t - 1)

theorem th1_nonneg (t : ℝ) : 0 ≤ th1 t := by
  unfold th1
  have := Real.smoothTransition.monotone (show t - 1 ≤ t by linarith)
  linarith

theorem th1_le_one (t : ℝ) : th1 t ≤ 1 := by
  unfold th1
  have := Real.smoothTransition.le_one t
  have := Real.smoothTransition.nonneg (t - 1)
  linarith

theorem th1_zero_of_le {t : ℝ} (h : t ≤ 0) : th1 t = 0 := by
  unfold th1
  rw [Real.smoothTransition.zero_of_nonpos h, Real.smoothTransition.zero_of_nonpos (by linarith)]
  simp

theorem th1_zero_of_ge {t : ℝ} (h : 2 ≤ t) : th1 t = 0 := by
  unfold th1
  rw [Real.smoothTransition.one_of_one_le (by linarith), Real.smoothTransition.one_of_one_le (by linarith)]
  simp

theorem th1_contDiff : ContDiff ℝ ∞ th1 :=
  Real.smoothTransition.contDiff.sub (Real.smoothTransition.contDiff.comp (contDiff_id.sub contDiff_const))

theorem th1_tele (t : ℝ) (N : ℕ) :
    ∑ k ∈ Finset.range (2 * N + 1), th1 (t + N - k) = S1 (t + N) - S1 (t - N - 1) := by
  have h := Finset.sum_range_sub' (fun k : ℕ => S1 (t + N - k)) (2 * N + 1)
  simp only [Nat.cast_zero, sub_zero] at h
  have h2 : ∀ k : ℕ, th1 (t + N - k) = S1 (t + N - k) - S1 (t + N - ((k + 1 : ℕ) : ℝ)) := by
    intro k
    unfold th1
    congr 2
    push_cast
    ring
  simp_rw [h2]
  rw [h]
  congr 2
  push_cast
  ring


/-- the plateau cutoff `∏_i (S(d x_i + N) - S(d x_i - N - 1))` -/
def plat (d N : ℕ) (x : Euc d) : ℝ :=
  ∏ i, (S1 ((d : ℝ) * x i + N) - S1 ((d : ℝ) * x i - N - 1))

/-- the partition pieces `∏_i th1 (d x_i + N - k_i)` -/
def Th (d N : ℕ) (k : Fin d → ℕ) (x : Euc d) : ℝ := ∏ i, th1 ((d : ℝ) * x i + N - k i)

theorem plat_eq_sum (d N : ℕ) (x : Euc d) :
    plat d N x = ∑ k ∈ Fintype.piFinset (fun _ : Fin d => Finset.range (2 * N + 1)), Th d N k x := by
  unfold plat Th
  rw [← Finset.prod_univ_sum (fun _ : Fin d => Finset.range (2 * N + 1))
    (fun i j => th1 ((d : ℝ) * x i + N - j))]
  refine Finset.prod_congr rfl fun i _ => ?_
  exact (th1_tele ((d : ℝ) * x i) N).symm ▸ rfl


theorem plat_factor_mem (a b : ℝ) (h : b ≤ a) : 0 ≤ S1 a - S1 b ∧ S1 a - S1 b ≤ 1 := by
  have h1 := Real.smoothTransition.monotone h
  have h2 := Real.smoothTransition.le_one a
  have h3 := Real.smoothTransition.nonneg b
  constructor <;> linarith

theorem plat_fac_mem (d N : ℕ) (x : Euc d) (i : Fin d) :
    0 ≤ S1 ((d : ℝ) * x i + N) - S1 ((d : ℝ) * x i - N - 1) ∧
      S1 ((d : ℝ) * x i + N) - S1 ((d : ℝ) * x i - N - 1) ≤ 1 :=
  plat_factor_mem _ _ (by linarith [Nat.cast_nonneg (α := ℝ) N])

theorem plat_nonneg (d N : ℕ) (x : Euc d) : 0 ≤ plat d N x :=
  Finset.prod_nonneg fun i _ => (plat_fac_mem d N x i).1

theorem plat_le_one (d N : ℕ) (x : Euc d) : plat d N x ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => (plat_fac_mem d N x i).1) fun i _ => (plat_fac_mem d N x i).2

theorem plat_eq_one {d N : ℕ} {R : ℝ} (hN : (d : ℝ) * R + 1 ≤ N) {x : Euc d} (hx : ‖x‖ ≤ R) :
    plat d N x = 1 := by
  unfold plat
  refine Finset.prod_eq_one fun i _ => ?_
  have h1 : |x i| ≤ R := le_trans (by simpa using PiLp.norm_apply_le x i) hx
  have hd : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have h2 : (d : ℝ) * |x i| ≤ d * R := mul_le_mul_of_nonneg_left h1 hd
  have h3 : -(d * R) ≤ (d : ℝ) * x i := by
    have := neg_abs_le (x i)
    nlinarith
  have h4 : (d : ℝ) * x i ≤ d * R := by
    have := le_abs_self (x i)
    nlinarith
  rw [Real.smoothTransition.one_of_one_le (by linarith),
    Real.smoothTransition.zero_of_nonpos (by linarith)]
  simp

theorem plat_contDiff (d N : ℕ) : ContDiff ℝ ∞ (plat d N) := by
  unfold plat
  refine contDiff_prod fun i _ => ?_
  have hc : ContDiff ℝ ∞ fun x : Euc d => x i :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  exact (Real.smoothTransition.contDiff.comp ((contDiff_const.mul hc).add contDiff_const)).sub
    (Real.smoothTransition.contDiff.comp (((contDiff_const.mul hc).sub contDiff_const).sub contDiff_const))

theorem plat_support {d N : ℕ} (hd : 1 ≤ d) {x : Euc d} (hx : plat d N x ≠ 0) : ‖x‖ ≤ N + 2 := by
  have hfac : ∀ i, S1 ((d : ℝ) * x i + N) - S1 ((d : ℝ) * x i - N - 1) ≠ 0 := by
    intro i h0
    exact hx (Finset.prod_eq_zero (Finset.mem_univ i) h0)
  have hdpos : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hbd : ∀ i, |x i| ≤ (N + 2 : ℝ) / d := by
    intro i
    have hf := hfac i
    have hlow : -(N : ℝ) < d * x i := by
      by_contra h
      push Not at h
      apply hf
      rw [Real.smoothTransition.zero_of_nonpos (by linarith),
        Real.smoothTransition.zero_of_nonpos (by linarith)]
      simp
    have hup : (d : ℝ) * x i < N + 2 := by
      by_contra h
      push Not at h
      apply hf
      rw [Real.smoothTransition.one_of_one_le (by linarith),
        Real.smoothTransition.one_of_one_le (by linarith)]
      simp
    have hd0 : (0 : ℝ) < d := by linarith
    rw [abs_le]
    constructor
    · rw [← neg_div, div_le_iff₀ hd0]
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
    · rw [le_div_iff₀ hd0]
      nlinarith [Nat.cast_nonneg (α := ℝ) N]
  have h2 : ‖x‖ ^ 2 ≤ (N + 2 : ℝ) ^ 2 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖x i‖ ^ 2 ≤ ∑ _i : Fin d, ((N + 2 : ℝ) / d) ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hbd i) 2
      _ = (N + 2 : ℝ) ^ 2 / d := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      _ ≤ (N + 2 : ℝ) ^ 2 := by
          rw [div_le_iff₀ (by linarith)]
          nlinarith [sq_nonneg ((N : ℝ) + 2)]
  exact (sq_le_sq₀ (norm_nonneg _) (by positivity)).mp h2


theorem S1_lipschitz : ∃ C : ℝ≥0, LipschitzWith C S1 := by
  have hd : ContDiff ℝ 1 S1 := Real.smoothTransition.contDiff
  have hc : Continuous (deriv S1) := hd.continuous_deriv le_rfl
  obtain ⟨B, hB⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := 1)).exists_bound_of_continuousOn hc.continuousOn
  have hz : ∀ x : ℝ, x ∉ Set.Icc (0 : ℝ) 1 → deriv S1 x = 0 := by
    intro x hx
    rcases not_and_or.mp hx with h | h
    · have hx0 : x < 0 := not_le.mp h
      have : S1 =ᶠ[nhds x] fun _ => (0 : ℝ) := by
        filter_upwards [Iio_mem_nhds hx0] with y hy
        exact Real.smoothTransition.zero_of_nonpos (le_of_lt hy)
      rw [this.deriv_eq]; simp
    · have hx1 : 1 < x := not_le.mp h
      have : S1 =ᶠ[nhds x] fun _ => (1 : ℝ) := by
        filter_upwards [Ioi_mem_nhds hx1] with y hy
        exact Real.smoothTransition.one_of_one_le (le_of_lt hy)
      rw [this.deriv_eq]; simp
  refine ⟨Real.toNNReal B, lipschitzWith_of_nnnorm_deriv_le (hd.differentiable one_ne_zero) fun x => ?_⟩
  by_cases hx : x ∈ Set.Icc (0 : ℝ) 1
  · rw [← NNReal.coe_le_coe, coe_nnnorm]
    exact (hB x hx).trans (Real.le_coe_toNNReal B)
  · rw [hz x hx]; simp

theorem prod_sub_prod_le {ι : Type*} (s : Finset ι) (a b : ι → ℝ) (ha : ∀ i, 0 ≤ a i ∧ a i ≤ 1)
    (hb : ∀ i, 0 ≤ b i ∧ b i ≤ 1) :
    |∏ i ∈ s, a i - ∏ i ∈ s, b i| ≤ ∑ i ∈ s, |a i - b i| := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert j s hj ih =>
    rw [Finset.prod_insert hj, Finset.prod_insert hj, Finset.sum_insert hj]
    have hA0 : 0 ≤ ∏ i ∈ s, a i := Finset.prod_nonneg fun i _ => (ha i).1
    have hA1 : ∏ i ∈ s, a i ≤ 1 := Finset.prod_le_one₀ (fun i _ => (ha i).1) fun i _ => (ha i).2
    calc |a j * ∏ i ∈ s, a i - b j * ∏ i ∈ s, b i|
        = |(a j - b j) * ∏ i ∈ s, a i + b j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)| := by ring_nf
      _ ≤ |(a j - b j) * ∏ i ∈ s, a i| + |b j * (∏ i ∈ s, a i - ∏ i ∈ s, b i)| := abs_add_le _ _
      _ ≤ |a j - b j| + |∏ i ∈ s, a i - ∏ i ∈ s, b i| := by
          rw [abs_mul, abs_mul, abs_of_nonneg hA0, abs_of_nonneg (hb j).1]
          gcongr
          · nlinarith [abs_nonneg (a j - b j)]
          · nlinarith [abs_nonneg (∏ i ∈ s, a i - ∏ i ∈ s, b i), (hb j).2]
      _ ≤ _ := by linarith

theorem plat_lipschitz (d : ℕ) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (N : ℕ) (x y : Euc d), |plat d N x - plat d N y| ≤ L * ‖x - y‖ := by
  obtain ⟨C, hC⟩ := S1_lipschitz
  refine ⟨d * (2 * C * d), by positivity, fun N x y => ?_⟩
  unfold plat
  refine (prod_sub_prod_le Finset.univ _ _ (fun i => plat_fac_mem d N x i)
    (fun i => plat_fac_mem d N y i)).trans ?_
  have hi : ∀ i : Fin d, |(S1 ((d : ℝ) * x i + N) - S1 ((d : ℝ) * x i - N - 1)) -
      (S1 ((d : ℝ) * y i + N) - S1 ((d : ℝ) * y i - N - 1))| ≤ 2 * C * d * ‖x - y‖ := by
    intro i
    have h1 := hC.dist_le_mul ((d : ℝ) * x i + N) ((d : ℝ) * y i + N)
    have h2 := hC.dist_le_mul ((d : ℝ) * x i - N - 1) ((d : ℝ) * y i - N - 1)
    rw [Real.dist_eq, Real.dist_eq] at h1 h2
    have hxy : |x i - y i| ≤ ‖x - y‖ := by simpa using PiLp.norm_apply_le (x - y) i
    have e1 : |((d : ℝ) * x i + N) - ((d : ℝ) * y i + N)| = d * |x i - y i| := by
      rw [show ((d : ℝ) * x i + N) - ((d : ℝ) * y i + N) = d * (x i - y i) by ring, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg d)]
    have e2 : |((d : ℝ) * x i - N - 1) - ((d : ℝ) * y i - N - 1)| = d * |x i - y i| := by
      rw [show ((d : ℝ) * x i - N - 1) - ((d : ℝ) * y i - N - 1) = d * (x i - y i) by ring, abs_mul,
        abs_of_nonneg (Nat.cast_nonneg d)]
    rw [e1] at h1
    rw [e2] at h2
    have hCn : (0 : ℝ) ≤ C := C.2
    have h3 : (d : ℝ) * |x i - y i| ≤ d * ‖x - y‖ := mul_le_mul_of_nonneg_left hxy (Nat.cast_nonneg d)
    calc _ ≤ |S1 ((d : ℝ) * x i + N) - S1 ((d : ℝ) * y i + N)| +
          |S1 ((d : ℝ) * x i - N - 1) - S1 ((d : ℝ) * y i - N - 1)| := by
          rw [show (S1 ((d : ℝ) * x i + N) - S1 ((d : ℝ) * x i - N - 1)) -
              (S1 ((d : ℝ) * y i + N) - S1 ((d : ℝ) * y i - N - 1)) =
              (S1 ((d : ℝ) * x i + N) - S1 ((d : ℝ) * y i + N)) -
              (S1 ((d : ℝ) * x i - N - 1) - S1 ((d : ℝ) * y i - N - 1)) by ring]
          exact abs_sub _ _
      _ ≤ C * (d * ‖x - y‖) + C * (d * ‖x - y‖) := by
          gcongr
          · exact h1.trans (by gcongr)
          · exact h2.trans (by gcongr)
      _ = 2 * C * d * ‖x - y‖ := by ring
  calc ∑ i : Fin d, _ ≤ ∑ _i : Fin d, 2 * (C : ℝ) * d * ‖x - y‖ := Finset.sum_le_sum fun i _ => hi i
    _ = (d : ℝ) * (2 * C * d) * ‖x - y‖ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring


/-- the unshifted piece `∏_i th1 (d x_i)` -/
def Th0 (d : ℕ) (x : Euc d) : ℝ := ∏ i, th1 ((d : ℝ) * x i)

/-- the corner `c_k` of the piece `Th d N k` (`Th d N k x = Th0 d (x - c_k)`) -/
def cvec (d N : ℕ) (k : Fin d → ℕ) : Euc d := WithLp.toLp 2 fun i => (((k i : ℝ) - N) / d)

/-- the center of the support of the piece `Th d N k` -/
def zc (d N : ℕ) (k : Fin d → ℕ) : Euc d := WithLp.toLp 2 fun i => (((k i : ℝ) - N + 1) / d)

theorem Th_eq {d : ℕ} (hd : 1 ≤ d) (N : ℕ) (k : Fin d → ℕ) (x : Euc d) :
    Th d N k x = Th0 d (x - cvec d N k) := by
  unfold Th Th0
  refine Finset.prod_congr rfl fun i _ => ?_
  have hd0 : (d : ℝ) ≠ 0 := by positivity
  congr 1
  simp only [cvec, PiLp.sub_apply]
  field_simp
  ring

theorem Th0_contDiff (d : ℕ) : ContDiff ℝ ∞ (Th0 d) := by
  unfold Th0
  refine contDiff_prod fun i _ => ?_
  have hc : ContDiff ℝ ∞ fun x : Euc d => x i :=
    (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  exact th1_contDiff.comp (contDiff_const.mul hc)

theorem Th_nonneg (d N : ℕ) (k : Fin d → ℕ) (x : Euc d) : 0 ≤ Th d N k x :=
  Finset.prod_nonneg fun i _ => th1_nonneg _

theorem Th_le_one (d N : ℕ) (k : Fin d → ℕ) (x : Euc d) : Th d N k x ≤ 1 :=
  Finset.prod_le_one₀ (fun i _ => th1_nonneg _) fun i _ => th1_le_one _

theorem Th_coord {d N : ℕ} {k : Fin d → ℕ} {x : Euc d} (hx : Th d N k x ≠ 0) (i : Fin d) :
    0 < (d : ℝ) * x i + N - k i ∧ (d : ℝ) * x i + N - k i < 2 := by
  have h := fun j => (fun h0 => hx (Finset.prod_eq_zero (Finset.mem_univ j) h0))
  constructor
  · by_contra hc
    push Not at hc
    exact h i (th1_zero_of_le hc) |>.elim
  · by_contra hc
    push Not at hc
    exact h i (th1_zero_of_ge hc) |>.elim

theorem Th_support {d : ℕ} (hd : 1 ≤ d) {N : ℕ} {k : Fin d → ℕ} {x : Euc d} (hx : Th d N k x ≠ 0) :
    ‖x - zc d N k‖ ≤ 1 := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast hd
  have hb : ∀ i, |(x - zc d N k) i| ≤ 1 / d := by
    intro i
    obtain ⟨h1, h2⟩ := Th_coord hx i
    simp only [zc, PiLp.sub_apply]
    have e : (x i - ((k i : ℝ) - N + 1) / d) * d = d * x i - ((k i : ℝ) - N + 1) := by
      field_simp
    rw [abs_le]
    constructor
    · rw [← neg_div, div_le_iff₀ hd0]; linarith
    · rw [le_div_iff₀ hd0]; linarith
  have h2 : ‖x - zc d N k‖ ^ 2 ≤ 1 := by
    rw [EuclideanSpace.norm_sq_eq]
    calc ∑ i, ‖(x - zc d N k) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 / (d : ℝ)) ^ 2 :=
          Finset.sum_le_sum fun i _ => by
            rw [Real.norm_eq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) (hb i) 2
      _ = 1 / (d : ℝ) := by
          simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          field_simp
      _ ≤ 1 := by
          rw [div_le_one hd0]; exact_mod_cast hd
  exact (sq_le_sq₀ (norm_nonneg _) zero_le_one).mp (by simpa using h2)


theorem Th_overlap (d N : ℕ) (x : Euc d) (B : Finset (Fin d → ℕ)) :
    (B.filter fun k => Th d N k x ≠ 0).card ≤ 2 ^ d := by
  classical
  set a : Fin d → ℕ := fun i => ⌈(d : ℝ) * x i + N⌉₊ - 2 with ha
  have hsub : B.filter (fun k => Th d N k x ≠ 0) ⊆
      Fintype.piFinset (fun i => ({a i, a i + 1} : Finset ℕ)) := by
    intro k hk
    rw [Finset.mem_filter] at hk
    rw [Fintype.mem_piFinset]
    intro i
    obtain ⟨h1, h2⟩ := Th_coord hk.2 i
    have hai : a i = ⌈(d : ℝ) * x i + N⌉₊ - 2 := rfl
    obtain ⟨cn, hcn⟩ : ∃ cn : ℕ, cn = ⌈(d : ℝ) * x i + N⌉₊ := ⟨_, rfl⟩
    rw [← hcn] at hai
    have hc1 : (d : ℝ) * x i + N ≤ cn := by rw [hcn]; exact Nat.le_ceil _
    have hc2 : ∀ n : ℕ, n < cn ↔ (n : ℝ) < (d : ℝ) * x i + N := fun n => by
      rw [hcn]; exact Nat.lt_ceil
    have hlow : a i ≤ k i := by
      by_contra hlt
      push Not at hlt
      have h3 : k i + 2 < cn := by omega
      have h4 := (hc2 _).mp h3
      push_cast at h4
      linarith
    have hup : k i ≤ a i + 1 := by
      by_contra hlt
      push Not at hlt
      have hge : cn ≤ k i := by omega
      have h4 : ¬ (k i < cn) := not_lt.mpr hge
      rw [hc2] at h4
      linarith
    simp only [Finset.mem_insert, Finset.mem_singleton]
    omega
  calc (B.filter fun k => Th d N k x ≠ 0).card
      ≤ (Fintype.piFinset (fun i : Fin d => ({a i, a i + 1} : Finset ℕ))).card :=
        Finset.card_le_card hsub
    _ ≤ 2 ^ d := by
        rw [Fintype.card_piFinset]
        calc ∏ i : Fin d, ({a i, a i + 1} : Finset ℕ).card ≤ ∏ _i : Fin d, 2 :=
              Finset.prod_le_prod' fun i _ => Finset.card_le_two
          _ = 2 ^ d := by simp

end HRS.Whole.Q09A
