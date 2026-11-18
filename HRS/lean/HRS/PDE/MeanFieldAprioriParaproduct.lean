import HRS.PDE.MeanFieldAprioriBernstein
import HRS.PDE.Galerkin
import HRS.PDE.MeanFieldProduct
import HRS.PDE.MeanFieldProductB

/-!
# (I3) AP5b: the paraproduct estimate (package MF-01)

`exists_paraproduct_bound`: `‖f ∂_i g ⋆ f‖_{H^σ} ≤ C ‖f‖_∞ ‖f‖_{H^{σ+b}}` for `σ ≥ 0`,
`max(θ-1,0) < b ≤ 1`, `θ = s - d + 2`.  Route: dyadic shells `2^{m+3} ≤ |k| < 2^{m+4}` of the output
frequency, the smooth low-frequency part `forceLow (m)` of the force (sup-bounded by AP5a, which
lives on `|j| < 2^{m+1}` so that only the tail `|k-j| ≥ 2^m` of `f̂` contributes) and the high
part (`ℓ²`-bounded by AP5a); both are controlled with `mulCoeff_l2_bound`.

`exists_nonlinear_loss_bound` follows from the paraproduct bound (interaction term) and the
`H^j` product bound for the smooth multiplier `∂_i V` (potential term).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFApriori

variable {d : ℕ}

/-! ### Dyadic shells -/

/-- the dyadic shell index of `k` (meaningful for `8 ≤ |k|`): `2^{m+3} ≤ |k| < 2^{m+4}`. -/
def shellIdx (k : Lattice d) : ℕ := Nat.log 2 ⌊Lattice.enorm k⌋₊ - 3

theorem shellIdx_spec {k : Lattice d} (h : 8 ≤ Lattice.enorm k) :
    (2 : ℝ) ^ (shellIdx k + 3) ≤ Lattice.enorm k ∧ Lattice.enorm k < (2 : ℝ) ^ (shellIdx k + 4) := by
  set e := Lattice.enorm k with he
  have h8 : 8 ≤ ⌊e⌋₊ := Nat.le_floor (by exact_mod_cast h)
  have hne : ⌊e⌋₊ ≠ 0 := by omega
  have hL : 3 ≤ Nat.log 2 ⌊e⌋₊ := Nat.le_log_of_pow_le (by norm_num) (by simpa using h8)
  have h1 : 2 ^ Nat.log 2 ⌊e⌋₊ ≤ ⌊e⌋₊ := Nat.pow_log_le_self 2 hne
  have h2 : ⌊e⌋₊ < 2 ^ (Nat.log 2 ⌊e⌋₊ + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
  have he0 : 0 ≤ e := by rw [he]; exact norm_nonneg _
  constructor
  · have hidx : shellIdx k + 3 = Nat.log 2 ⌊e⌋₊ := by simp only [shellIdx, ← he]; omega
    rw [hidx]
    calc (2 : ℝ) ^ Nat.log 2 ⌊e⌋₊ = ((2 ^ Nat.log 2 ⌊e⌋₊ : ℕ) : ℝ) := by push_cast; rfl
      _ ≤ (⌊e⌋₊ : ℝ) := by exact_mod_cast h1
      _ ≤ e := Nat.floor_le he0
  · have hidx : shellIdx k + 4 = Nat.log 2 ⌊e⌋₊ + 1 := by simp only [shellIdx, ← he]; omega
    rw [hidx]
    calc e < (⌊e⌋₊ : ℝ) + 1 := Nat.lt_floor_add_one e
      _ ≤ ((2 ^ (Nat.log 2 ⌊e⌋₊ + 1) : ℕ) : ℝ) := by exact_mod_cast h2
      _ = (2 : ℝ) ^ (Nat.log 2 ⌊e⌋₊ + 1) := by push_cast; rfl

theorem sobWeight_le_shell {σ : ℝ} (hσ : 0 ≤ σ) {k : Lattice d} {m : ℕ}
    (h : Lattice.enorm k < (2 : ℝ) ^ (m + 4)) :
    sobWeight σ k ≤ (1 + 4 * Real.pi ^ 2 * 256) ^ σ * ((2 : ℝ) ^ m) ^ (2 * σ) := by
  unfold sobWeight
  have h0 : 0 ≤ Lattice.enorm k := norm_nonneg _
  have hm1 : (1 : ℝ) ≤ ((2 : ℝ) ^ m) ^ 2 := one_le_pow₀ (one_le_pow₀ (by norm_num))
  have hsq : Lattice.enorm k ^ 2 ≤ 256 * ((2 : ℝ) ^ m) ^ 2 := by
    have : Lattice.enorm k ^ 2 ≤ ((2 : ℝ) ^ (m + 4)) ^ 2 := by gcongr
    calc _ ≤ _ := this
      _ = 256 * ((2 : ℝ) ^ m) ^ 2 := by rw [pow_add]; ring
  have hle : 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 ≤
      (1 + 4 * Real.pi ^ 2 * 256) * ((2 : ℝ) ^ m) ^ 2 := by
    nlinarith [Real.pi_pos, sq_nonneg Real.pi]
  have hpos : 0 ≤ 1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
  calc (1 + 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) ^ σ
      ≤ ((1 + 4 * Real.pi ^ 2 * 256) * ((2 : ℝ) ^ m) ^ 2) ^ σ := Real.rpow_le_rpow hpos hle hσ
    _ = (1 + 4 * Real.pi ^ 2 * 256) ^ σ * ((2 : ℝ) ^ m) ^ (2 * σ) := by
        rw [Real.mul_rpow (by positivity) (by positivity)]
        congr 1
        rw [← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        push_cast
        ring_nf

theorem sobWeight_le_crude {σ : ℝ} (hσ : 0 ≤ σ) {k : Lattice d} (h : Lattice.enorm k < 8) :
    sobWeight σ k ≤ (1 + 4 * Real.pi ^ 2 * 64) ^ σ := by
  unfold sobWeight
  have h0 : 0 ≤ Lattice.enorm k := norm_nonneg _
  have : Lattice.enorm k ^ 2 ≤ 64 := by nlinarith
  exact Real.rpow_le_rpow (by positivity) (by nlinarith [Real.pi_pos, sq_nonneg Real.pi]) hσ

/-! ### Summation over shells -/

theorem fine_shell_sum (P : ℕ → Coeff d) (hP : ∀ m, Summable fun k => ‖P m k‖ ^ 2) {σ : ℝ}
    (hσ : 0 ≤ σ) (S : Finset (Lattice d)) (M : ℕ)
    (hM : ∀ k ∈ S, 8 ≤ Lattice.enorm k → shellIdx k ≤ M) :
    ∑ k ∈ S, (if 8 ≤ Lattice.enorm k then sobWeight σ k * ‖P (shellIdx k) k‖ ^ 2 else 0) ≤
      ∑ m ∈ Finset.range (M + 1), (1 + 4 * Real.pi ^ 2 * 256) ^ σ * ((2 : ℝ) ^ m) ^ (2 * σ) *
        ∑' k, ‖P m k‖ ^ 2 := by
  classical
  set S' := S.filter (fun k => 8 ≤ Lattice.enorm k) with hS'
  have h1 : ∑ k ∈ S, (if 8 ≤ Lattice.enorm k then sobWeight σ k * ‖P (shellIdx k) k‖ ^ 2 else 0) =
      ∑ k ∈ S', sobWeight σ k * ‖P (shellIdx k) k‖ ^ 2 := by
    rw [hS', Finset.sum_filter]
  rw [h1]
  have h2 : ∑ k ∈ S', sobWeight σ k * ‖P (shellIdx k) k‖ ^ 2 ≤
      ∑ k ∈ S', (1 + 4 * Real.pi ^ 2 * 256) ^ σ * ((2 : ℝ) ^ (shellIdx k)) ^ (2 * σ) *
        ‖P (shellIdx k) k‖ ^ 2 := by
    refine Finset.sum_le_sum fun k hk => ?_
    have hk8 : 8 ≤ Lattice.enorm k := (Finset.mem_filter.1 hk).2
    gcongr
    exact sobWeight_le_shell hσ (shellIdx_spec hk8).2
  refine h2.trans ?_
  have hmaps : ∀ k ∈ S', shellIdx k ∈ Finset.range (M + 1) := fun k hk => by
    have := Finset.mem_filter.1 hk
    exact Finset.mem_range.2 (Nat.lt_succ_of_le (hM k this.1 this.2))
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  refine Finset.sum_le_sum fun m _ => ?_
  have : ∀ k ∈ S'.filter (fun k => shellIdx k = m),
      (1 + 4 * Real.pi ^ 2 * 256) ^ σ * ((2 : ℝ) ^ (shellIdx k)) ^ (2 * σ) *
        ‖P (shellIdx k) k‖ ^ 2 =
      (1 + 4 * Real.pi ^ 2 * 256) ^ σ * ((2 : ℝ) ^ m) ^ (2 * σ) * ‖P m k‖ ^ 2 := by
    intro k hk
    rw [(Finset.mem_filter.1 hk).2]
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum]
  refine mul_le_mul_of_nonneg_left ?_ (by positivity)
  exact (hP m).sum_le_tsum _ (fun k _ => by positivity)

/-! ### Dyadic tail sums -/

theorem enorm_rpow_le_sobWeight {γ : ℝ} (hγ : 0 ≤ γ) (j : Lattice d) :
    Lattice.enorm j ^ γ ≤ sobWeight (γ / 2) j := by
  unfold sobWeight
  have h0 : 0 ≤ Lattice.enorm j := norm_nonneg _
  calc Lattice.enorm j ^ γ = (Lattice.enorm j ^ 2) ^ (γ / 2) := by
        rw [← Real.rpow_natCast, ← Real.rpow_mul h0]; congr 1; push_cast; ring
    _ ≤ _ := Real.rpow_le_rpow (by positivity)
        (by
          have hpi : 1 ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
          have := mul_le_mul_of_nonneg_right hpi (sq_nonneg (Lattice.enorm j))
          linarith) (by positivity)

theorem dyadic_pointwise {γ : ℝ} (hγ : 0 < γ) (j : Lattice d) (N : ℕ) :
    ∑ m ∈ Finset.range N, (if (2 : ℝ) ^ m ≤ Lattice.enorm j then ((2 : ℝ) ^ m) ^ γ else 0) ≤
      ((2 : ℝ) ^ γ / ((2 : ℝ) ^ γ - 1)) * sobWeight (γ / 2) j := by
  classical
  have hρ : 1 < (2 : ℝ) ^ γ := Real.one_lt_rpow (by norm_num) hγ
  have hK : 0 ≤ (2 : ℝ) ^ γ / ((2 : ℝ) ^ γ - 1) := by
    have : 0 < (2 : ℝ) ^ γ - 1 := by linarith
    positivity
  have hW : 0 ≤ sobWeight (γ / 2) j := (sobWeight_posC _ j).le
  by_cases he : Lattice.enorm j < 1
  · have : ∀ m ∈ Finset.range N, (if (2 : ℝ) ^ m ≤ Lattice.enorm j then ((2 : ℝ) ^ m) ^ γ else 0) = 0 := by
      intro m _
      have : ¬ ((2 : ℝ) ^ m ≤ Lattice.enorm j) := by
        push Not
        exact lt_of_lt_of_le he (one_le_pow₀ (by norm_num))
      simp [this]
    rw [Finset.sum_eq_zero this]
    positivity
  · push Not at he
    set e := Lattice.enorm j with hedef
    have he0 : 0 ≤ e := by linarith
    have hfl : 1 ≤ ⌊e⌋₊ := Nat.le_floor (by simpa using he)
    set L := Nat.log 2 ⌊e⌋₊ with hL
    have hmem : ∀ m : ℕ, (2 : ℝ) ^ m ≤ e → m ≤ L := by
      intro m hm
      have : 2 ^ m ≤ ⌊e⌋₊ := Nat.le_floor (by exact_mod_cast hm)
      exact Nat.le_log_of_pow_le (by norm_num) this
    have hL2 : (2 : ℝ) ^ L ≤ e := by
      have h1 : 2 ^ L ≤ ⌊e⌋₊ := Nat.pow_log_le_self 2 (by omega)
      calc (2 : ℝ) ^ L = ((2 ^ L : ℕ) : ℝ) := by push_cast; rfl
        _ ≤ (⌊e⌋₊ : ℝ) := by exact_mod_cast h1
        _ ≤ e := Nat.floor_le he0
    rw [← Finset.sum_filter]
    calc ∑ m ∈ (Finset.range N).filter (fun m => (2 : ℝ) ^ m ≤ e), ((2 : ℝ) ^ m) ^ γ
        ≤ ∑ m ∈ Finset.range (L + 1), ((2 : ℝ) ^ m) ^ γ := by
          refine Finset.sum_le_sum_of_subset_of_nonneg ?_ (fun m _ _ => by positivity)
          intro m hm
          exact Finset.mem_range.2 (Nat.lt_succ_of_le (hmem m (Finset.mem_filter.1 hm).2))
      _ ≤ ((2 : ℝ) ^ L) ^ γ * ((2 : ℝ) ^ γ / ((2 : ℝ) ^ γ - 1)) := by
          have := sum_rpow_two_pow_le (θ := γ) (b := γ) hγ le_rfl L
          linarith
      _ ≤ e ^ γ * ((2 : ℝ) ^ γ / ((2 : ℝ) ^ γ - 1)) := by
          gcongr
      _ ≤ sobWeight (γ / 2) j * ((2 : ℝ) ^ γ / ((2 : ℝ) ^ γ - 1)) := by
          gcongr
          exact enorm_rpow_le_sobWeight hγ.le j
      _ = _ := by ring

theorem dyadic_tail_sum {γ : ℝ} (hγ : 0 < γ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ c : Lattice d → ℝ, (∀ j, 0 ≤ c j) → Summable c →
      Summable (fun j => sobWeight (γ / 2) j * c j) → ∀ N : ℕ,
      ∑ m ∈ Finset.range N, ((2 : ℝ) ^ m) ^ γ *
          ∑' j, (if (2 : ℝ) ^ m ≤ Lattice.enorm j then c j else 0) ≤
        K * ∑' j, sobWeight (γ / 2) j * c j := by
  classical
  have hρ : 1 < (2 : ℝ) ^ γ := Real.one_lt_rpow (by norm_num) hγ
  have hK : 0 ≤ (2 : ℝ) ^ γ / ((2 : ℝ) ^ γ - 1) := by
    have : 0 < (2 : ℝ) ^ γ - 1 := by linarith
    positivity
  refine ⟨(2 : ℝ) ^ γ / ((2 : ℝ) ^ γ - 1), hK, fun c hc0 hcs hcw N => ?_⟩
  have hsum : ∀ m : ℕ, Summable fun j => ((2 : ℝ) ^ m) ^ γ *
      (if (2 : ℝ) ^ m ≤ Lattice.enorm j then c j else 0) := by
    intro m
    refine Summable.mul_left _ (Summable.of_nonneg_of_le (fun j => ?_) (fun j => ?_) hcs)
    · split_ifs <;> simp [hc0 j]
    · split_ifs <;> simp [hc0 j]
  have h1 : ∑ m ∈ Finset.range N, ((2 : ℝ) ^ m) ^ γ *
          ∑' j, (if (2 : ℝ) ^ m ≤ Lattice.enorm j then c j else 0) =
      ∑' j, ∑ m ∈ Finset.range N, ((2 : ℝ) ^ m) ^ γ *
          (if (2 : ℝ) ^ m ≤ Lattice.enorm j then c j else 0) := by
    rw [Summable.tsum_finsetSum (fun m _ => hsum m)]
    refine Finset.sum_congr rfl fun m _ => ?_
    rw [tsum_mul_left]
  rw [h1, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun j => ?_) (summable_sum fun m _ => hsum m) (hcw.mul_left _)
  have : ∑ m ∈ Finset.range N, ((2 : ℝ) ^ m) ^ γ *
          (if (2 : ℝ) ^ m ≤ Lattice.enorm j then c j else 0) =
      c j * ∑ m ∈ Finset.range N, (if (2 : ℝ) ^ m ≤ Lattice.enorm j then ((2 : ℝ) ^ m) ^ γ else 0) := by
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun m _ => ?_
    split_ifs <;> ring
  rw [this]
  calc c j * ∑ m ∈ Finset.range N, (if (2 : ℝ) ^ m ≤ Lattice.enorm j then ((2 : ℝ) ^ m) ^ γ else 0)
      ≤ c j * (((2 : ℝ) ^ γ / ((2 : ℝ) ^ γ - 1)) * sobWeight (γ / 2) j) :=
        mul_le_mul_of_nonneg_left (dyadic_pointwise hγ j N) (hc0 j)
    _ = _ := by ring

/-! ### Convolution and weight lemmas -/

theorem mulCoeff_comm (a c : Coeff d) (k : Lattice d) : mulCoeff a c k = mulCoeff c a k := by
  unfold mulCoeff
  rw [← (Equiv.subLeft k).tsum_eq (fun j => c (k - j) * a j)]
  refine tsum_congr fun j => ?_
  simp [Equiv.subLeft_apply, mul_comm]

theorem mulCoeff_add_right {a c₁ c₂ : Coeff d} (ha : MemHs 0 a) (h₁ : MemHs 0 c₁) (h₂ : MemHs 0 c₂)
    (k : Lattice d) : mulCoeff a (fun j => c₁ j + c₂ j) k = mulCoeff a c₁ k + mulCoeff a c₂ k := by
  unfold mulCoeff
  rw [← Summable.tsum_add (summable_mulCoeff a c₁ ha h₁ k) (summable_mulCoeff a c₂ ha h₂ k)]
  exact tsum_congr fun j => by ring

theorem sobWeight_mono_exp {a b : ℝ} (hab : a ≤ b) (k : Lattice d) : sobWeight a k ≤ sobWeight b k := by
  unfold sobWeight
  exact Real.rpow_le_rpow_of_exponent_le
    (by nlinarith [sq_nonneg (Real.pi * Lattice.enorm k), Real.pi_pos]) hab

theorem memHs_mono' {a b : ℝ} (hab : a ≤ b) {c : Coeff d} (hc : MemHs b c) : MemHs a c :=
  Summable.of_nonneg_of_le (fun k => by have := sobWeight_posC a (d := d) k; positivity)
    (fun k => mul_le_mul_of_nonneg_right (sobWeight_mono_exp hab k) (by positivity)) hc

theorem hsNormSq_mono' {a b : ℝ} (hab : a ≤ b) {c : Coeff d} (hc : MemHs b c) :
    hsNormSq a c ≤ hsNormSq b c :=
  Summable.tsum_le_tsum (fun k => mul_le_mul_of_nonneg_right (sobWeight_mono_exp hab k)
    (by positivity)) (memHs_mono' hab hc) hc

theorem abs_le_enorm (k : Lattice d) (i : Fin d) : |(k i : ℝ)| ≤ Lattice.enorm k := by
  have h2 : ‖(Lattice.toEuc k) i‖ ≤ ‖Lattice.toEuc k‖ := PiLp.norm_apply_le _ i
  simpa [Lattice.toEuc, Lattice.enorm] using h2

/-! ### Properties of `forceLow` -/

theorem norm_forceLow_le (s : ℝ) (i : Fin d) (n : ℕ) (c : Coeff d) (k : Lattice d) :
    ‖forceLow d s i n c k‖ ≤ ‖gradRieszCoeff d s i c k‖ := by
  unfold forceLow
  rw [norm_mul, Complex.norm_real, Real.norm_eq_abs,
    abs_of_nonneg (chiF_nonneg d _)]
  exact mul_le_of_le_one_left (norm_nonneg _) (chiF_le_one d _)

theorem norm_sub_forceLow_le (s : ℝ) (i : Fin d) (n : ℕ) (c : Coeff d) (k : Lattice d) :
    ‖gradRieszCoeff d s i c k - forceLow d s i n c k‖ ≤ ‖gradRieszCoeff d s i c k‖ := by
  rw [sub_forceLow]
  have h0 := chiF_nonneg d (LevyAux.eps n • Lattice.toEuc k)
  have h1 := chiF_le_one d (LevyAux.eps n • Lattice.toEuc k)
  rw [norm_mul]
  have : ‖(1 - ((LevyAux.chiF d (LevyAux.eps n • Lattice.toEuc k) : ℝ) : ℂ))‖ ≤ 1 := by
    have e : (1 - ((LevyAux.chiF d (LevyAux.eps n • Lattice.toEuc k) : ℝ) : ℂ)) =
        ((1 - LevyAux.chiF d (LevyAux.eps n • Lattice.toEuc k) : ℝ) : ℂ) := by push_cast; ring
    rw [e, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (by linarith)]
    linarith
  exact mul_le_of_le_one_left (norm_nonneg _) this

theorem forceLow_support (s : ℝ) (i : Fin d) (m : ℕ) (c : Coeff d) {j : Lattice d}
    (h : forceLow d s i m c j ≠ 0) : Lattice.enorm j < (2 : ℝ) ^ (m + 1) := by
  by_contra hcon
  push Not at hcon
  apply h
  have hχ : LevyAux.chiF d (LevyAux.eps m • Lattice.toEuc j) = 0 := by
    apply LevyAux.chiF_zero
    rw [norm_smul, Real.norm_of_nonneg (LevyAux.eps_pos m).le]
    unfold LevyAux.eps
    have hp : (0 : ℝ) < (2 : ℝ) ^ m := by positivity
    rw [← div_eq_inv_mul, le_div_iff₀ hp]
    have : ‖Lattice.toEuc j‖ = Lattice.enorm j := rfl
    rw [this, pow_succ] at *
    linarith
  simp [forceLow, hχ]

theorem isTrigPoly_forceLow (s : ℝ) (i : Fin d) (m : ℕ) (c : Coeff d) :
    IsTrigPoly (2 ^ (m + 1)) (forceLow d s i m c) := by
  intro k hk
  have h1 := forceLow_support s i m c hk
  intro i'
  have h2 := abs_le_enorm k i'
  have h3 : (|(k i' : ℝ)|) < (2 : ℝ) ^ (m + 1) := lt_of_le_of_lt h2 h1
  have h4 : |k i'| < ((2 ^ (m + 1) : ℕ) : ℤ) := by
    have : ((|k i'| : ℤ) : ℝ) < (((2 ^ (m + 1) : ℕ) : ℤ) : ℝ) := by
      push_cast
      simpa using h3
    exact_mod_cast this
  exact h4.le

theorem isRealCoeff_forceLow (s : ℝ) (i : Fin d) (m : ℕ) {c : Coeff d} (hc : IsRealCoeff c) :
    IsRealCoeff (forceLow d s i m c) := by
  intro k
  have hneg : Lattice.toEuc (-k) = -Lattice.toEuc k := by ext i; simp [Lattice.toEuc]
  have hr : rieszCoeff d s (-k) = rieszCoeff d s k := by
    unfold rieszCoeff
    simp only [neg_eq_zero, enorm_neg']
  have hχ : LevyAux.chiF d (LevyAux.eps m • Lattice.toEuc (-k)) =
      LevyAux.chiF d (LevyAux.eps m • Lattice.toEuc k) := by
    rw [hneg, smul_neg, LevyAux.chiF_neg]
  simp only [forceLow, gradRieszCoeff, derivCoeff, rieszMult, hc k, hr, hχ, map_mul,
    Complex.conj_ofReal, Complex.conj_I, map_intCast, map_ofNat, Pi.neg_apply, Int.cast_neg]
  ring

theorem memHs_zero_of_norm_le {a b : Coeff d} (h : ∀ k, ‖a k‖ ≤ ‖b k‖) (hb : MemHs 0 b) :
    MemHs 0 a := by
  rw [memHs_zero_iff] at hb ⊢
  exact Summable.of_nonneg_of_le (fun k => by positivity)
    (fun k => by gcongr; exact h k) hb

theorem hsNormSq_zero_le_of_norm_le {a b : Coeff d} (h : ∀ k, ‖a k‖ ≤ ‖b k‖) (hb : MemHs 0 b) :
    hsNormSq 0 a ≤ hsNormSq 0 b := by
  rw [hsNormSq_zero, hsNormSq_zero]
  refine Summable.tsum_le_tsum (fun k => by gcongr; exact h k) ?_ ((memHs_zero_iff b).1 hb)
  exact (memHs_zero_iff a).1 (memHs_zero_of_norm_le h hb)

/-- the tail `{|j| ≥ 2^m}` of a coefficient sequence -/
def tailCoeff (m : ℕ) (c : Coeff d) : Coeff d :=
  fun j => if (2 : ℝ) ^ m ≤ Lattice.enorm j then c j else 0

theorem norm_tailCoeff_le (m : ℕ) (c : Coeff d) (j : Lattice d) : ‖tailCoeff m c j‖ ≤ ‖c j‖ := by
  unfold tailCoeff
  split_ifs <;> simp

theorem norm_tailCoeff_sq (m : ℕ) (c : Coeff d) (j : Lattice d) :
    ‖tailCoeff m c j‖ ^ 2 = if (2 : ℝ) ^ m ≤ Lattice.enorm j then ‖c j‖ ^ 2 else 0 := by
  unfold tailCoeff
  split_ifs <;> simp

theorem hsNormSq_zero_tailCoeff (m : ℕ) (c : Coeff d) :
    hsNormSq 0 (tailCoeff m c) = ∑' j, (if (2 : ℝ) ^ m ≤ Lattice.enorm j then ‖c j‖ ^ 2 else 0) := by
  rw [hsNormSq_zero]
  exact tsum_congr fun j => norm_tailCoeff_sq m c j

/-- `ℓ²` bound for the gradient of the Riesz potential. -/
theorem grad_l2_bound (s : ℝ) (i : Fin d) :
    ∃ Cs : ℝ, 0 ≤ Cs ∧ ∀ (a : ℝ), s - d + 1 ≤ a → ∀ F : Coeff d, MemHs a F →
      MemHs 0 (gradRieszCoeff d s i F) ∧ hsNormSq 0 (gradRieszCoeff d s i F) ≤ Cs * hsNormSq a F := by
  refine ⟨rieszConst d s ^ 2 * (1 + (2 : ℝ) ^ (-(s - (d : ℝ) + 1))), by positivity, fun a ha F hF => ?_⟩
  set Cs := rieszConst d s ^ 2 * (1 + (2 : ℝ) ^ (-(s - (d : ℝ) + 1))) with hCs
  have hpt : ∀ k, ‖gradRieszCoeff d s i F k‖ ^ 2 ≤ Cs * (sobWeight a k * ‖F k‖ ^ 2) := by
    intro k
    rw [norm_gradRieszCoeff]
    calc (2 * Real.pi * |(k i : ℝ)| * |rieszCoeff d s k| * ‖F k‖) ^ 2
        = (2 * Real.pi * |(k i : ℝ)| * |rieszCoeff d s k|) ^ 2 * ‖F k‖ ^ 2 := by ring
      _ ≤ (Cs * sobWeight (s - (d : ℝ) + 1) k) * ‖F k‖ ^ 2 := by
          gcongr
          exact sq_symbol_le d s i k
      _ ≤ (Cs * sobWeight a k) * ‖F k‖ ^ 2 := by
          gcongr
          exact sobWeight_mono_exp ha k
      _ = _ := by ring
  have hs : Summable fun k => ‖gradRieszCoeff d s i F k‖ ^ 2 :=
    Summable.of_nonneg_of_le (fun k => by positivity) hpt (hF.mul_left Cs)
  refine ⟨(memHs_zero_iff _).2 hs, ?_⟩
  rw [hsNormSq_zero]
  calc ∑' k, ‖gradRieszCoeff d s i F k‖ ^ 2 ≤ ∑' k, Cs * (sobWeight a k * ‖F k‖ ^ 2) :=
        Summable.tsum_le_tsum hpt hs (hF.mul_left Cs)
    _ = Cs * hsNormSq a F := by rw [tsum_mul_left]; rfl

/-- fixed-scale low piece: `‖u_low · F_{≥2^m}‖₂ ≤ C 2^{mb} ‖f‖_∞ ‖F_{≥2^m}‖₂`. -/
theorem low_piece_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (b : ℝ)
    (hb : max (s - d + 1) 0 < b) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f : Torus d → ℝ), Continuous f → MemHs 0 (coeffOf f) → ∀ m : ℕ,
      MemHs 0 (mulCoeff (forceLow d s i m (coeffOf f)) (tailCoeff m (coeffOf f))) ∧
      hsNormSq 0 (mulCoeff (forceLow d s i m (coeffOf f)) (tailCoeff m (coeffOf f))) ≤
        (C * ((2 : ℝ) ^ m) ^ b * Torus.supNorm f) ^ 2 * hsNormSq 0 (tailCoeff m (coeffOf f)) := by
  obtain ⟨C, hC0, hC⟩ := exists_forceLow_sup_bound hd s hs0 hsd b hb i
  refine ⟨C, hC0, fun f hf hF m => ?_⟩
  have hreal : IsRealCoeff (coeffOf f) := fun k => (conj_coeffOfC f k).symm
  set ul := forceLow d s i m (coeffOf f) with hul
  have hreal' : IsRealCoeff ul := isRealCoeff_forceLow s i m hreal
  have hsum : Summable fun k => ‖ul k‖ := by
    refine summable_of_ne_finset_zero (s := boxFinset d (2 ^ (m + 1))) fun k hk => ?_
    have h0 : ul k = 0 := (isTrigPoly_forceLow s i m (coeffOf f)).eq_zero
      (fun h => hk (mem_boxFinset.2 h))
    rw [h0]
    simp
  have hcoef : coeffOf (toFun ul) = ul := coeffOf_toFun ul hreal' hsum
  have hcont : Continuous (toFun ul) := MFProduct.continuous_toFun ul hsum
  have hsup : Torus.supNorm (toFun ul) ≤ C * ((2 : ℝ) ^ m) ^ b * Torus.supNorm f := by
    refine Real.iSup_le (fun x => ?_) (by have := supNorm_nonneg f; positivity)
    rw [Real.norm_eq_abs]
    exact hC m f hf x
  have htail : MemHs 0 (tailCoeff m (coeffOf f)) :=
    memHs_zero_of_norm_le (norm_tailCoeff_le m _) hF
  obtain ⟨h1, h2⟩ := mulCoeff_l2_bound hcont htail
  rw [hcoef] at h1 h2
  refine ⟨h1, h2.trans ?_⟩
  gcongr
  · exact hsNormSq_nonneg _ _
  · exact supNorm_nonneg _

/-- fixed-scale high piece. -/
theorem high_piece_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (i : Fin d) :
    ∃ Ch : ℝ, 0 ≤ Ch ∧ ∀ (f : Torus d → ℝ), Continuous f → MemHs (s - d + 1) (coeffOf f) → ∀ m : ℕ,
      MemHs 0 (mulCoeff (coeffOf f) (fun j => gradRieszCoeff d s i (coeffOf f) j -
        forceLow d s i m (coeffOf f) j)) ∧
      hsNormSq 0 (mulCoeff (coeffOf f) (fun j => gradRieszCoeff d s i (coeffOf f) j -
        forceLow d s i m (coeffOf f) j)) ≤
        Torus.supNorm f ^ 2 * (Ch * ∑' j, (if (2 : ℝ) ^ m ≤ Lattice.enorm j then
          sobWeight (s - d + 1) j * ‖coeffOf f j‖ ^ 2 else 0)) := by
  obtain ⟨Ch, hCh0, hCh⟩ := forceHigh_l2_bound hd s hs0 hsd i
  refine ⟨Ch, hCh0, fun f hf hF m => ?_⟩
  set F := coeffOf f with hFdef
  obtain ⟨Cs, -, hCs⟩ := grad_l2_bound (d := d) s i
  have hu : MemHs 0 (gradRieszCoeff d s i F) := (hCs _ le_rfl F hF).1
  set uh : Coeff d := fun j => gradRieszCoeff d s i F j - forceLow d s i m F j with huh
  have huhM : MemHs 0 uh :=
    memHs_zero_of_norm_le (fun j => norm_sub_forceLow_le s i m F j) hu
  have hdom : Summable fun j => (if (2 : ℝ) ^ m ≤ Lattice.enorm j then
      sobWeight (s - d + 1) j * ‖F j‖ ^ 2 else 0) :=
    Summable.of_nonneg_of_le
      (fun j => by
        split_ifs
        · exact mul_nonneg (sobWeight_posC _ j).le (sq_nonneg _)
        · exact le_rfl)
      (fun j => by
        split_ifs
        · exact le_rfl
        · exact mul_nonneg (sobWeight_posC _ j).le (sq_nonneg _)) hF
  have hle : ∀ j, ‖uh j‖ ^ 2 ≤ Ch * (if (2 : ℝ) ^ m ≤ Lattice.enorm j then
      sobWeight (s - d + 1) j * ‖F j‖ ^ 2 else 0) := fun j => hCh m F j
  have hnorm : hsNormSq 0 uh ≤ Ch * ∑' j, (if (2 : ℝ) ^ m ≤ Lattice.enorm j then
      sobWeight (s - d + 1) j * ‖F j‖ ^ 2 else 0) := by
    rw [hsNormSq_zero, ← tsum_mul_left]
    exact Summable.tsum_le_tsum hle ((memHs_zero_iff uh).1 huhM) (hdom.mul_left Ch)
  obtain ⟨h1, h2⟩ := mulCoeff_l2_bound hf huhM
  refine ⟨h1, h2.trans ?_⟩
  exact mul_le_mul_of_nonneg_left hnorm (sq_nonneg _)

/-- On the output shell `|k| ≥ 2^{m+3}` only the tail of `f̂` contributes against `u_low`. -/
theorem mulCoeff_split_shell (s : ℝ) (i : Fin d) (m : ℕ) {F : Coeff d} (hF : MemHs 0 F)
    (hu : MemHs 0 (gradRieszCoeff d s i F)) {k : Lattice d} (hk : (2 : ℝ) ^ (m + 3) ≤ Lattice.enorm k) :
    mulCoeff F (gradRieszCoeff d s i F) k =
      mulCoeff (forceLow d s i m F) (tailCoeff m F) k +
        mulCoeff F (fun j => gradRieszCoeff d s i F j - forceLow d s i m F j) k := by
  have hul : MemHs 0 (forceLow d s i m F) :=
    memHs_zero_of_norm_le (fun j => norm_forceLow_le s i m F j) hu
  have huh : MemHs 0 (fun j => gradRieszCoeff d s i F j - forceLow d s i m F j) :=
    memHs_zero_of_norm_le (fun j => norm_sub_forceLow_le s i m F j) hu
  have h1 : mulCoeff F (gradRieszCoeff d s i F) k =
      mulCoeff F (fun j => forceLow d s i m F j +
        (gradRieszCoeff d s i F j - forceLow d s i m F j)) k := by
    unfold mulCoeff
    exact tsum_congr fun j => by ring
  rw [h1, mulCoeff_add_right hF hul huh k, mulCoeff_comm (forceLow d s i m F)]
  congr 1
  unfold mulCoeff
  refine tsum_congr fun j => ?_
  by_cases hj : forceLow d s i m F j = 0
  · simp [hj]
  · have h2 := forceLow_support s i m F hj
    have h3 := enorm_le_add k j
    have h4 : (2 : ℝ) ^ m ≤ Lattice.enorm (k - j) := by
      have : (2 : ℝ) ^ (m + 3) = 8 * 2 ^ m := by rw [pow_add]; ring
      have h5 : (2 : ℝ) ^ (m + 1) = 2 * 2 ^ m := by rw [pow_succ]; ring
      nlinarith [pow_pos (show (0 : ℝ) < 2 by norm_num) m]
    simp [tailCoeff, h4]

/-! ### Summation over the dyadic scales -/

theorem rpow_two_mul_aux {x : ℝ} (hx : 0 < x) (σ b : ℝ) :
    x ^ (2 * σ) * (x ^ b) ^ 2 = x ^ (2 * (σ + b)) := by
  have : (x ^ b) ^ 2 = x ^ (2 * b) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hx.le]
    norm_num
    ring_nf
  rw [this, ← Real.rpow_add hx]
  ring_nf

theorem sum_low_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (b : ℝ)
    (hb : max (s - d + 1) 0 < b) (i : Fin d) {σ : ℝ} (hσ : 0 < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : Torus d → ℝ, Continuous f → MemHs (σ + b) (coeffOf f) → ∀ N : ℕ,
      ∑ m ∈ Finset.range N, (1 + 4 * Real.pi ^ 2 * 256) ^ σ * ((2 : ℝ) ^ m) ^ (2 * σ) *
        ∑' k, ‖mulCoeff (forceLow d s i m (coeffOf f)) (tailCoeff m (coeffOf f)) k‖ ^ 2 ≤
        K * Torus.supNorm f ^ 2 * hsNormSq (σ + b) (coeffOf f) := by
  obtain ⟨Cl, hCl0, hCl⟩ := low_piece_bound hd s hs0 hsd b hb i
  have hb0 : 0 < b := lt_of_le_of_lt (le_max_right _ _) hb
  have hγ : 0 < 2 * (σ + b) := by positivity
  obtain ⟨K1, hK1, hdy⟩ := dyadic_tail_sum (d := d) hγ
  have hγ2 : 2 * (σ + b) / 2 = σ + b := by ring
  set Cw := (1 + 4 * Real.pi ^ 2 * 256) ^ σ with hCw
  have hCw0 : 0 ≤ Cw := by positivity
  refine ⟨Cw * Cl ^ 2 * K1, by positivity, fun f hf hFσ N => ?_⟩
  set F := coeffOf f with hFdef
  have hF0 : MemHs 0 F := memHs_mono' (by linarith) hFσ
  have hdy' := hdy (fun j => ‖F j‖ ^ 2) (fun j => by positivity) ((memHs_zero_iff F).1 hF0)
    (by rw [hγ2]; exact hFσ) N
  rw [hγ2] at hdy'
  calc ∑ m ∈ Finset.range N, Cw * ((2 : ℝ) ^ m) ^ (2 * σ) *
        ∑' k, ‖mulCoeff (forceLow d s i m F) (tailCoeff m F) k‖ ^ 2
      ≤ ∑ m ∈ Finset.range N, Cw * ((2 : ℝ) ^ m) ^ (2 * σ) *
          ((Cl * ((2 : ℝ) ^ m) ^ b * Torus.supNorm f) ^ 2 *
            ∑' j, (if (2 : ℝ) ^ m ≤ Lattice.enorm j then ‖F j‖ ^ 2 else 0)) := by
        refine Finset.sum_le_sum fun m _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        obtain ⟨-, h2⟩ := hCl f hf hF0 m
        rw [hsNormSq_zero, hsNormSq_zero_tailCoeff] at h2
        exact h2
    _ = Cw * Cl ^ 2 * Torus.supNorm f ^ 2 * ∑ m ∈ Finset.range N, ((2 : ℝ) ^ m) ^ (2 * (σ + b)) *
          ∑' j, (if (2 : ℝ) ^ m ≤ Lattice.enorm j then ‖F j‖ ^ 2 else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        rw [← rpow_two_mul_aux (by positivity : (0 : ℝ) < 2 ^ m) σ b]
        ring
    _ ≤ Cw * Cl ^ 2 * Torus.supNorm f ^ 2 *
          (K1 * ∑' j, sobWeight (σ + b) j * ‖F j‖ ^ 2) :=
        mul_le_mul_of_nonneg_left hdy' (by positivity)
    _ = Cw * Cl ^ 2 * K1 * Torus.supNorm f ^ 2 * hsNormSq (σ + b) F := by
        unfold hsNormSq; ring

theorem sum_high_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (b : ℝ)
    (hb : max (s - d + 1) 0 < b) (i : Fin d) {σ : ℝ} (hσ : 0 < σ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ f : Torus d → ℝ, Continuous f → MemHs (σ + b) (coeffOf f) → ∀ N : ℕ,
      ∑ m ∈ Finset.range N, (1 + 4 * Real.pi ^ 2 * 256) ^ σ * ((2 : ℝ) ^ m) ^ (2 * σ) *
        ∑' k, ‖mulCoeff (coeffOf f) (fun j => gradRieszCoeff d s i (coeffOf f) j -
          forceLow d s i m (coeffOf f) j) k‖ ^ 2 ≤
        K * Torus.supNorm f ^ 2 * hsNormSq (σ + b) (coeffOf f) := by
  obtain ⟨Ch, hCh0, hCh⟩ := high_piece_bound hd s hs0 hsd i
  have hγ : 0 < 2 * σ := by positivity
  obtain ⟨K1, hK1, hdy⟩ := dyadic_tail_sum (d := d) hγ
  have hγ2 : 2 * σ / 2 = σ := by ring
  have hθb : s - d + 1 < b := lt_of_le_of_lt (le_max_left _ _) hb
  set Cw := (1 + 4 * Real.pi ^ 2 * 256) ^ σ with hCw
  have hCw0 : 0 ≤ Cw := by positivity
  refine ⟨Cw * Ch * K1, by positivity, fun f hf hFσ N => ?_⟩
  set F := coeffOf f with hFdef
  have hFθ : MemHs (s - d + 1) F := memHs_mono' (by linarith) hFσ
  have hdom : Summable fun j => sobWeight (s - d + 1) j * ‖F j‖ ^ 2 := hFθ
  have hdy' := hdy (fun j => sobWeight (s - d + 1) j * ‖F j‖ ^ 2)
    (fun j => mul_nonneg (sobWeight_posC _ j).le (sq_nonneg _)) hdom
    (by
      rw [hγ2]
      refine Summable.of_nonneg_of_le (fun j => mul_nonneg (sobWeight_posC _ j).le
        (mul_nonneg (sobWeight_posC _ j).le (sq_nonneg _))) (fun j => ?_) hFσ
      rw [← mul_assoc, ← sobWeight_add]
      exact mul_le_mul_of_nonneg_right (sobWeight_mono_exp (by linarith) j) (sq_nonneg _)) N
  rw [hγ2] at hdy'
  have hbound : ∑' j, sobWeight σ j * (sobWeight (s - d + 1) j * ‖F j‖ ^ 2) ≤ hsNormSq (σ + b) F := by
    refine Summable.tsum_le_tsum (fun j => ?_) ?_ hFσ
    · rw [← mul_assoc, ← sobWeight_add]
      exact mul_le_mul_of_nonneg_right (sobWeight_mono_exp (by linarith) j) (sq_nonneg _)
    · refine Summable.of_nonneg_of_le (fun j => mul_nonneg (sobWeight_posC _ j).le
        (mul_nonneg (sobWeight_posC _ j).le (sq_nonneg _))) (fun j => ?_) hFσ
      rw [← mul_assoc, ← sobWeight_add]
      exact mul_le_mul_of_nonneg_right (sobWeight_mono_exp (by linarith) j) (sq_nonneg _)
  calc ∑ m ∈ Finset.range N, Cw * ((2 : ℝ) ^ m) ^ (2 * σ) *
        ∑' k, ‖mulCoeff F (fun j => gradRieszCoeff d s i F j - forceLow d s i m F j) k‖ ^ 2
      ≤ ∑ m ∈ Finset.range N, Cw * ((2 : ℝ) ^ m) ^ (2 * σ) *
          (Torus.supNorm f ^ 2 * (Ch * ∑' j, (if (2 : ℝ) ^ m ≤ Lattice.enorm j then
            sobWeight (s - d + 1) j * ‖F j‖ ^ 2 else 0))) := by
        refine Finset.sum_le_sum fun m _ => ?_
        refine mul_le_mul_of_nonneg_left ?_ (by positivity)
        obtain ⟨-, h2⟩ := hCh f hf hFθ m
        rw [hsNormSq_zero] at h2
        exact h2
    _ = Cw * Ch * Torus.supNorm f ^ 2 * ∑ m ∈ Finset.range N, ((2 : ℝ) ^ m) ^ (2 * σ) *
          ∑' j, (if (2 : ℝ) ^ m ≤ Lattice.enorm j then
            sobWeight (s - d + 1) j * ‖F j‖ ^ 2 else 0) := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun m _ => ?_
        ring
    _ ≤ Cw * Ch * Torus.supNorm f ^ 2 *
          (K1 * ∑' j, sobWeight σ j * (sobWeight (s - d + 1) j * ‖F j‖ ^ 2)) :=
        mul_le_mul_of_nonneg_left hdy' (by positivity)
    _ ≤ Cw * Ch * Torus.supNorm f ^ 2 * (K1 * hsNormSq (σ + b) F) := by
        gcongr
    _ = Cw * Ch * K1 * Torus.supNorm f ^ 2 * hsNormSq (σ + b) F := by ring

/-! ### The paraproduct estimate -/

theorem memHs_of_finite_sum_le {G : Coeff d} {m B : ℝ}
    (h : ∀ S : Finset (Lattice d), ∑ k ∈ S, sobWeight m k * ‖G k‖ ^ 2 ≤ B) :
    MemHs m G ∧ hsNormSq m G ≤ B := by
  have hs : MemHs m G :=
    summable_of_sum_le (fun k => mul_nonneg (sobWeight_posC _ k).le (sq_nonneg _)) h
  exact ⟨hs, hs.tsum_le_of_sum_le h⟩

theorem paraproduct_sq_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (σ b : ℝ)
    (hσ : 0 ≤ σ) (hb : max (s - d + 1) 0 < b) (i : Fin d) :
    ∃ Q : ℝ, 0 ≤ Q ∧ ∀ f : Torus d → ℝ, Continuous f → MemHs (σ + b) (coeffOf f) →
      MemHs σ (mulCoeff (coeffOf f) (gradRieszCoeff d s i (coeffOf f))) ∧
      hsNormSq σ (mulCoeff (coeffOf f) (gradRieszCoeff d s i (coeffOf f))) ≤
        Q * Torus.supNorm f ^ 2 * hsNormSq (σ + b) (coeffOf f) := by
  classical
  obtain ⟨Cs, hCs0, hCs⟩ := grad_l2_bound (d := d) s i
  have hb0 : 0 < b := lt_of_le_of_lt (le_max_right _ _) hb
  have hθb : s - d + 1 < b := lt_of_le_of_lt (le_max_left _ _) hb
  -- common facts about `f`
  have common : ∀ f : Torus d → ℝ, Continuous f → MemHs (σ + b) (coeffOf f) →
      MemHs 0 (coeffOf f) ∧ MemHs 0 (gradRieszCoeff d s i (coeffOf f)) ∧
      MemHs 0 (mulCoeff (coeffOf f) (gradRieszCoeff d s i (coeffOf f))) ∧
      hsNormSq 0 (mulCoeff (coeffOf f) (gradRieszCoeff d s i (coeffOf f))) ≤
        Cs * Torus.supNorm f ^ 2 * hsNormSq (σ + b) (coeffOf f) := by
    intro f hf hFσ
    have hF0 : MemHs 0 (coeffOf f) := memHs_mono' (by linarith) hFσ
    obtain ⟨hu, hnu⟩ := hCs (σ + b) (by linarith) (coeffOf f) hFσ
    obtain ⟨hG, hGn⟩ := mulCoeff_l2_bound hf hu
    refine ⟨hF0, hu, hG, hGn.trans ?_⟩
    calc Torus.supNorm f ^ 2 * hsNormSq 0 (gradRieszCoeff d s i (coeffOf f))
        ≤ Torus.supNorm f ^ 2 * (Cs * hsNormSq (σ + b) (coeffOf f)) :=
          mul_le_mul_of_nonneg_left hnu (sq_nonneg _)
      _ = _ := by ring
  rcases hσ.eq_or_lt with h0 | hpos
  · -- σ = 0: no decomposition needed
    subst h0
    refine ⟨Cs, hCs0, fun f hf hFσ => ?_⟩
    obtain ⟨-, -, hG, hGn⟩ := common f hf hFσ
    refine ⟨hG, ?_⟩
    exact hGn
  · -- σ > 0
    obtain ⟨Kl, hKl0, hKl⟩ := sum_low_bound hd s hs0 hsd b hb i hpos
    obtain ⟨Kh, hKh0, hKh⟩ := sum_high_bound hd s hs0 hsd b hb i hpos
    obtain ⟨Cl, hCl0, hCl⟩ := low_piece_bound hd s hs0 hsd b hb i
    obtain ⟨Ch, hCh0, hCh⟩ := high_piece_bound hd s hs0 hsd i
    set Wcr := (1 + 4 * Real.pi ^ 2 * 64) ^ σ with hWcr
    have hWcr0 : 0 ≤ Wcr := by positivity
    refine ⟨Wcr * Cs + 2 * Kl + 2 * Kh, by positivity, fun f hf hFσ => ?_⟩
    obtain ⟨hF0, hu, hG, hGn⟩ := common f hf hFσ
    set F := coeffOf f with hFdef
    set G := mulCoeff F (gradRieszCoeff d s i F) with hGdef
    have hFθ : MemHs (s - d + 1) F := memHs_mono' (by linarith) hFσ
    set Pl : ℕ → Coeff d := fun m => mulCoeff (forceLow d s i m F) (tailCoeff m F) with hPl
    set Ph : ℕ → Coeff d := fun m => mulCoeff F (fun j => gradRieszCoeff d s i F j -
      forceLow d s i m F j) with hPh
    have hPlS : ∀ m, Summable fun k => ‖Pl m k‖ ^ 2 := fun m =>
      (memHs_zero_iff _).1 (hCl f hf hF0 m).1
    have hPhS : ∀ m, Summable fun k => ‖Ph m k‖ ^ 2 := fun m =>
      (memHs_zero_iff _).1 (hCh f hf hFθ m).1
    apply memHs_of_finite_sum_le
    intro S
    set M := S.sup shellIdx with hMdef
    have hM : ∀ k ∈ S, 8 ≤ Lattice.enorm k → shellIdx k ≤ M := fun k hk _ =>
      Finset.le_sup (f := shellIdx) hk
    have hpt : ∀ k ∈ S, sobWeight σ k * ‖G k‖ ^ 2 ≤
        (if Lattice.enorm k < 8 then Wcr * ‖G k‖ ^ 2 else 0) +
        2 * (if 8 ≤ Lattice.enorm k then sobWeight σ k * ‖Pl (shellIdx k) k‖ ^ 2 else 0) +
        2 * (if 8 ≤ Lattice.enorm k then sobWeight σ k * ‖Ph (shellIdx k) k‖ ^ 2 else 0) := by
      intro k _
      have hw0 := (sobWeight_posC (d := d) σ k).le
      by_cases hk : Lattice.enorm k < 8
      · have hk' : ¬ 8 ≤ Lattice.enorm k := not_le.2 hk
        simp only [hk, hk', ite_true, ite_false, mul_zero, add_zero]
        exact mul_le_mul_of_nonneg_right (sobWeight_le_crude hpos.le hk) (sq_nonneg _)
      · have hk8 : 8 ≤ Lattice.enorm k := not_lt.1 hk
        simp only [hk, hk8, ite_true, ite_false, zero_add]
        have hsplit : G k = Pl (shellIdx k) k + Ph (shellIdx k) k :=
          mulCoeff_split_shell s i (shellIdx k) hF0 hu (shellIdx_spec hk8).1
        rw [hsplit]
        have hn := norm_add_le (Pl (shellIdx k) k) (Ph (shellIdx k) k)
        have hsq : ‖Pl (shellIdx k) k + Ph (shellIdx k) k‖ ^ 2 ≤
            2 * ‖Pl (shellIdx k) k‖ ^ 2 + 2 * ‖Ph (shellIdx k) k‖ ^ 2 := by
          nlinarith [norm_nonneg (Pl (shellIdx k) k), norm_nonneg (Ph (shellIdx k) k),
            norm_nonneg (Pl (shellIdx k) k + Ph (shellIdx k) k),
            sq_nonneg (‖Pl (shellIdx k) k‖ - ‖Ph (shellIdx k) k‖)]
        calc sobWeight σ k * ‖Pl (shellIdx k) k + Ph (shellIdx k) k‖ ^ 2
            ≤ sobWeight σ k * (2 * ‖Pl (shellIdx k) k‖ ^ 2 + 2 * ‖Ph (shellIdx k) k‖ ^ 2) :=
              mul_le_mul_of_nonneg_left hsq hw0
          _ = _ := by ring
    have hA : ∑ k ∈ S, (if Lattice.enorm k < 8 then Wcr * ‖G k‖ ^ 2 else 0) ≤
        Wcr * (Cs * Torus.supNorm f ^ 2 * hsNormSq (σ + b) F) := by
      calc ∑ k ∈ S, (if Lattice.enorm k < 8 then Wcr * ‖G k‖ ^ 2 else 0)
          ≤ ∑ k ∈ S, Wcr * ‖G k‖ ^ 2 :=
            Finset.sum_le_sum fun k _ => by
              split_ifs
              · exact le_rfl
              · positivity
        _ = Wcr * ∑ k ∈ S, ‖G k‖ ^ 2 := by rw [Finset.mul_sum]
        _ ≤ Wcr * ∑' k, ‖G k‖ ^ 2 :=
            mul_le_mul_of_nonneg_left (((memHs_zero_iff G).1 hG).sum_le_tsum _
              (fun k _ => sq_nonneg _)) hWcr0
        _ ≤ _ := by
            refine mul_le_mul_of_nonneg_left ?_ hWcr0
            rw [← hsNormSq_zero]
            exact hGn
    have hB := (fine_shell_sum Pl hPlS hpos.le S M hM).trans (hKl f hf hFσ (M + 1))
    have hC := (fine_shell_sum Ph hPhS hpos.le S M hM).trans (hKh f hf hFσ (M + 1))
    calc ∑ k ∈ S, sobWeight σ k * ‖G k‖ ^ 2
        ≤ ∑ k ∈ S, ((if Lattice.enorm k < 8 then Wcr * ‖G k‖ ^ 2 else 0) +
          2 * (if 8 ≤ Lattice.enorm k then sobWeight σ k * ‖Pl (shellIdx k) k‖ ^ 2 else 0) +
          2 * (if 8 ≤ Lattice.enorm k then sobWeight σ k * ‖Ph (shellIdx k) k‖ ^ 2 else 0)) :=
          Finset.sum_le_sum hpt
      _ = ∑ k ∈ S, (if Lattice.enorm k < 8 then Wcr * ‖G k‖ ^ 2 else 0) +
          2 * ∑ k ∈ S, (if 8 ≤ Lattice.enorm k then sobWeight σ k * ‖Pl (shellIdx k) k‖ ^ 2 else 0) +
          2 * ∑ k ∈ S, (if 8 ≤ Lattice.enorm k then sobWeight σ k * ‖Ph (shellIdx k) k‖ ^ 2 else 0) := by
          rw [Finset.sum_add_distrib, Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]
      _ ≤ Wcr * (Cs * Torus.supNorm f ^ 2 * hsNormSq (σ + b) F) +
          2 * (Kl * Torus.supNorm f ^ 2 * hsNormSq (σ + b) F) +
          2 * (Kh * Torus.supNorm f ^ 2 * hsNormSq (σ + b) F) := by
          gcongr
      _ = _ := by ring

set_option linter.unusedVariables false in
theorem exists_paraproduct_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (σ b : ℝ)
    (hσ : 0 ≤ σ) (hb : max (s - d + 1) 0 < b) (hb1 : b ≤ 1) (i : Fin d) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Continuous f → MemHs (σ + b) (coeffOf f) →
      MemHs σ (mulCoeff (coeffOf f) (gradRieszCoeff d s i (coeffOf f))) ∧
      hsNorm σ (mulCoeff (coeffOf f) (gradRieszCoeff d s i (coeffOf f))) ≤
        C * Torus.supNorm f * hsNorm (σ + b) (coeffOf f) := by
  obtain ⟨Q, hQ0, hQ⟩ := paraproduct_sq_bound hd s hs0 hsd σ b hσ hb i
  refine ⟨Real.sqrt Q, Real.sqrt_nonneg _, fun f hf hFσ => ?_⟩
  obtain ⟨hG, hGn⟩ := hQ f hf hFσ
  refine ⟨hG, ?_⟩
  unfold hsNorm
  calc Real.sqrt (hsNormSq σ (mulCoeff (coeffOf f) (gradRieszCoeff d s i (coeffOf f))))
      ≤ Real.sqrt (Q * Torus.supNorm f ^ 2 * hsNormSq (σ + b) (coeffOf f)) :=
        Real.sqrt_le_sqrt hGn
    _ = Real.sqrt Q * Torus.supNorm f * Real.sqrt (hsNormSq (σ + b) (coeffOf f)) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hQ0, Real.sqrt_sq (supNorm_nonneg f)]

/-! ### The loss of derivatives of the nonlinearity -/

theorem hsNormSq_derivCoeff_le (m : ℝ) (i : Fin d) {c : Coeff d} (hc : MemHs m c) :
    MemHs (m - 1) (derivCoeff i c) ∧ hsNormSq (m - 1) (derivCoeff i c) ≤ hsNormSq m c := by
  have hpt : ∀ k, sobWeight (m - 1) k * ‖derivCoeff i c k‖ ^ 2 ≤ sobWeight m k * ‖c k‖ ^ 2 := by
    intro k
    rw [norm_derivCoeff_sq]
    have h1 : (2 * Real.pi * (k i : ℝ)) ^ 2 ≤ sobWeight 1 k := by
      have := abs_le_enorm k i
      have h2 : (k i : ℝ) ^ 2 ≤ Lattice.enorm k ^ 2 := by
        rw [← sq_abs]; exact pow_le_pow_left₀ (abs_nonneg _) this 2
      unfold sobWeight
      rw [Real.rpow_one]
      nlinarith [sq_nonneg Real.pi]
    have h3 : sobWeight m k = sobWeight (m - 1) k * sobWeight 1 k := by
      rw [← sobWeight_add]; congr 1; ring
    rw [h3]
    have := sobWeight_posC (d := d) (m - 1) k
    calc sobWeight (m - 1) k * ((2 * Real.pi * (k i : ℝ)) ^ 2 * ‖c k‖ ^ 2)
        = sobWeight (m - 1) k * (2 * Real.pi * (k i : ℝ)) ^ 2 * ‖c k‖ ^ 2 := by ring
      _ ≤ sobWeight (m - 1) k * sobWeight 1 k * ‖c k‖ ^ 2 := by gcongr
  have hs : MemHs (m - 1) (derivCoeff i c) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_posC _ k).le (sq_nonneg _)) hpt hc
  exact ⟨hs, Summable.tsum_le_tsum hpt hs hc⟩

theorem hsNormSq_add_le {m : ℝ} {a c : Coeff d} (ha : MemHs m a) (hc : MemHs m c) :
    MemHs m (fun k => a k + c k) ∧
      hsNormSq m (fun k => a k + c k) ≤ 2 * (hsNormSq m a + hsNormSq m c) := by
  have hpt : ∀ k, sobWeight m k * ‖a k + c k‖ ^ 2 ≤
      2 * (sobWeight m k * ‖a k‖ ^ 2) + 2 * (sobWeight m k * ‖c k‖ ^ 2) := by
    intro k
    have hw := (sobWeight_posC (d := d) m k).le
    have hn := norm_add_le (a k) (c k)
    have hsq : ‖a k + c k‖ ^ 2 ≤ 2 * ‖a k‖ ^ 2 + 2 * ‖c k‖ ^ 2 := by
      nlinarith [norm_nonneg (a k), norm_nonneg (c k), norm_nonneg (a k + c k),
        sq_nonneg (‖a k‖ - ‖c k‖)]
    nlinarith [mul_le_mul_of_nonneg_left hsq hw]
  have hs : MemHs m (fun k => a k + c k) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_posC _ k).le (sq_nonneg _)) hpt
      ((ha.mul_left 2).add (hc.mul_left 2))
  refine ⟨hs, ?_⟩
  calc hsNormSq m (fun k => a k + c k)
      ≤ ∑' k, (2 * (sobWeight m k * ‖a k‖ ^ 2) + 2 * (sobWeight m k * ‖c k‖ ^ 2)) :=
        Summable.tsum_le_tsum hpt hs ((ha.mul_left 2).add (hc.mul_left 2))
    _ = 2 * (hsNormSq m a + hsNormSq m c) := by
        rw [Summable.tsum_add (ha.mul_left 2) (hc.mul_left 2), tsum_mul_left, tsum_mul_left]
        unfold hsNormSq; ring

theorem hsNormSq_sum_le {m : ℝ} (a : Fin d → Coeff d) (ha : ∀ i, MemHs m (a i)) :
    MemHs m (fun k => ∑ i, a i k) ∧
      hsNormSq m (fun k => ∑ i, a i k) ≤ (d : ℝ) * ∑ i, hsNormSq m (a i) := by
  have hpt : ∀ k, sobWeight m k * ‖∑ i, a i k‖ ^ 2 ≤
      (d : ℝ) * ∑ i, sobWeight m k * ‖a i k‖ ^ 2 := by
    intro k
    have hw := (sobWeight_posC (d := d) m k).le
    have h1 : ‖∑ i, a i k‖ ≤ ∑ i, ‖a i k‖ := norm_sum_le _ _
    have h2 : (∑ i, ‖a i k‖) ^ 2 ≤ (d : ℝ) * ∑ i, ‖a i k‖ ^ 2 := by
      have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
        (f := fun i => ‖a i k‖)
      simpa using this
    have h3 : ‖∑ i, a i k‖ ^ 2 ≤ (d : ℝ) * ∑ i, ‖a i k‖ ^ 2 :=
      (pow_le_pow_left₀ (norm_nonneg _) h1 2).trans h2
    calc sobWeight m k * ‖∑ i, a i k‖ ^ 2 ≤ sobWeight m k * ((d : ℝ) * ∑ i, ‖a i k‖ ^ 2) :=
          mul_le_mul_of_nonneg_left h3 hw
      _ = _ := by rw [Finset.mul_sum, Finset.mul_sum, Finset.mul_sum]; refine Finset.sum_congr rfl fun i _ => ?_; ring
  have hsum : Summable fun k => ∑ i, sobWeight m k * ‖a i k‖ ^ 2 := summable_sum fun i _ => ha i
  have hs : MemHs m (fun k => ∑ i, a i k) :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_posC _ k).le (sq_nonneg _)) hpt
      (hsum.mul_left _)
  refine ⟨hs, ?_⟩
  calc hsNormSq m (fun k => ∑ i, a i k)
      ≤ ∑' k, (d : ℝ) * ∑ i, sobWeight m k * ‖a i k‖ ^ 2 :=
        Summable.tsum_le_tsum hpt hs (hsum.mul_left _)
    _ = (d : ℝ) * ∑ i, hsNormSq m (a i) := by
        rw [tsum_mul_left, Summable.tsum_finsetSum fun i _ => ha i]
        rfl

set_option linter.unusedVariables false in
theorem exists_nonlinear_loss_bound (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (b : ℝ)
    (hb : max (s - d + 1) 0 < b) (hb1 : b ≤ 1) (j : ℝ) (hj : 1 ≤ j) (V : Torus d → ℝ)
    (hV : Torus.IsCk (⌈j⌉₊ + 1 : ℕ) V) (ν : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Torus d → ℝ, Continuous f → MemHs j (coeffOf f) →
      MemHs (j - (1 + b)) (mfRhsCoeff d s V ν (coeffOf f) - (ν : ℂ) • laplaceCoeff (coeffOf f)) ∧
      hsNorm (j - (1 + b)) (mfRhsCoeff d s V ν (coeffOf f) - (ν : ℂ) • laplaceCoeff (coeffOf f)) ≤
        C * (Torus.supNorm f + 1) * hsNorm j (coeffOf f) := by
  have hb0 : 0 < b := lt_of_le_of_lt (le_max_right _ _) hb
  have hθb : s - d + 1 < b := lt_of_le_of_lt (le_max_left _ _) hb
  set σ' := j - b with hσ'
  have hσ'0 : 0 ≤ σ' := by linarith
  have hσ'j : σ' + b = j := by rw [hσ']; ring
  choose Qg hQg0 hQg using fun i : Fin d => paraproduct_sq_bound hd s hs0 hsd σ' b hσ'0 hb i
  obtain ⟨C0, hC00, hC0⟩ := ProdAux.prodBound_all hd ⌈σ'⌉₊ σ' hσ'0
    (by have := Nat.le_ceil σ'; linarith)
  -- the smooth multipliers `∂_i V`
  set dV : Fin d → Torus d → ℝ := fun i => Torus.partialDeriv i V with hdV
  have hdVj : ∀ i, Torus.IsCk (⌈j⌉₊ : ℕ) (dV i) := fun i => ProdAux.isCk_partialDeriv hV i
  have hceil : ⌈σ'⌉₊ ≤ ⌈j⌉₊ := Nat.ceil_mono (by linarith)
  have hdVσ : ∀ i, Torus.IsCk (⌈σ'⌉₊ : ℕ) (dV i) := fun i =>
    (hdVj i).of_le (by exact_mod_cast hceil)
  have hj1 : 1 ≤ ⌈j⌉₊ := by
    have := Nat.le_ceil j
    exact_mod_cast (by linarith : (1 : ℝ) ≤ ⌈j⌉₊)
  have hdV1 : ∀ i, Torus.IsCk 1 (dV i) := fun i => (hdVj i).of_le (by exact_mod_cast hj1)
  have hV1 : Torus.IsCk 1 V := hV.of_le (by exact_mod_cast Nat.le_add_left 1 _)
  have hdVc : ∀ i, derivCoeff i (coeffOf V) = coeffOf (dV i) := fun i =>
    (coeffOf_partialDeriv_eq i V hV1).symm
  have hV0 : ∀ i, MemHs 0 (derivCoeff i (coeffOf V)) := fun i => by
    rw [hdVc]; exact (coeffOf_memHs_zero (continuous_of_isCk (hdV1 i))).1
  set cb : Fin d → ℝ := fun i => Torus.cbNorm ⌈σ'⌉₊ (dV i) with hcb
  refine ⟨Real.sqrt (2 * d * (∑ i, Qg i + ∑ i, C0 * cb i ^ 2)),
    Real.sqrt_nonneg _, fun f hf hF => ?_⟩
  set F := coeffOf f with hFdef
  have hFσ' : MemHs σ' F := memHs_mono' (by linarith) hF
  have hF0 : MemHs 0 F := memHs_mono' (by linarith) hF
  have hFσb : MemHs (σ' + b) F := by rw [hσ'j]; exact hF
  have hg0 : ∀ i, MemHs 0 (gradRieszCoeff d s i F) := fun i => by
    obtain ⟨Cs, -, hCs⟩ := grad_l2_bound (d := d) s i
    exact (hCs j (by linarith) F hF).1
  set Vt : Fin d → Coeff d := fun i => mulCoeff (coeffOf (dV i)) F with hVt
  set Gt : Fin d → Coeff d := fun i => mulCoeff F (gradRieszCoeff d s i F) with hGt
  have hGtb : ∀ i, MemHs σ' (Gt i) ∧ hsNormSq σ' (Gt i) ≤
      Qg i * Torus.supNorm f ^ 2 * hsNormSq (σ' + b) F := fun i => hQg i f hf hFσb
  have hVtb : ∀ i, MemHs σ' (Vt i) ∧ hsNormSq σ' (Vt i) ≤ C0 * cb i ^ 2 * hsNormSq σ' F :=
    fun i => hC0 (dV i) (hdVσ i) F hFσ'
  have hR : mfRhsCoeff d s V ν F - (ν : ℂ) • laplaceCoeff F =
      fun k => ∑ i, (derivCoeff i (Vt i) k + derivCoeff i (Gt i) k) := by
    funext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mfRhsCoeff]
    rw [add_sub_cancel_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : mulCoeff F (fun k' => derivCoeff i (coeffOf V) k' + gradRieszCoeff d s i F k') =
        fun k' => Vt i k' + Gt i k' := by
      funext k'
      rw [mulCoeff_add_right hF0 (hV0 i) (hg0 i) k', hdVc, hVt, hGt]
      simp only [mulCoeff_comm F (coeffOf (dV i)) k']
    rw [h1]
    simp only [derivCoeff]
    ring
  have hRidx : j - (1 + b) = σ' - 1 := by rw [hσ']; ring
  rw [hR, hRidx]
  -- the two sums
  have hDV : ∀ i, MemHs (σ' - 1) (derivCoeff i (Vt i)) ∧
      hsNormSq (σ' - 1) (derivCoeff i (Vt i)) ≤ hsNormSq σ' (Vt i) :=
    fun i => hsNormSq_derivCoeff_le σ' i (hVtb i).1
  have hDG : ∀ i, MemHs (σ' - 1) (derivCoeff i (Gt i)) ∧
      hsNormSq (σ' - 1) (derivCoeff i (Gt i)) ≤ hsNormSq σ' (Gt i) :=
    fun i => hsNormSq_derivCoeff_le σ' i (hGtb i).1
  obtain ⟨hSV, hSVn⟩ := hsNormSq_sum_le (m := σ' - 1) (fun i => derivCoeff i (Vt i))
    (fun i => (hDV i).1)
  obtain ⟨hSG, hSGn⟩ := hsNormSq_sum_le (m := σ' - 1) (fun i => derivCoeff i (Gt i))
    (fun i => (hDG i).1)
  have hsplit : (fun k => ∑ i, (derivCoeff i (Vt i) k + derivCoeff i (Gt i) k)) =
      fun k => (∑ i, derivCoeff i (Vt i) k) + ∑ i, derivCoeff i (Gt i) k := by
    funext k; rw [Finset.sum_add_distrib]
  rw [hsplit]
  obtain ⟨hT, hTn⟩ := hsNormSq_add_le hSV hSG
  refine ⟨hT, ?_⟩
  set X := hsNormSq j F with hX
  have hX0 : 0 ≤ X := hsNormSq_nonneg _ _
  have hXσ : hsNormSq σ' F ≤ X := hsNormSq_mono' (by linarith) hF
  have hsup0 := supNorm_nonneg f
  have hVsum : ∑ i, hsNormSq (σ' - 1) (derivCoeff i (Vt i)) ≤ (∑ i, C0 * cb i ^ 2) * X := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (hDV i).2.trans ((hVtb i).2.trans ?_)
    exact mul_le_mul_of_nonneg_left hXσ (by positivity)
  have hGsum : ∑ i, hsNormSq (σ' - 1) (derivCoeff i (Gt i)) ≤
      (∑ i, Qg i) * Torus.supNorm f ^ 2 * X := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (hDG i).2.trans ((hGtb i).2.trans ?_)
    rw [hσ'j]
  have hQsum : 0 ≤ ∑ i, Qg i := Finset.sum_nonneg fun i _ => hQg0 i
  have hCsum : 0 ≤ ∑ i, C0 * cb i ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  set Q := 2 * (d : ℝ) * (∑ i, Qg i + ∑ i, C0 * cb i ^ 2) with hQ
  have hQ0 : 0 ≤ Q := by positivity
  have hfin : hsNormSq (σ' - 1) (fun k => (∑ i, derivCoeff i (Vt i) k) + ∑ i, derivCoeff i (Gt i) k) ≤
      Q * (Torus.supNorm f + 1) ^ 2 * X := by
    refine hTn.trans ?_
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h1 : hsNormSq (σ' - 1) (fun k => ∑ i, derivCoeff i (Vt i) k) ≤
        d * ((∑ i, C0 * cb i ^ 2) * X) :=
      hSVn.trans (mul_le_mul_of_nonneg_left hVsum hd0)
    have h2 : hsNormSq (σ' - 1) (fun k => ∑ i, derivCoeff i (Gt i) k) ≤
        d * ((∑ i, Qg i) * Torus.supNorm f ^ 2 * X) :=
      hSGn.trans (mul_le_mul_of_nonneg_left hGsum hd0)
    have h3 : (∑ i, C0 * cb i ^ 2) * X ≤ (∑ i, C0 * cb i ^ 2) * (Torus.supNorm f + 1) ^ 2 * X := by
      have : (1 : ℝ) ≤ (Torus.supNorm f + 1) ^ 2 := by nlinarith
      calc (∑ i, C0 * cb i ^ 2) * X = (∑ i, C0 * cb i ^ 2) * 1 * X := by ring
        _ ≤ _ := by gcongr
    have h4 : (∑ i, Qg i) * Torus.supNorm f ^ 2 * X ≤ (∑ i, Qg i) * (Torus.supNorm f + 1) ^ 2 * X := by
      have : Torus.supNorm f ^ 2 ≤ (Torus.supNorm f + 1) ^ 2 := by nlinarith
      gcongr
    calc 2 * (hsNormSq (σ' - 1) (fun k => ∑ i, derivCoeff i (Vt i) k) +
          hsNormSq (σ' - 1) (fun k => ∑ i, derivCoeff i (Gt i) k))
        ≤ 2 * (d * ((∑ i, C0 * cb i ^ 2) * (Torus.supNorm f + 1) ^ 2 * X) +
            d * ((∑ i, Qg i) * (Torus.supNorm f + 1) ^ 2 * X)) := by
          gcongr
          · exact h1.trans (mul_le_mul_of_nonneg_left h3 hd0)
          · exact h2.trans (mul_le_mul_of_nonneg_left h4 hd0)
      _ = _ := by rw [hQ]; ring
  unfold hsNorm
  calc Real.sqrt (hsNormSq (σ' - 1) (fun k => (∑ i, derivCoeff i (Vt i) k) + ∑ i, derivCoeff i (Gt i) k))
      ≤ Real.sqrt (Q * (Torus.supNorm f + 1) ^ 2 * X) := Real.sqrt_le_sqrt hfin
    _ = Real.sqrt Q * (Torus.supNorm f + 1) * Real.sqrt X := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hQ0, Real.sqrt_sq (by linarith)]

end HRS.PDE.MFApriori
