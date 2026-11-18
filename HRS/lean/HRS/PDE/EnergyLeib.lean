import HRS.PDE.EnergyMul

/-!
# Derivatives of coefficient sequences: Leibniz rule, norms, derivative functions
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-! ### Multi-index derivative multipliers -/

theorem multiDerivCoeff_apply (α : Fin d → ℕ) (c : Coeff d) (k : Lattice d) :
    multiDerivCoeff α c k = (∏ i, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ (α i)) * c k := rfl

theorem multiDerivCoeff_zero (c : Coeff d) : multiDerivCoeff 0 c = c := by
  funext k; simp [multiDerivCoeff_apply]

theorem multiDerivCoeff_add (α β : Fin d → ℕ) (c : Coeff d) :
    multiDerivCoeff (α + β) c = multiDerivCoeff α (multiDerivCoeff β c) := by
  funext k
  simp only [multiDerivCoeff_apply, Pi.add_apply, pow_add, Finset.prod_mul_distrib]
  ring

theorem derivCoeff_eq_multi (j : Fin d) (c : Coeff d) :
    derivCoeff j c = multiDerivCoeff (Pi.single j 1) c := by
  funext k
  simp only [derivCoeff, multiDerivCoeff_apply]
  congr 1
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hi; simp [hi]
  · simp

theorem isTrigPoly_multiDerivCoeff {n : ℕ} {c : Coeff d} (hc : IsTrigPoly n c) (α : Fin d → ℕ) :
    IsTrigPoly n (multiDerivCoeff α c) := fun k hk => by
  apply hc k
  intro h; apply hk; simp [multiDerivCoeff_apply, h]

theorem isTrigPoly_mono {n n' : ℕ} (h : n ≤ n') {c : Coeff d} (hc : IsTrigPoly n c) :
    IsTrigPoly n' c := fun k hk i => (hc k hk i).trans (by exact_mod_cast h)

theorem norm_symbol_factor (j : ℤ) :
    ‖(2 * Real.pi * Complex.I * (j : ℂ))‖ = |2 * Real.pi * (j : ℝ)| := by
  have : (2 * Real.pi * Complex.I * (j : ℂ)) = ((2 * Real.pi * (j : ℝ) : ℝ) : ℂ) * Complex.I := by
    push_cast; ring
  rw [this, norm_mul, Complex.norm_real, Complex.norm_I, mul_one, Real.norm_eq_abs]

theorem norm_sq_multiDerivCoeff (γ : Fin d → ℕ) (c : Coeff d) (k : Lattice d) :
    ‖multiDerivCoeff γ c k‖ ^ 2 = (∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * γ i)) * ‖c k‖ ^ 2 := by
  rw [multiDerivCoeff_apply, norm_mul, mul_pow, norm_prod, ← Finset.prod_pow]
  congr 1
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [norm_pow, ← pow_mul, mul_comm (γ i) 2, pow_mul, norm_symbol_factor, sq_abs, pow_mul]


/-! ### Leibniz rule at the coefficient level -/

/-- The multi-indices `β ≤ α`. -/
def leibnizSet (α : Fin d → ℕ) : Finset (Fin d → ℕ) :=
  Fintype.piFinset fun i => Finset.range (α i + 1)

theorem mem_leibnizSet {α β : Fin d → ℕ} : β ∈ leibnizSet α ↔ ∀ i, β i ≤ α i := by
  simp [leibnizSet, Fintype.mem_piFinset, Nat.lt_succ_iff]

/-- The multinomial binomial coefficient `∏ C(α_i, β_i)`. -/
def binomW (α β : Fin d → ℕ) : ℕ := ∏ i, Nat.choose (α i) (β i)

theorem prod_add_pow_expand (α : Fin d → ℕ) (x y : Fin d → ℂ) :
    ∏ i, (x i + y i) ^ (α i) =
      ∑ β ∈ leibnizSet α, (binomW α β : ℂ) * ((∏ i, x i ^ (β i)) * ∏ i, y i ^ (α i - β i)) := by
  have h1 : ∀ i, (x i + y i) ^ (α i) =
      ∑ m ∈ Finset.range (α i + 1), x i ^ m * y i ^ (α i - m) * (Nat.choose (α i) m : ℂ) :=
    fun i => add_pow _ _ _
  simp_rw [h1]
  rw [Finset.prod_univ_sum]
  refine Finset.sum_congr rfl fun β _ => ?_
  rw [Finset.prod_mul_distrib, Finset.prod_mul_distrib, binomW, Nat.cast_prod]
  ring

theorem multiDeriv_symbol_leibniz (α : Fin d → ℕ) (k l : Lattice d) :
    (∏ i, (2 * Real.pi * Complex.I * (k i : ℂ)) ^ (α i)) =
      ∑ β ∈ leibnizSet α, (binomW α β : ℂ) *
        ((∏ i, (2 * Real.pi * Complex.I * ((k - l) i : ℂ)) ^ (β i)) *
          ∏ i, (2 * Real.pi * Complex.I * (l i : ℂ)) ^ (α i - β i)) := by
  have := prod_add_pow_expand α (fun i => 2 * Real.pi * Complex.I * ((k - l) i : ℂ))
    (fun i => 2 * Real.pi * Complex.I * (l i : ℂ))
  rw [← this]
  refine Finset.prod_congr rfl fun i _ => ?_
  congr 1
  simp only [Pi.sub_apply]
  push_cast
  ring

/-- **Leibniz rule for convolutions**: for a trigonometric polynomial `c`,
`D_α(a * c) = ∑_{β ≤ α} binom(α,β) (D_β a) * (D_{α-β} c)`. -/
theorem multiDerivCoeff_mulCoeff {n : ℕ} (α : Fin d → ℕ) (a c : Coeff d) (hc : IsTrigPoly n c)
    (k : Lattice d) :
    multiDerivCoeff α (mulCoeff a c) k = ∑ β ∈ leibnizSet α, (binomW α β : ℂ) *
      mulCoeff (multiDerivCoeff β a) (multiDerivCoeff (α - β) c) k := by
  have hc' : ∀ γ, IsTrigPoly n (multiDerivCoeff γ c) := isTrigPoly_multiDerivCoeff hc
  simp_rw [mulCoeff_of_trig (hc' _)]
  rw [multiDerivCoeff_apply, mulCoeff_of_trig hc, Finset.mul_sum]
  simp_rw [Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [multiDeriv_symbol_leibniz α k l, Finset.sum_mul]
  refine Finset.sum_congr rfl fun β _ => ?_
  simp only [multiDerivCoeff_apply, Pi.sub_apply]
  ring

theorem multiDerivCoeff_comm_single (α : Fin d → ℕ) (j : Fin d) (c : Coeff d) :
    multiDerivCoeff α (derivCoeff j c) = multiDerivCoeff (α + Pi.single j 1) c := by
  rw [derivCoeff_eq_multi, ← multiDerivCoeff_add]

/-! ### Norm bounds for derivatives -/

theorem memHs_of_isTrigPolyE {n : ℕ} {c : Coeff d} (hc : IsTrigPoly n c) (r : ℝ) : MemHs r c :=
  summable_of_ne_finset_zero (s := boxFin d n) fun k hk => by
    rw [eq_zero_of_isTrigPoly hc hk]; simp

theorem hsNormSq_of_isTrigPoly {n : ℕ} {c : Coeff d} (hc : IsTrigPoly n c) (r : ℝ) :
    hsNormSq r c = ∑ k ∈ boxFin d n, sobWeight r k * ‖c k‖ ^ 2 :=
  tsum_eq_sum fun k hk => by rw [eq_zero_of_isTrigPoly hc hk]; simp

theorem hsNormSq_nonnegE (r : ℝ) (c : Coeff d) : 0 ≤ hsNormSq r c :=
  tsum_nonneg fun k => mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _)

/-- `∑_{k∈S} |D_γ c(k)|² ≤ ‖c‖²_{H^m}` for `|γ| ≤ m`. -/
theorem sum_sq_multiDeriv_le (γ : Fin d → ℕ) (m : ℕ) (hγ : ∑ i, γ i ≤ m) (c : Coeff d)
    (hc : MemHs (m : ℝ) c) (S : Finset (Lattice d)) :
    ∑ k ∈ S, ‖multiDerivCoeff γ c k‖ ^ 2 ≤ hsNormSq (m : ℝ) c := by
  calc ∑ k ∈ S, ‖multiDerivCoeff γ c k‖ ^ 2
      ≤ ∑ k ∈ S, sobWeight (m : ℝ) k * ‖c k‖ ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [norm_sq_multiDerivCoeff, sobWeight_natCast]
        exact mul_le_mul_of_nonneg_right ((weight_le_pow γ k).trans
          (pow_le_pow_right₀ (one_le_sobBaseE k) hγ)) (sq_nonneg _)
    _ ≤ hsNormSq (m : ℝ) c :=
        hc.sum_le_tsum S (fun k _ => mul_nonneg (sobWeight_nonnegE _ _) (sq_nonneg _))

/-! ### Derivative functions of a smooth function -/

theorem exists_dirs : ∀ (p : ℕ) (β : Fin d → ℕ), ∑ i, β i = p →
    ∃ m : Fin p → Euc d, (∀ s, ‖m s‖ ≤ 1) ∧
      ∀ k : Lattice d, ∏ s, Lattice.dot k (m s) = ∏ i, (k i : ℝ) ^ β i := by
  intro p
  induction p with
  | zero =>
    intro β hβ
    refine ⟨Fin.elim0, fun s => s.elim0, fun k => ?_⟩
    have : β = 0 := by
      funext i
      have := (Finset.sum_eq_zero_iff.mp hβ) i (Finset.mem_univ i)
      simpa using this
    subst this
    simp
  | succ p ih =>
    intro β hβ
    obtain ⟨i, hi⟩ : ∃ i, β i ≠ 0 := by
      by_contra h
      push Not at h
      simp [h] at hβ
    set β' : Fin d → ℕ := β - Pi.single i 1 with hβ'
    have hsplit : β = β' + Pi.single i 1 := by
      funext j
      by_cases hj : j = i
      · subst hj; simp [hβ']; omega
      · simp [hβ', hj]
    have hsum' : ∑ j, β' j = p := by
      have : ∑ j, β j = ∑ j, β' j + 1 := by
        conv_lhs => rw [hsplit]
        simp [Finset.sum_add_distrib]
      omega
    obtain ⟨m', hm'1, hm'2⟩ := ih β' hsum'
    refine ⟨Fin.cons (EuclideanSpace.single i 1) m', fun s => ?_, fun k => ?_⟩
    · refine Fin.cases ?_ (fun t => ?_) s
      · simp
      · simpa using hm'1 t
    · rw [Fin.prod_univ_succ]
      simp only [Fin.cons_zero, Fin.cons_succ]
      rw [hm'2 k]
      have hd : Lattice.dot k (EuclideanSpace.single i (1 : ℝ)) = (k i : ℝ) := by
        simp [Lattice.dot, PiLp.single_apply]
      rw [hd]
      conv_rhs => rw [hsplit]
      simp only [Pi.add_apply, pow_add, Finset.prod_mul_distrib]
      rw [mul_comm]
      congr 1
      rw [Finset.prod_eq_single i]
      · simp
      · intro j _ hj; simp [hj]
      · simp

theorem exists_derivFun (b : Torus d → ℝ) (K : ℕ) (hb : ContDiff ℝ (K : WithTop ℕ∞) (Torus.lift b))
    (β : Fin d → ℕ) (hβ : ∑ i, β i ≤ K) :
    ∃ φ : Torus d → ℝ, Continuous φ ∧ coeffOf φ = multiDerivCoeff β (coeffOf b) ∧
      ∀ x, |φ x| ≤ Torus.cbNorm K b := by
  obtain ⟨p, hp⟩ : ∃ p, ∑ i, β i = p := ⟨_, rfl⟩
  obtain ⟨m, hm1, hm2⟩ := exists_dirs p β hp
  rw [hp] at hβ
  set G : Euc d → ℝ := Torus.lift b with hG
  have hPer : Torus.Per G := fun y n => Torus.lift_periodic b y n
  refine ⟨Torus.descend (fun y => iteratedFDeriv ℝ p G y m), ?_, ?_, ?_⟩
  · exact Torus.continuous_descend (hPer.iteratedFDeriv_apply m)
      (Torus.continuous_iteratedFDeriv_apply hb hβ m)
  · funext k
    have h1 : coeffOf (Torus.descend (fun y => iteratedFDeriv ℝ p G y m)) k =
        Torus.fcoef (Torus.descend (fun y => iteratedFDeriv ℝ p G y m)) k := coeffOf_eq _ _
    have h2 : coeffOf b k = Torus.fcoef (Torus.descend G) k := by
      rw [hG, Torus.descend_lift]; exact coeffOf_eq _ _
    rw [h1, Torus.fcoef_iteratedFDeriv hPer hb k p hβ m, ← h2, multiDerivCoeff_apply, ← Complex.ofReal_prod, hm2 k]
    congr 1
    have : ((2 * Real.pi * Complex.I) ^ p : ℂ) = ∏ i, (2 * Real.pi * Complex.I) ^ (β i) := by
      rw [Finset.prod_pow_eq_pow_sum, hp]
    rw [this]
    push_cast
    rw [← Finset.prod_mul_distrib]
    refine Finset.prod_congr rfl fun i _ => ?_
    simp only [mul_pow]
  · intro x
    have hbdd := Torus.bddAbove_norm_iteratedFDeriv_lift p b (hb.of_le (by exact_mod_cast hβ))
    have h1 : |iteratedFDeriv ℝ p G (Torus.rep x) m| ≤ ‖iteratedFDeriv ℝ p G (Torus.rep x)‖ := by
      have := (iteratedFDeriv ℝ p G (Torus.rep x)).le_opNorm m
      have hprod : ∏ s, ‖m s‖ ≤ 1 := Finset.prod_le_one₀ (fun s _ => norm_nonneg _) fun s _ => hm1 s
      calc |iteratedFDeriv ℝ p G (Torus.rep x) m|
          = ‖iteratedFDeriv ℝ p G (Torus.rep x) m‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖iteratedFDeriv ℝ p G (Torus.rep x)‖ * ∏ s, ‖m s‖ := this
        _ ≤ ‖iteratedFDeriv ℝ p G (Torus.rep x)‖ * 1 := by gcongr
        _ = _ := mul_one _
    have h2 : ‖iteratedFDeriv ℝ p G (Torus.rep x)‖ ≤ ⨆ y : Euc d, ‖iteratedFDeriv ℝ p G y‖ :=
      le_ciSup hbdd (Torus.rep x)
    have h3 : (⨆ y : Euc d, ‖iteratedFDeriv ℝ p G y‖) ≤ Torus.cbNorm K b := by
      unfold Torus.cbNorm
      exact Finset.single_le_sum (f := fun j => ⨆ y : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift b) y‖)
        (fun j _ => Real.iSup_nonneg fun y => norm_nonneg _)
        (Finset.mem_range.mpr (Nat.lt_succ_of_le hβ))
    exact h1.trans (h2.trans h3)


/-! ### Cauchy–Schwarz and pairing bounds -/

theorem cs_bound {ι : Type*} (S : Finset ι) (u v : ι → ℂ) (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (hu : ∑ k ∈ S, ‖u k‖ ^ 2 ≤ a ^ 2) (hv : ∑ k ∈ S, ‖v k‖ ^ 2 ≤ b ^ 2) :
    ∑ k ∈ S, ‖u k‖ * ‖v k‖ ≤ a * b := by
  have h := Finset.sum_mul_sq_le_sq_mul_sq S (fun k => ‖u k‖) (fun k => ‖v k‖)
  have hnn : 0 ≤ ∑ k ∈ S, ‖u k‖ * ‖v k‖ := Finset.sum_nonneg fun _ _ => mul_nonneg (norm_nonneg _) (norm_nonneg _)
  have h2 : (∑ k ∈ S, ‖u k‖ * ‖v k‖) ^ 2 ≤ (a * b) ^ 2 := by
    calc (∑ k ∈ S, ‖u k‖ * ‖v k‖) ^ 2 ≤ (∑ k ∈ S, ‖u k‖ ^ 2) * ∑ k ∈ S, ‖v k‖ ^ 2 := h
      _ ≤ a ^ 2 * b ^ 2 := mul_le_mul hu hv (Finset.sum_nonneg fun _ _ => sq_nonneg _) (sq_nonneg _)
      _ = (a * b) ^ 2 := by ring
  exact (pow_le_pow_iff_left₀ hnn (mul_nonneg ha hb) two_ne_zero).mp h2

/-- `‖∑_k conj(w_k) (φ̂ * c)(k)‖ ≤ K a e` when `∑|w|² ≤ a²`, `∑|c|² ≤ e²`. -/
theorem pairing_bound (φ : Torus d → ℝ) (hφ : Continuous φ) (K : ℝ) (hK : ∀ x, |φ x| ≤ K)
    {n : ℕ} (c : Coeff d) (hc : IsTrigPoly n c) (S : Finset (Lattice d)) (w : Coeff d) (a e : ℝ)
    (ha : 0 ≤ a) (he : 0 ≤ e) (hw : ∑ k ∈ S, ‖w k‖ ^ 2 ≤ a ^ 2)
    (hce : ∑ k ∈ boxFin d n, ‖c k‖ ^ 2 ≤ e ^ 2) :
    ‖∑ k ∈ S, conj (w k) * mulCoeff (coeffOf φ) c k‖ ≤ K * (a * e) := by
  have hK0 : 0 ≤ K := (abs_nonneg _).trans (hK (Classical.arbitrary _))
  have h1 := l2_mul_le φ hφ K hK n c hc S
  have h2 : ∑ k ∈ S, ‖mulCoeff (coeffOf φ) c k‖ ^ 2 ≤ (K * e) ^ 2 := by
    refine h1.trans ?_
    rw [mul_pow]
    exact mul_le_mul_of_nonneg_left hce (sq_nonneg _)
  calc ‖∑ k ∈ S, conj (w k) * mulCoeff (coeffOf φ) c k‖
      ≤ ∑ k ∈ S, ‖conj (w k) * mulCoeff (coeffOf φ) c k‖ := norm_sum_le _ _
    _ = ∑ k ∈ S, ‖w k‖ * ‖mulCoeff (coeffOf φ) c k‖ := by
        refine Finset.sum_congr rfl fun k _ => ?_
        rw [norm_mul, RCLike.norm_conj]
    _ ≤ a * (K * e) := cs_bound S w (fun k => mulCoeff (coeffOf φ) c k) a (K * e) ha
          (mul_nonneg hK0 he) hw h2
    _ = K * (a * e) := by ring

theorem conj_coeffOf (b : Torus d → ℝ) (n : Lattice d) : conj (coeffOf b n) = coeffOf b (-n) := by
  rw [coeffOf_eq, coeffOf_eq, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, Complex.conj_ofReal]
  rw [← Torus.mode_neg, neg_neg]

/-- On a box, the `α`-weighted bilinear form is the pairing of the `α`-derivatives. -/
theorem bilinForm_weight_eq {n : ℕ} (α : Fin d → ℕ) (c F : Coeff d) (hF : IsTrigPoly n F) :
    bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)) c F =
      ∑ k ∈ boxFin d n, conj (multiDerivCoeff α F k) * multiDerivCoeff α c k := by
  unfold bilinForm
  rw [tsum_eq_sum (s := boxFin d n)]
  · refine Finset.sum_congr rfl fun k _ => ?_
    have hsq : ((∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i) : ℝ) : ℂ) =
        multiDerivCoeff α (fun _ => (1 : ℂ)) k * conj (multiDerivCoeff α (fun _ => (1 : ℂ)) k) := by
      rw [Complex.mul_conj']
      have := norm_sq_multiDerivCoeff α (fun _ => (1 : ℂ)) k
      simp only [norm_one, one_pow, mul_one] at this
      rw [← this]; push_cast; ring
    rw [hsq]
    simp only [multiDerivCoeff_apply, map_mul, mul_one]
    ring
  · intro k hk
    rw [eq_zero_of_isTrigPoly hF hk]; simp

/-- Symmetrisation (integration by parts at the coefficient level) for a real function `b`:
`2 Re ∑ conj(w) (b̂ * ∂_j w) = - Re ∑ conj(w) ((∂_j b)^ * w)`. -/
theorem re_top_term {n : ℕ} (b : Torus d → ℝ) (w : Coeff d) (hw : IsTrigPoly n w) (j : Fin d) :
    (∑ k ∈ boxFin d n, conj (w k) * mulCoeff (coeffOf b) (derivCoeff j w) k).re =
      -(1 / 2) * (∑ k ∈ boxFin d n, conj (w k) * mulCoeff (derivCoeff j (coeffOf b)) w k).re := by
  have hw' : IsTrigPoly n (derivCoeff j w) := by
    rw [derivCoeff_eq_multi]; exact isTrigPoly_multiDerivCoeff hw _
  set f : Lattice d → Lattice d → ℂ := fun k l =>
    conj (w k) * (coeffOf b (k - l) * ((2 * Real.pi * Complex.I * (l j : ℂ)) * w l)) with hf
  set g : Lattice d → Lattice d → ℂ := fun k l =>
    conj (w k) * (((2 * Real.pi * Complex.I * ((k - l) j : ℂ)) * coeffOf b (k - l)) * w l) with hg
  have hA : ∑ k ∈ boxFin d n, conj (w k) * mulCoeff (coeffOf b) (derivCoeff j w) k =
      ∑ k ∈ boxFin d n, ∑ l ∈ boxFin d n, f k l := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mulCoeff_of_trig hw', Finset.mul_sum]
    rfl
  have hB : ∑ k ∈ boxFin d n, conj (w k) * mulCoeff (derivCoeff j (coeffOf b)) w k =
      ∑ k ∈ boxFin d n, ∑ l ∈ boxFin d n, g k l := by
    refine Finset.sum_congr rfl fun k _ => ?_
    rw [mulCoeff_of_trig hw, Finset.mul_sum]
    rfl
  rw [hA, hB]
  have hconj : conj (∑ k ∈ boxFin d n, ∑ l ∈ boxFin d n, f k l) =
      ∑ k ∈ boxFin d n, ∑ l ∈ boxFin d n, (w l * ((coeffOf b (k - l) *
        (-(2 * Real.pi * Complex.I * (k j : ℂ)))) * conj (w k))) := by
    rw [map_sum]
    simp_rw [map_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun k _ => Finset.sum_congr rfl fun l _ => ?_
    simp only [hf, map_mul, Complex.conj_conj, conj_coeffOf, neg_sub, Complex.conj_I,
      Complex.conj_ofReal, map_neg, map_natCast, map_intCast, map_ofNat]
    ring
  have hsum : (∑ k ∈ boxFin d n, ∑ l ∈ boxFin d n, f k l) +
      conj (∑ k ∈ boxFin d n, ∑ l ∈ boxFin d n, f k l) +
      (∑ k ∈ boxFin d n, ∑ l ∈ boxFin d n, g k l) = 0 := by
    rw [hconj]
    simp only [← Finset.sum_add_distrib]
    refine Finset.sum_eq_zero fun k _ => Finset.sum_eq_zero fun l _ => ?_
    simp only [hf, hg, Pi.sub_apply]
    push_cast
    ring
  have hre := congrArg Complex.re hsum
  simp only [Complex.add_re, Complex.conj_re, Complex.zero_re] at hre
  linarith

end HRS.PDE
