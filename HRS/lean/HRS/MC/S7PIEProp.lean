import HRS.MC.S7PIEInterp
import HRS.MC.L2C0Aux2
import HRS.Main.A33Aux3

/-!
# Packet PI-E, part 2: the propagator matrix in the real trigonometric basis

For `AdjointData` at a level `J ≥ m_*` and horizon `T`, the matrix `pieT u t j k = ∫ e_j (U^{u,t} e_k)` of the adjoint
propagator in the real basis `e_k` of `L²_0` satisfies the finite-section bounds `pieFinBd` at every integer level
`1 ≤ n ≤ J` (from `adjoint_torus_classical` and linearity of the propagator on trigonometric polynomials).
-/

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.PIE

open HRS HRS.PDE HRS.A33

variable {d : ℕ}

/-- finite real trigonometric combination `∑_{k ∈ K} ξ_k e_k` -/
def pieComb (K : Finset (NonzeroLattice d)) (ξ : NonzeroLattice d → ℝ) : Torus d → ℝ :=
  fun x => ∑ k ∈ K, ξ k * Torus.realMode k x

/-- the matrix of the propagator `U^{u,t}` in the real basis -/
def pieT (D : DynData d) (μ : ℝ → Torus d → ℝ) (u t : ℝ) (j k : NonzeroLattice d) : ℝ :=
  Torus.funRealCoeff (propagator D μ u t (Torus.realMode k)) j

lemma pieComb_continuous (K : Finset (NonzeroLattice d)) (ξ : NonzeroLattice d → ℝ) :
    Continuous (pieComb K ξ) := by
  unfold pieComb
  exact continuous_finset_sum _ fun k _ => continuous_const.mul (Torus.continuous_realMode k)

lemma pieComb_coeff (K : Finset (NonzeroLattice d)) (ξ : NonzeroLattice d → ℝ) (j : NonzeroLattice d) :
    Torus.funRealCoeff (pieComb K ξ) j = if j ∈ K then ξ j else 0 := by
  classical
  unfold Torus.funRealCoeff pieComb
  have hint : ∀ k ∈ K, Integrable fun x : Torus d => Torus.realMode j x * (ξ k * Torus.realMode k x) :=
    fun k _ => ClassicalAux.integrable_of_continuous
      ((Torus.continuous_realMode j).mul (continuous_const.mul (Torus.continuous_realMode k)))
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum _ hint]
  have : ∀ k ∈ K, ∫ x : Torus d, Torus.realMode j x * (ξ k * Torus.realMode k x) =
      if j = k then ξ k else 0 := by
    intro k _
    have e : ∀ x : Torus d, Torus.realMode j x * (ξ k * Torus.realMode k x) =
        ξ k * (Torus.realMode j x * Torus.realMode k x) := fun x => by ring
    simp_rw [e]
    rw [integral_const_mul, Torus.realMode_orthonormal]
    split_ifs <;> simp
  rw [Finset.sum_congr rfl this]
  by_cases hj : j ∈ K
  · rw [if_pos hj, Finset.sum_eq_single j]
    · simp
    · intro k _ hk; rw [if_neg (Ne.symm hk)]
    · intro h; exact absurd hj h
  · rw [if_neg hj]
    exact Finset.sum_eq_zero fun k hk => by
      rw [if_neg]; rintro rfl; exact hj hk

lemma pieComb_mean (K : Finset (NonzeroLattice d)) (ξ : NonzeroLattice d → ℝ) :
    Torus.mean (pieComb K ξ) = 0 := by
  unfold Torus.mean pieComb
  have hint : ∀ k ∈ K, Integrable fun x : Torus d => ξ k * Torus.realMode k x := fun k _ =>
    ClassicalAux.integrable_of_continuous (continuous_const.mul (Torus.continuous_realMode k))
  rw [integral_finset_sum _ hint]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_const_mul, Torus.integral_realMode]; simp

lemma pieComb_memSobolev (K : Finset (NonzeroLattice d)) (ξ : NonzeroLattice d → ℝ) (σ : ℝ) :
    MemSobolev σ (pieComb K ξ) := by
  refine ⟨ClassicalAux.memLp_two_of_continuous (pieComb_continuous K ξ), ?_⟩
  refine summable_of_ne_finset_zero (s := K) fun j hj => ?_
  rw [pieComb_coeff, if_neg hj]; simp

lemma pieComb_sobolevNorm_sq (K : Finset (NonzeroLattice d)) (ξ : NonzeroLattice d → ℝ) (σ : ℝ) :
    sobolevNorm σ (pieComb K ξ) ^ 2 = ∑ k ∈ K, Lattice.jp k.1 ^ (2 * σ) * ξ k ^ 2 := by
  classical
  unfold sobolevNorm
  rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
      mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))), pieComb_mean]
  rw [tsum_eq_sum (s := K) (fun j hj => by rw [pieComb_coeff, if_neg hj]; simp)]
  simp only [zero_pow two_ne_zero, zero_add]
  exact Finset.sum_congr rfl fun k hk => by rw [pieComb_coeff, if_pos hk]

/-- the standing hypotheses: `AdjointData` at a level `J ≥ m_*` on the horizon `[0,T]` -/
def PIEHyp (J : ℕ) (D : DynData d) (μ : ℝ → Torus d → ℝ) (T : ℝ) : Prop :=
  1 ≤ d ∧ mStar d ≤ J ∧ ∃ (Rg : PDE.Regime) (MB Λ VB ν₀ : ℝ), AdjointData D.s J Rg MB Λ VB D ν₀ T μ

lemma pieDom_comb (J : ℕ) (K : Finset (NonzeroLattice d)) (ξ : NonzeroLattice d → ℝ) :
    Dom J (pieComb K ξ) := ⟨pieComb_continuous K ξ, pieComb_memSobolev K ξ _⟩

lemma pieComb_single (k : NonzeroLattice d) :
    Torus.realMode k = pieComb {k} (fun _ => 1) := by
  funext x; simp [pieComb]

lemma pieDom_realMode (J : ℕ) (k : NonzeroLattice d) : Dom J (Torus.realMode k) := by
  rw [pieComb_single]; exact pieDom_comb J _ _

/-- linearity of the propagator on trigonometric polynomials -/
lemma pie_prop_comb {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {u : ℝ} (hu : u ∈ Set.Icc 0 t) (K : Finset (NonzeroLattice d))
    (ξ : NonzeroLattice d → ℝ) :
    propagator D μ u t (pieComb K ξ) =
      fun x => ∑ k ∈ K, ξ k * propagator D μ u t (Torus.realMode k) x := by
  classical
  obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
  induction K using Finset.induction_on with
  | empty =>
    have : pieComb (∅ : Finset (NonzeroLattice d)) ξ = fun _ => (0 : ℝ) := by
      funext x; simp [pieComb]
    rw [this, prop_const hd D.s D.hs0 D.hsd J hJ Rg MB Λ VB D ν₀ T μ hA ht 0 hu]
    funext x; simp
  | insert a K ha ih =>
    have e : pieComb (insert a K) ξ =
        fun x => ξ a * Torus.realMode a x + 1 * pieComb K ξ x := by
      funext x; simp [pieComb, Finset.sum_insert ha]
    rw [e, prop_lin hd D.s D.hs0 D.hsd J hJ Rg MB Λ VB D ν₀ T μ hA ht (pieDom_realMode J a)
      (pieDom_comb J K ξ) (ξ a) 1 hu, ih]
    funext x; simp [Finset.sum_insert ha]

lemma pie_prop_continuous {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {u : ℝ} (hu : u ∈ Set.Icc 0 t) {φ : Torus d → ℝ} (hφ : Dom J φ) :
    Continuous (propagator D μ u t φ) := by
  obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
  exact (prop_facts hd D.s D.hs0 D.hsd J hJ Rg MB Λ VB D ν₀ T μ hA ht hφ hu).2

/-- the real coefficients of `U (∑ ξ_k e_k)` -/
lemma pie_coeff_comb {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    {t : ℝ} (ht : t ∈ Set.Ioc 0 T) {u : ℝ} (hu : u ∈ Set.Icc 0 t) (K : Finset (NonzeroLattice d))
    (ξ : NonzeroLattice d → ℝ) (j : NonzeroLattice d) :
    Torus.funRealCoeff (propagator D μ u t (pieComb K ξ)) j = ∑ k ∈ K, ξ k * pieT D μ u t j k := by
  classical
  rw [pie_prop_comb H ht hu K ξ]
  unfold Torus.funRealCoeff pieT
  have hint : ∀ k ∈ K, Integrable fun x : Torus d =>
      Torus.realMode j x * (ξ k * propagator D μ u t (Torus.realMode k) x) := fun k _ =>
    ClassicalAux.integrable_of_continuous ((Torus.continuous_realMode j).mul
      (continuous_const.mul (pie_prop_continuous H ht hu (pieDom_realMode J k))))
  simp_rw [Finset.mul_sum]
  rw [integral_finset_sum _ hint]
  refine Finset.sum_congr rfl fun k _ => ?_
  have e : ∀ x : Torus d, Torus.realMode j x * (ξ k * propagator D μ u t (Torus.realMode k) x) =
      ξ k * (Torus.realMode j x * propagator D μ u t (Torus.realMode k) x) := fun x => by ring
  simp_rw [e]
  rw [integral_const_mul]
  rfl

/-- integer-level bound for the propagator, uniform in `0 ≤ u ≤ t ≤ T` -/
lemma pie_level_bound {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (n : ℕ) (hn1 : 1 ≤ n) (hnJ : n ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc 0 T, ∀ u ∈ Set.Icc 0 t, ∀ φ : Torus d → ℝ, Dom J φ →
      MemSobolev (n : ℝ) (propagator D μ u t φ) ∧
        sobolevNorm (n : ℝ) (propagator D μ u t φ) ≤ C * sobolevNorm (n : ℝ) φ := by
  obtain ⟨hd, hJ, Rg, MB, Λ, VB, ν₀, hA⟩ := H
  obtain ⟨C0, Cs, hC0, hCs, hmain⟩ := adjoint_torus_classical hd D.s D.hs0 D.hsd J hJ Rg MB Λ VB
  set lam : ℝ := Rg.lambdaM (Cs n) ν₀ (thetaOrder d D.s) with hlam
  refine ⟨Real.exp (|lam| * T), (Real.exp_pos _).le, fun t ht u hu φ hφ => ?_⟩
  obtain ⟨-, -, hb, -⟩ := hmain D ν₀ T μ hA t ht φ hφ.1 hφ.2
  obtain ⟨h1, h2⟩ := hb n hn1 hnJ u hu
  refine ⟨h1, h2.trans ?_⟩
  refine mul_le_mul_of_nonneg_right (Real.exp_le_exp.2 ?_) ?_
  · calc lam * (t - u) ≤ |lam| * (t - u) := mul_le_mul_of_nonneg_right (le_abs_self _) (by linarith [hu.2])
      _ ≤ |lam| * T := mul_le_mul_of_nonneg_left (by linarith [hu.1, ht.2]) (abs_nonneg _)
  · unfold sobolevNorm; exact Real.sqrt_nonneg _

/-- finite-section bound of the propagator matrix at an integer level -/
lemma pie_finBd {J : ℕ} {D : DynData d} {μ : ℝ → Torus d → ℝ} {T : ℝ} (H : PIEHyp J D μ T)
    (n : ℕ) (hn1 : 1 ≤ n) (hnJ : n ≤ J) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ t ∈ Set.Ioc 0 T, ∀ u ∈ Set.Icc 0 t,
      pieFinBd (pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1) (pieT D μ u t) (n : ℝ)) C := by
  classical
  obtain ⟨C, hC, hbd⟩ := pie_level_bound H n hn1 hnJ
  refine ⟨C, hC, fun t ht u hu K J' x => ?_⟩
  set ξ : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (-(n : ℝ)) * x k with hξ
  obtain ⟨hmem, hnorm⟩ := hbd t ht u hu (pieComb K ξ) (pieDom_comb J K ξ)
  have hpos : ∀ k : NonzeroLattice d, 0 < Lattice.jp k.1 := fun k => Torus.jp_pos k.1
  -- the rows
  have hrow : ∀ j : NonzeroLattice d, ∑ k ∈ K, pieWmat (fun k : NonzeroLattice d => Lattice.jp k.1)
        (pieT D μ u t) (n : ℝ) j k * x k =
      Lattice.jp j.1 ^ (n : ℝ) * Torus.funRealCoeff (propagator D μ u t (pieComb K ξ)) j := by
    intro j
    rw [pie_coeff_comb H ht hu K ξ j, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    simp only [pieWmat, hξ]
    have : Lattice.jp k.1 ^ (n : ℝ) * Lattice.jp k.1 ^ (-(n : ℝ)) = 1 := by
      rw [← Real.rpow_add (hpos k)]; simp
    have e1 : Lattice.jp j.1 ^ (n : ℝ) * pieT D μ u t j k * Lattice.jp k.1 ^ (-(n : ℝ)) * x k =
        Lattice.jp j.1 ^ (n : ℝ) * (Lattice.jp k.1 ^ (-(n : ℝ)) * x k * pieT D μ u t j k) := by ring
    exact e1
  simp_rw [hrow]
  obtain ⟨-, hsum⟩ := hmem
  set c : NonzeroLattice d → ℝ := fun j => Torus.funRealCoeff (propagator D μ u t (pieComb K ξ)) j with hc
  have h1 : ∑ j ∈ J', (Lattice.jp j.1 ^ (n : ℝ) * c j) ^ 2 ≤
      ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (2 * (n : ℝ)) * c j ^ 2 := by
    refine (Finset.sum_le_sum fun j _ => le_of_eq ?_).trans
      (hsum.sum_le_tsum J' fun j _ => mul_nonneg (Real.rpow_nonneg (hpos j).le _) (sq_nonneg _))
    rw [mul_pow, Torus.jp_rpow_sq]
  have h2 : ∑' j : NonzeroLattice d, Lattice.jp j.1 ^ (2 * (n : ℝ)) * c j ^ 2 ≤
      sobolevNorm (n : ℝ) (propagator D μ u t (pieComb K ξ)) ^ 2 := by
    unfold sobolevNorm
    rw [Real.sq_sqrt (add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
      mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)))]
    linarith [sq_nonneg (Torus.mean (propagator D μ u t (pieComb K ξ)))]
  have h3 : sobolevNorm (n : ℝ) (propagator D μ u t (pieComb K ξ)) ^ 2 ≤
      C ^ 2 * ∑ k ∈ K, x k ^ 2 := by
    have hnn : 0 ≤ sobolevNorm (n : ℝ) (propagator D μ u t (pieComb K ξ)) := by
      unfold sobolevNorm; exact Real.sqrt_nonneg _
    calc _ ≤ (C * sobolevNorm (n : ℝ) (pieComb K ξ)) ^ 2 := pow_le_pow_left₀ hnn hnorm 2
      _ = C ^ 2 * ∑ k ∈ K, x k ^ 2 := by
          rw [mul_pow, pieComb_sobolevNorm_sq]
          congr 1
          refine Finset.sum_congr rfl fun k _ => ?_
          simp only [hξ]
          rw [mul_pow, Torus.jp_rpow_sq, ← mul_assoc, ← Real.rpow_add (hpos k)]
          simp
  exact h1.trans (h2.trans h3)

end HRS.MC.Sec7.PIE

end
