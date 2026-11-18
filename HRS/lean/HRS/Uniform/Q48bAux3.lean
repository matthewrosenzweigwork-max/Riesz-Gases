import HRS.Uniform.Q48bAux2

/-!
# Q48b, part 3: finite trigonometric test functions

For a finite set `T` of nonzero frequencies and real coefficients `c`, the test function
`φ_{T,c} = ∑_{l∈T} c_l e_l` is smooth, has zero mean, real Fourier coefficients `c` on `T`, and
`‖P_{ρβ} φ_{T,c}‖_{H^a} ≤ K_a (∑_{l∈T} ⟨l⟩^{2a} c_l²)^{1/2}` for `2a > d` (`P_{ρβ}` the `ρβ`-mean projection).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q48b

open HRS HRS.PDE

variable {d : ℕ}

/-- The weight `⟨l⟩`. -/
def q48bW (l : NonzeroLattice d) : ℝ := Lattice.jp l.1

theorem q48bW_pos (l : NonzeroLattice d) : 0 < q48bW l := Torus.jp_pos l.1

open Classical in
theorem q48b_isSmooth_realMode (k : NonzeroLattice d) : Torus.IsSmooth (Torus.realMode k) := by
  unfold Torus.IsSmooth Torus.IsCk
  have hdot : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (fun y : Euc d => Lattice.dot k.1 y) := by
    unfold Lattice.dot
    refine ContDiff.sum fun i _ => contDiff_const.mul ?_
    exact (EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).contDiff
  have hlift : Torus.lift (Torus.realMode k) = fun y : Euc d =>
      if Lattice.IsPosHalf k.1 then Real.sqrt 2 * Real.cos (2 * Real.pi * Lattice.dot k.1 y)
      else Real.sqrt 2 * Real.sin (2 * Real.pi * Lattice.dot k.1 y) := by
    funext y
    unfold Torus.lift Torus.realMode
    simp only [Function.comp, Torus.cosMode_mk, Torus.sinMode_mk]
  rw [hlift]
  split_ifs
  · exact contDiff_const.mul (Real.contDiff_cos.comp (contDiff_const.mul hdot))
  · exact contDiff_const.mul (Real.contDiff_sin.comp (contDiff_const.mul hdot))

/-- The finite trigonometric test function `∑_{l∈T} c_l e_l`. -/
def q48bTest (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) : Torus d → ℝ :=
  fun x => ∑ l ∈ T, c l * Torus.realMode l x

theorem q48bTest_smooth (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) :
    Torus.IsSmooth (q48bTest T c) := by
  unfold Torus.IsSmooth Torus.IsCk
  have : Torus.lift (q48bTest T c) = fun y => ∑ l ∈ T, c l * Torus.lift (Torus.realMode l) y := rfl
  rw [this]
  exact ContDiff.sum fun l _ => contDiff_const.mul (q48b_isSmooth_realMode l)

theorem q48bTest_continuous (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) :
    Continuous (q48bTest T c) :=
  q48b_continuous_of_isSmooth (q48bTest_smooth T c)

theorem q48b_integrable_cont {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

theorem q48bTest_coeff (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ)
    (k : NonzeroLattice d) :
    Torus.funRealCoeff (q48bTest T c) k = if k ∈ T then c k else 0 := by
  classical
  unfold Torus.funRealCoeff q48bTest
  have hint : ∀ l ∈ T, Integrable (fun x => Torus.realMode k x * (c l * Torus.realMode l x)) := by
    intro l _
    exact q48b_integrable_cont ((Torus.continuous_realMode k).mul
      (continuous_const.mul (Torus.continuous_realMode l)))
  have e : ∀ x, Torus.realMode k x * ∑ l ∈ T, c l * Torus.realMode l x =
      ∑ l ∈ T, c l * (Torus.realMode k x * Torus.realMode l x) := by
    intro x
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun l _ => by ring
  simp_rw [e]
  rw [integral_finset_sum _ (fun l hl => by
    have := hint l hl
    simpa [mul_left_comm] using this)]
  have e2 : ∀ l, ∫ x, c l * (Torus.realMode k x * Torus.realMode l x) =
      if k = l then c l else 0 := by
    intro l
    rw [integral_const_mul, Torus.realMode_orthonormal]
    split_ifs <;> simp
  simp_rw [e2]
  by_cases hk : k ∈ T
  · rw [if_pos hk]
    rw [Finset.sum_eq_single k]
    · simp
    · intro l _ hl; simp [Ne.symm hl]
    · intro h; exact absurd hk h
  · rw [if_neg hk]
    refine Finset.sum_eq_zero fun l hl => ?_
    have : k ≠ l := fun h => hk (h ▸ hl)
    simp [this]

theorem q48bTest_mean (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) :
    Torus.mean (q48bTest T c) = 0 := by
  unfold Torus.mean q48bTest
  rw [integral_finset_sum T (f := fun l x => c l * Torus.realMode l x) (fun l _ =>
    (q48b_integrable_cont (continuous_const.mul (Torus.continuous_realMode l)) :
      Integrable (fun x => c l * Torus.realMode l x)))]
  refine Finset.sum_eq_zero fun l _ => ?_
  rw [integral_const_mul, Torus.integral_realMode, mul_zero]

theorem q48bTest_memSobolev (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) (a : ℝ) :
    MemSobolev a (q48bTest T c) :=
  HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (q48bTest_smooth T c) a

/-- The Sobolev sum of a test function. -/
theorem q48bTest_tsum (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) (a : ℝ) :
    ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * a) * Torus.funRealCoeff (q48bTest T c) k ^ 2 =
      ∑ l ∈ T, q48bW l ^ (2 * a) * c l ^ 2 := by
  classical
  rw [tsum_eq_sum (s := T)]
  · refine Finset.sum_congr rfl fun l hl => ?_
    rw [q48bTest_coeff, if_pos hl]; rfl
  · intro k hk
    rw [q48bTest_coeff, if_neg hk]; simp

theorem q48bTest_sobolevNorm (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ) (a : ℝ) :
    sobolevNorm a (q48bTest T c) = Real.sqrt (∑ l ∈ T, q48bW l ^ (2 * a) * c l ^ 2) := by
  unfold sobolevNorm
  rw [q48bTest_mean, q48bTest_tsum]
  simp

/-- Shifting by a constant does not change the real Fourier coefficients. -/
theorem q48b_funRealCoeff_add_const {g : Torus d → ℝ} (hg : MemLp g 2 volume) (p : ℝ)
    (k : NonzeroLattice d) :
    Torus.funRealCoeff (fun x => g x + p) k = Torus.funRealCoeff g k := by
  unfold Torus.funRealCoeff
  have hr : MemLp (Torus.realMode k) 2 (volume : Measure (Torus d)) :=
    (Torus.continuous_realMode k).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have h1 : Integrable (fun x => Torus.realMode k x * g x) := hr.integrable_mul hg
  have h2 : Integrable (fun x => Torus.realMode k x * p) :=
    q48b_integrable_cont ((Torus.continuous_realMode k).mul continuous_const)
  have e : ∀ x, Torus.realMode k x * (g x + p) = Torus.realMode k x * g x + Torus.realMode k x * p :=
    fun x => by ring
  simp_rw [e]
  rw [integral_add h1 h2, integral_mul_const, Torus.integral_realMode]
  simp

theorem q48b_funRealCoeff_projMean {g : Torus d → ℝ} (μ : Measure (Torus d))
    (hg : MemLp (projMean μ g) 2 volume) (k : NonzeroLattice d) :
    Torus.funRealCoeff g k = Torus.funRealCoeff (projMean μ g) k := by
  have := q48b_funRealCoeff_add_const hg (pair μ g) k
  have e : (fun x => projMean μ g x + pair μ g) = g := by
    funext x; unfold projMean; ring
  rw [e] at this
  exact this

/-- Bound for the `ρβ`-mean projection of a test function. -/
theorem q48b_proj_test_bound (ρβ : Torus d → ℝ) (hρ : IsProbDensity ρβ) (a : ℝ) (ha : (d : ℝ) < 2 * a) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (T : Finset (NonzeroLattice d)) (c : NonzeroLattice d → ℝ),
      sobolevNorm a (projMean (withDensityReal ρβ) (q48bTest T c)) ≤
        K * Real.sqrt (∑ l ∈ T, q48bW l ^ (2 * a) * c l ^ 2) := by
  haveI : IsProbabilityMeasure (withDensityReal ρβ) := isProb_withDensityReal hρ
  set B : ℝ := ‖NegSobolev.ofMeasureDiff a (withDensityReal ρβ) (volume : Measure (Torus d))‖ with hB
  refine ⟨Real.sqrt (B ^ 2 + 1), Real.sqrt_nonneg _, fun T c => ?_⟩
  set φ := q48bTest T c with hφ
  set N : ℝ := Real.sqrt (∑ l ∈ T, q48bW l ^ (2 * a) * c l ^ 2) with hN
  have hNn : 0 ≤ N := Real.sqrt_nonneg _
  set p : ℝ := pair (withDensityReal ρβ) φ with hp
  have hpair0 : pair (volume : Measure (Torus d)) φ = 0 := by
    have := q48bTest_mean T c
    unfold Torus.mean at this
    exact this
  have hpB : |p| ≤ B * N := by
    have := abs_pair_sub_le a ha (withDensityReal ρβ) volume φ (q48bTest_memSobolev T c a)
      (q48bTest_continuous T c)
    rw [hpair0, sub_zero, ← hp] at this
    rwa [hφ, q48bTest_sobolevNorm] at this
  have hmean : Torus.mean (projMean (withDensityReal ρβ) φ) = -p := by
    unfold Torus.mean projMean
    rw [integral_sub (q48b_integrable_cont (q48bTest_continuous T c)) (integrable_const _)]
    have := q48bTest_mean T c
    unfold Torus.mean at this
    simp [this, hp]
  have hcoef : ∀ k, Torus.funRealCoeff (projMean (withDensityReal ρβ) φ) k = Torus.funRealCoeff φ k := by
    intro k
    have h := q48b_funRealCoeff_add_const (g := φ)
      ((q48bTest_continuous T c).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)) (-p) k
    unfold projMean
    simpa [sub_eq_add_neg] using h
  have hsq : sobolevNorm a (projMean (withDensityReal ρβ) φ) ^ 2 = p ^ 2 + N ^ 2 := by
    unfold sobolevNorm
    rw [Real.sq_sqrt, hmean]
    · have : ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * a) *
          Torus.funRealCoeff (projMean (withDensityReal ρβ) φ) k ^ 2 = N ^ 2 := by
        simp_rw [hcoef]
        rw [hφ, q48bTest_tsum, hN, Real.sq_sqrt]
        exact Finset.sum_nonneg fun l _ => mul_nonneg (Real.rpow_nonneg (q48bW_pos l).le _) (sq_nonneg _)
      rw [this]; ring
    · exact add_nonneg (sq_nonneg _) (tsum_nonneg fun k =>
        mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))
  have hle : sobolevNorm a (projMean (withDensityReal ρβ) φ) ^ 2 ≤
      (Real.sqrt (B ^ 2 + 1) * N) ^ 2 := by
    have h1 : Real.sqrt (B ^ 2 + 1) ^ 2 = B ^ 2 + 1 := Real.sq_sqrt (by positivity)
    rw [hsq, mul_pow, h1]
    have : p ^ 2 ≤ (B * N) ^ 2 := by
      rw [← sq_abs p]; exact pow_le_pow_left₀ (abs_nonneg _) hpB 2
    nlinarith [this]
  have hnn : 0 ≤ Real.sqrt (B ^ 2 + 1) * N := by positivity
  have hsn : 0 ≤ sobolevNorm a (projMean (withDensityReal ρβ) φ) := Real.sqrt_nonneg _
  exact le_of_sq_le_sq hle hnn |>.trans le_rfl

end HRS.Uniform.Q48b
