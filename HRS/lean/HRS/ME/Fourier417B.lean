import HRS.ME.Fourier417A

/-!
# Row 4.17, packet M5 (part B): proofs of `fourier_coeff_decay` and `fourier_coeff_regular`

Statements copied verbatim from `HRS/ME/Spec417Fourier.lean`.  Helper lemmas carry the prefix `fb`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.ME

variable {d : ℕ}

open HRS

/-! ### Helper lemmas on single real modes -/

theorem fb_funRealCoeff_mode (c : ℝ) (j k : NonzeroLattice d) :
    Torus.funRealCoeff (fun x => c * Torus.realMode j x) k = if k = j then c else 0 := by
  unfold Torus.funRealCoeff
  have h : ∀ x, Torus.realMode k x * (c * Torus.realMode j x) =
      c * (Torus.realMode k x * Torus.realMode j x) := fun x => by ring
  simp_rw [h]
  rw [integral_const_mul, Torus.realMode_orthonormal]
  split_ifs <;> simp

theorem fb_mean_mode (c : ℝ) (j : NonzeroLattice d) :
    Torus.mean (fun x => c * Torus.realMode j x) = 0 := by
  unfold Torus.mean
  rw [integral_const_mul, Torus.integral_realMode, mul_zero]

theorem fb_sobolev_mode (K c : ℝ) (hc : 0 ≤ c) (j : NonzeroLattice d) :
    sobolevNorm K (fun x => c * Torus.realMode j x) = c * Lattice.jp j.1 ^ K := by
  unfold sobolevNorm
  rw [fb_mean_mode]
  have hsum : ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * K) *
      Torus.funRealCoeff (fun x => c * Torus.realMode j x) k ^ 2 =
      c ^ 2 * Lattice.jp j.1 ^ (2 * K) := by
    rw [tsum_eq_single j]
    · rw [fb_funRealCoeff_mode, if_pos rfl]; ring
    · intro k hk
      rw [fb_funRealCoeff_mode, if_neg hk]; simp
  rw [hsum]
  rw [show (0 : ℝ) ^ 2 + c ^ 2 * Lattice.jp j.1 ^ (2 * K) = (c * Lattice.jp j.1 ^ K) ^ 2 by
    rw [mul_pow, Torus.jp_rpow_sq]; ring]
  exact Real.sqrt_sq (mul_nonneg hc (Real.rpow_nonneg (Torus.jp_pos _).le _))

theorem fb_memSobolev_mode (K c : ℝ) (j : NonzeroLattice d) :
    MemSobolev K (fun x => c * Torus.realMode j x) := by
  refine ⟨?_, ?_⟩
  · exact ((continuous_const.mul (Torus.continuous_realMode j))).memLp_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · apply summable_of_ne_finset_zero (s := {j})
    intro k hk
    rw [fb_funRealCoeff_mode, if_neg (by simpa using hk)]
    simp

/-- `sqrt (a² + X) ≤ |a| + sqrt X`. -/
theorem fb_sqrt_add_sq_le (a X : ℝ) (hX : 0 ≤ X) :
    Real.sqrt (a ^ 2 + X) ≤ |a| + Real.sqrt X := by
  have h1 : a ^ 2 + X ≤ (|a| + Real.sqrt X) ^ 2 := by
    have := Real.sq_sqrt hX
    nlinarith [sq_abs a, abs_nonneg a, Real.sqrt_nonneg X]
  calc Real.sqrt (a ^ 2 + X) ≤ Real.sqrt ((|a| + Real.sqrt X) ^ 2) := Real.sqrt_le_sqrt h1
    _ = _ := Real.sqrt_sq (by positivity)

/-- Subtracting a constant from a continuous mean-zero function. -/
theorem fb_sobolev_sub_const (K : ℝ) {f : Torus d → ℝ} (hf : Continuous f) (hm : Torus.mean f = 0)
    (a : ℝ) : sobolevNorm K (fun x => f x - a) ≤ |a| + sobolevNorm K f := by
  have hfi : Integrable f := hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hmean : Torus.mean (fun x => f x - a) = -a := by
    unfold Torus.mean
    rw [integral_sub hfi (integrable_const a)]
    have : ∫ _x : Torus d, a = a := by simp
    unfold Torus.mean at hm
    rw [this, hm]; ring
  have hcoef : ∀ k : NonzeroLattice d, Torus.funRealCoeff (fun x => f x - a) k =
      Torus.funRealCoeff f k := by
    intro k
    unfold Torus.funRealCoeff
    have h : ∀ x, Torus.realMode k x * (f x - a) = Torus.realMode k x * f x - a * Torus.realMode k x :=
      fun x => by ring
    simp_rw [h]
    have hi1 : Integrable (fun x => Torus.realMode k x * f x) :=
      ((Torus.continuous_realMode k).mul hf).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    have hi2 : Integrable (fun x => a * Torus.realMode k x) :=
      ((Torus.continuous_realMode k).const_mul a).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    rw [integral_sub hi1 (by simpa [mul_comm] using hi2), integral_const_mul]
    simp [Torus.integral_realMode]
  have hX : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (2 * K) * Torus.funRealCoeff f k ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  unfold sobolevNorm
  simp_rw [hcoef, hmean, hm]
  simpa using fb_sqrt_add_sq_le a _ hX

/-- Bound on the projection modulo constants of a single scaled mode, for a probability density. -/
theorem fb_projMean_mode (ρ : Torus d → ℝ) (hprob : IsProbDensity ρ) (hρc : Continuous ρ)
    (K c : ℝ) (hc : 0 ≤ c) (j : NonzeroLattice d) :
    sobolevNorm K (projMean (withDensityReal ρ) (fun x => c * Torus.realMode j x)) ≤
      c * (Real.sqrt 2 + Lattice.jp j.1 ^ K) := by
  set φ : Torus d → ℝ := fun x => c * Torus.realMode j x with hφdef
  have hφc : Continuous φ := continuous_const.mul (Torus.continuous_realMode j)
  have hpair : |pair (withDensityReal ρ) φ| ≤ c * Real.sqrt 2 := by
    rw [PDE.MFSemigroup.pair_withDensityReal hprob φ]
    have hρi : Integrable ρ := hρc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have hg : Integrable (fun y => (c * Real.sqrt 2) * ρ y) :=
      hρi.const_mul _
    have hbound : ∫ y, (c * Real.sqrt 2) * ρ y = c * Real.sqrt 2 := by
      rw [integral_const_mul, hprob.integral_one, mul_one]
    calc |∫ y, ρ y * φ y| = ‖∫ y, ρ y * φ y‖ := (Real.norm_eq_abs _).symm
      _ ≤ ∫ y, (c * Real.sqrt 2) * ρ y := by
          apply norm_integral_le_of_norm_le hg
          refine Filter.Eventually.of_forall fun y => ?_
          rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hprob.nonneg y), hφdef]
          have h1 : |c * Torus.realMode j y| ≤ c * Real.sqrt 2 := by
            rw [abs_mul, abs_of_nonneg hc]
            exact mul_le_mul_of_nonneg_left (Torus.abs_realMode_le j y) hc
          calc ρ y * |c * Torus.realMode j y| ≤ ρ y * (c * Real.sqrt 2) :=
                mul_le_mul_of_nonneg_left h1 (hprob.nonneg y)
            _ = (c * Real.sqrt 2) * ρ y := by ring
      _ = c * Real.sqrt 2 := hbound
  have hφm : Torus.mean φ = 0 := fb_mean_mode c j
  unfold projMean
  have h1 := fb_sobolev_sub_const K hφc hφm (pair (withDensityReal ρ) φ)
  have h2 := fb_sobolev_mode K c hc j
  rw [← hφdef] at h2
  calc sobolevNorm K (fun x => φ x - pair (withDensityReal ρ) φ)
      ≤ |pair (withDensityReal ρ) φ| + sobolevNorm K φ := h1
    _ ≤ c * Real.sqrt 2 + c * Lattice.jp j.1 ^ K := by rw [h2]; linarith
    _ = c * (Real.sqrt 2 + Lattice.jp j.1 ^ K) := by ring

/-- The weighted `ℓ¹` sum of real coefficients is controlled by the Sobolev norm of index `n`. -/
theorem fb_coeff_sum (p n : ℕ) (hn : (d : ℝ) / 2 + p < n) {h : Torus d → ℝ} (hint : Integrable h)
    (hm : MemSobolev (n : ℝ) h) :
    Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ p * |Torus.funRealCoeff h l|) ∧
    ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ p * |Torus.funRealCoeff h l| ≤
      (Real.sqrt 2 * (1 + Real.sqrt (∑' k : NonzeroLattice d,
        Lattice.jp k.1 ^ (-(2 * ((n : ℝ) - (p : ℝ))))))) * sobolevNorm (n : ℝ) h := by
  obtain ⟨hsum, hbd⟩ := Torus.sobolev_coeff_bound hn hint hm.2
  have hle : ∀ l : NonzeroLattice d, Lattice.jp l.1 ^ p * |Torus.funRealCoeff h l| ≤
      Real.sqrt 2 * (Lattice.jp l.1 ^ p * ‖Torus.fcoef h l.1‖) := fun l => by
    have h1 := Torus.abs_funRealCoeff_le hint l
    have hp : 0 ≤ Lattice.jp l.1 ^ p := pow_nonneg (Torus.jp_pos _).le p
    calc Lattice.jp l.1 ^ p * |Torus.funRealCoeff h l|
        ≤ Lattice.jp l.1 ^ p * (Real.sqrt 2 * ‖Torus.fcoef h l.1‖) := mul_le_mul_of_nonneg_left h1 hp
      _ = _ := by ring
  have hsubS : Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ p * ‖Torus.fcoef h l.1‖) :=
    hsum.comp_injective Subtype.val_injective
  have hS2 : Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ p * |Torus.funRealCoeff h l|) :=
    Summable.of_nonneg_of_le (fun l => mul_nonneg (pow_nonneg (Torus.jp_pos _).le p) (abs_nonneg _))
      hle (hsubS.mul_left _)
  refine ⟨hS2, ?_⟩
  have hcmp : ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ p * ‖Torus.fcoef h l.1‖ ≤
      ∑' k : Lattice d, Lattice.jp k ^ p * ‖Torus.fcoef h k‖ :=
    tsum_comp_le_tsum_of_inj hsum (fun k => mul_nonneg (pow_nonneg (Torus.jp_pos _).le p)
      (norm_nonneg _)) Subtype.val_injective
  set S := sobolevNorm (n : ℝ) h with hSdef
  set T := ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * (n : ℝ)) * Torus.funRealCoeff h l ^ 2 with hTdef
  set A1 := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * ((n : ℝ) - (p : ℝ)))) with hA1
  have hT0 : 0 ≤ T := tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  have hmean : |Torus.mean h| ≤ S := by
    rw [hSdef]; unfold sobolevNorm
    exact Real.abs_le_sqrt (by linarith [hT0])
  have hsqrtT : Real.sqrt T ≤ S := by
    rw [hSdef]; unfold sobolevNorm
    exact Real.sqrt_le_sqrt (by linarith [sq_nonneg (Torus.mean h)])
  have hmain : ∑' k : Lattice d, Lattice.jp k ^ p * ‖Torus.fcoef h k‖ ≤ S + Real.sqrt A1 * S :=
    hbd.trans (add_le_add hmean (mul_le_mul_of_nonneg_left hsqrtT (Real.sqrt_nonneg _)))
  have hT : ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ p * |Torus.funRealCoeff h l| ≤
      Real.sqrt 2 * ∑' k : Lattice d, Lattice.jp k ^ p * ‖Torus.fcoef h k‖ := by
    calc ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ p * |Torus.funRealCoeff h l|
        ≤ ∑' l : NonzeroLattice d, Real.sqrt 2 * (Lattice.jp l.1 ^ p * ‖Torus.fcoef h l.1‖) :=
          Summable.tsum_le_tsum hle hS2 (hsubS.mul_left _)
      _ = Real.sqrt 2 * ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ p * ‖Torus.fcoef h l.1‖ := by
          rw [tsum_mul_left]
      _ ≤ Real.sqrt 2 * ∑' k : Lattice d, Lattice.jp k ^ p * ‖Torus.fcoef h k‖ :=
          mul_le_mul_of_nonneg_left hcmp (Real.sqrt_nonneg _)
  calc _ ≤ Real.sqrt 2 * ∑' k : Lattice d, Lattice.jp k ^ p * ‖Torus.fcoef h k‖ := hT
    _ ≤ Real.sqrt 2 * (S + Real.sqrt A1 * S) := mul_le_mul_of_nonneg_left hmain (Real.sqrt_nonneg _)
    _ = _ := by ring

/-- Cauchy-Schwarz for the weighted coefficient sums of `H^0` and `H^{2N}` functions. -/
theorem fb_tsum_cs (N : ℝ) (hN : 0 ≤ N) {h : Torus d → ℝ} (h0 : MemSobolev 0 h)
    (h2 : MemSobolev (2 * N) h) :
    (∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * N) * Torus.funRealCoeff h l ^ 2) ^ 2 ≤
      (∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * (0 : ℝ)) * Torus.funRealCoeff h l ^ 2) *
        (∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * (2 * N)) * Torus.funRealCoeff h l ^ 2) := by
  have hX0 : 0 ≤ ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * (0 : ℝ)) * Torus.funRealCoeff h l ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  have hX2 : 0 ≤ ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * (2 * N)) * Torus.funRealCoeff h l ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  have hXs : 0 ≤ ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * N) * Torus.funRealCoeff h l ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  have hf0 : ∀ l : NonzeroLattice d, 0 ≤ |Torus.funRealCoeff h l| := fun l => abs_nonneg _
  have hg0 : ∀ l : NonzeroLattice d, 0 ≤ Lattice.jp l.1 ^ (2 * N) * |Torus.funRealCoeff h l| :=
    fun l => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (abs_nonneg _)
  have hfs : Summable (fun l : NonzeroLattice d => |Torus.funRealCoeff h l| ^ (2 : ℝ)) := by
    refine h0.2.congr fun l => ?_
    rw [Real.rpow_two, sq_abs, mul_zero, Real.rpow_zero, one_mul]
  have hgs : Summable (fun l : NonzeroLattice d =>
      (Lattice.jp l.1 ^ (2 * N) * |Torus.funRealCoeff h l|) ^ (2 : ℝ)) := by
    refine h2.2.congr fun l => ?_
    rw [Real.rpow_two, mul_pow, sq_abs, Torus.jp_rpow_sq]
  have key := Real.inner_le_Lp_mul_Lq_tsum_of_nonneg Real.HolderConjugate.two_two hf0 hg0 hfs hgs
  have hL : ∑' l : NonzeroLattice d, |Torus.funRealCoeff h l| *
      (Lattice.jp l.1 ^ (2 * N) * |Torus.funRealCoeff h l|) =
      ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * N) * Torus.funRealCoeff h l ^ 2 :=
    tsum_congr fun l => by rw [← sq_abs (Torus.funRealCoeff h l)]; ring
  have hF : ∑' l : NonzeroLattice d, |Torus.funRealCoeff h l| ^ (2 : ℝ) =
      ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * (0 : ℝ)) * Torus.funRealCoeff h l ^ 2 :=
    tsum_congr fun l => by rw [Real.rpow_two, sq_abs, mul_zero, Real.rpow_zero, one_mul]
  have hG : ∑' l : NonzeroLattice d, (Lattice.jp l.1 ^ (2 * N) * |Torus.funRealCoeff h l|) ^ (2 : ℝ) =
      ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * (2 * N)) * Torus.funRealCoeff h l ^ 2 :=
    tsum_congr fun l => by rw [Real.rpow_two, mul_pow, sq_abs, Torus.jp_rpow_sq]
  rw [hL, hF, hG, ← Real.sqrt_eq_rpow, ← Real.sqrt_eq_rpow] at key
  have hsq := key
  set X0 := ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * (0 : ℝ)) * Torus.funRealCoeff h l ^ 2
  set X2 := ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * (2 * N)) * Torus.funRealCoeff h l ^ 2
  set Xs := ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * N) * Torus.funRealCoeff h l ^ 2
  calc Xs ^ 2 ≤ (Real.sqrt X0 * Real.sqrt X2) ^ 2 := pow_le_pow_left₀ hXs hsq 2
    _ = X0 * X2 := by rw [mul_pow, Real.sq_sqrt hX0, Real.sq_sqrt hX2]

/-- Sobolev interpolation at the midpoint: `‖h‖_N² ≤ ‖h‖_0 ‖h‖_{2N}`. -/
theorem fb_interp (N : ℝ) (hN : 0 ≤ N) {h : Torus d → ℝ} (h0 : MemSobolev 0 h)
    (h2 : MemSobolev (2 * N) h) :
    sobolevNorm N h ^ 2 ≤ sobolevNorm 0 h * sobolevNorm (2 * N) h := by
  have hcs := fb_tsum_cs N hN h0 h2
  have hX0 : 0 ≤ ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * (0 : ℝ)) * Torus.funRealCoeff h l ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  have hX2 : 0 ≤ ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * (2 * N)) * Torus.funRealCoeff h l ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  have hXs : 0 ≤ ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * N) * Torus.funRealCoeff h l ^ 2 :=
    tsum_nonneg fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _)
  set M := Torus.mean h
  set X0 := ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * (0 : ℝ)) * Torus.funRealCoeff h l ^ 2
  set X2 := ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * (2 * N)) * Torus.funRealCoeff h l ^ 2
  set Xs := ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ (2 * N) * Torus.funRealCoeff h l ^ 2
  have e0 : sobolevNorm 0 h = Real.sqrt (M ^ 2 + X0) := rfl
  have e2 : sobolevNorm (2 * N) h = Real.sqrt (M ^ 2 + X2) := rfl
  have eN : sobolevNorm N h = Real.sqrt (M ^ 2 + Xs) := rfl
  have hMX : 0 ≤ M ^ 2 + Xs := by positivity
  have hX2le : 2 * Xs ≤ X0 + X2 := by
    nlinarith [sq_nonneg (X0 - X2), sq_nonneg (2 * Xs - X0 - X2)]
  have hkey : (M ^ 2 + Xs) ^ 2 ≤ (M ^ 2 + X0) * (M ^ 2 + X2) := by
    nlinarith [mul_nonneg (sq_nonneg M) (sub_nonneg.mpr hX2le), hcs]
  rw [e0, e2, eN, ← Real.sqrt_mul (by positivity)]
  calc Real.sqrt (M ^ 2 + Xs) ^ 2 = M ^ 2 + Xs := Real.sq_sqrt hMX
    _ = Real.sqrt ((M ^ 2 + Xs) ^ 2) := (Real.sqrt_sq hMX).symm
    _ ≤ Real.sqrt ((M ^ 2 + X0) * (M ^ 2 + X2)) := Real.sqrt_le_sqrt hkey

/-- The generator maps smooth functions into `H^n` (the coefficient-level argument of
`equilibriumGen_sobolev_bound_proof`, truncated before the norm bound). -/
theorem fb_gen_memSobolev (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (n : ℕ) (f : Torus d → ℝ) (hf : Torus.IsSmooth f) :
    MemSobolev (n : ℝ) (PDE.equilibriumGen d s ρβ β⁻¹ f) := by
  obtain ⟨D, hD⟩ : ∃ D : DynData d, D = PDE.mfData d s hs0 hsd V β hβ := ⟨_, rfl⟩
  have hDs : D.s = s := by rw [hD]; rfl
  have hDM : D.M = -1 := by rw [hD]; rfl
  have hDV : D.V = V := by rw [hD]; rfl
  have hDinv : D.invβ = β⁻¹ := by rw [hD]; rfl
  have hK : PDE.ClassicalAux.ConvKernelFacts d D.s := PDE.ClassicalAux.convKernelFacts hd D
  have hV1 : Torus.IsCk 1 V := PDE.ClassicalAux.isCk_of_le (by norm_num) hV
  have hV2 : Torus.IsCk 2 V := PDE.ClassicalAux.isCk_of_le (by norm_num) hV
  have hρ1 : Torus.IsCk 1 ρβ := PDE.ClassicalAux.isCk_of_le (by norm_num) hρS
  have hρ2 : Torus.IsCk 2 ρβ := PDE.ClassicalAux.isCk_of_le (by norm_num) hρS
  have hρC : Continuous ρβ := Torus.continuous_of_continuous_lift (ContDiff.continuous hρ1)
  have hprob : IsProbDensity ρβ := hρβ.1
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hρC.continuousOn
  obtain ⟨M, hMdef⟩ : ∃ M : ℝ, M = ρβ x0 := ⟨_, rfl⟩
  have hM : ∀ x, ρβ x ≤ M := fun x => by
    rw [hMdef]; exact isMaxOn_iff.mp hx0 x (Set.mem_univ x)
  have hM0 : 0 ≤ M := by rw [hMdef]; exact (hpos x0).le
  -- loss bound at index `n + 2`, with a fixed auxiliary regularity index `r`
  have hiN : (1 : ℝ) ≤ (n : ℝ) + 2 := by
    have := (Nat.cast_nonneg n : (0 : ℝ) ≤ n); linarith
  obtain ⟨Cl, hCl, hloss⟩ := PDE.MFAdjoint.exists_forwardGen_loss hd s hs0 hsd ((n : ℝ) + 2)
    ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) hiN (by linarith)
  have hρH : PDE.MemHs ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) :=
    PDE.MFSemigroup.memHs_of_isSmooth hρS _
  have hVH : PDE.MemHs ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V) :=
    PDE.MFSemigroup.memHs_of_isSmooth hV _
  have ha := PDE.MFAdjoint.aExp_spec s hsd
  have hf2 : Torus.IsCk 2 f := PDE.ClassicalAux.isCk_of_le (by norm_num) hf
  have hfC : Continuous f := Torus.continuous_of_continuous_lift (ContDiff.continuous hf2)
  have hFH : PDE.MemHs ((n : ℝ) + 2) (PDE.coeffOf f) := PDE.MFSemigroup.memHs_of_isSmooth hf _
  -- the backward generator and its coefficients
  have hbgC := PDE.ClassicalPart.continuous_backwardGenerator D hK (by rw [hDV]; exact hV1) hρ1 hf2
  have hbgc := PDE.ClassicalAux.coeffOf_backwardGenerator D hK (by rw [hDV]; exact hV1) hρ1 hf2
  obtain ⟨φ, hφ⟩ : ∃ φ : Torus d → ℝ, φ = backwardGenerator D ρβ f := ⟨_, rfl⟩
  rw [← hφ] at hbgC hbgc
  -- the loss bound for `forwardGen F`
  have hlossF := hloss D hDs hDM ρβ hρC hρH (by rw [hDV]; exact hVH) (PDE.coeffOf f) hFH
  rw [hDinv, hDV] at hlossF
  obtain ⟨RF, hRF⟩ : ∃ R : PDE.Coeff d, R = PDE.forwardGen D ρβ (PDE.coeffOf f) -
      fun k => ((β⁻¹ : ℝ) : ℂ) * PDE.laplaceCoeff (PDE.coeffOf f) k := ⟨_, rfl⟩
  rw [← hRF] at hlossF
  obtain ⟨L, hL⟩ : ∃ L : PDE.Coeff d,
      L = fun k => ((β⁻¹ : ℝ) : ℂ) * PDE.laplaceCoeff (PDE.coeffOf f) k := ⟨_, rfl⟩
  have hLapH : PDE.MemHs (n : ℝ) L := by rw [hL]; exact (fourierTailA_lap (β⁻¹) (n : ℝ) hFH).1
  have hLapN : PDE.hsNorm (n : ℝ) L ≤ |β⁻¹| * PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) := by
    rw [hL]; exact (fourierTailA_lap (β⁻¹) (n : ℝ) hFH).2
  have hRFn0 := fourierTailA_hs_mono (m := (n : ℝ)) (m' := (n : ℝ) + 2 - PDE.MFAdjoint.aExp d s)
    (by linarith [ha.2.1]) hlossF.1
  have hRFN : PDE.hsNorm (n : ℝ) RF ≤ Cl * (PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf ρβ) +
      PDE.hsNorm ((d : ℝ) / 2 + ((n : ℝ) + 2) + 1) (PDE.coeffOf V)) * PDE.hsNorm ((n : ℝ) + 2) (PDE.coeffOf f) :=
    hRFn0.2.trans hlossF.2
  have hRF0 := fourierTailA_hs_mono (m := 0) (m' := (n : ℝ)) (Nat.cast_nonneg n) hRFn0.1
  have hL0 := fourierTailA_hs_mono (m := 0) (m' := (n : ℝ)) (Nat.cast_nonneg n) hLapH
  -- decomposition `forwardGen F = RF + L` (pointwise)
  have hGRL : PDE.forwardGen D ρβ (PDE.coeffOf f) = fun k => RF k + L k := by
    funext k
    rw [hRF, hL]
    simp only [Pi.sub_apply]
    ring
  have hGRLk : ∀ k, PDE.forwardGen D ρβ (PDE.coeffOf f) k = RF k + L k := fun k => congrFun hGRL k
  -- the centering constant `c = μ_β(backward generator)`
  obtain ⟨c, hc⟩ : ∃ c : ℝ, c = pair (withDensityReal ρβ) φ := ⟨_, rfl⟩
  have hEq0 := PDE.equilibrium_operator_order hd s hs0 hsd β hβ V hV2 ρβ hρβ hρ2 hpos f hf2
  rw [← hD, ← hφ] at hEq0
  have hAF : PDE.equilibriumGen d s ρβ β⁻¹ f = fun x => φ x - c := by
    rw [← hEq0, hc]; rfl
  obtain ⟨e', he'⟩ : ∃ e' : PDE.Coeff d, ∀ k, e' k = ((-c : ℝ) : ℂ) * PDE.deltaCoeff (0 : Lattice d) k :=
    ⟨fun k => ((-c : ℝ) : ℂ) * PDE.deltaCoeff (0 : Lattice d) k, fun k => rfl⟩
  have hcdelta := fourierTailA_const_delta (d := d) (-c) (n : ℝ)
  have he'fun : e' = fun k => ((-c : ℝ) : ℂ) * PDE.deltaCoeff (0 : Lattice d) k := funext he'
  rw [← he'fun] at hcdelta
  -- coefficients of `A f`
  have hAcoef : PDE.coeffOf (PDE.equilibriumGen d s ρβ β⁻¹ f) =
      fun k => RF k + (L k + e' k) := by
    funext k
    rw [hAF]
    have hsub : PDE.coeffOf (fun x => φ x - c) k = PDE.coeffOf φ k - PDE.coeffOf (fun _ : Torus d => c) k :=
      PDE.MFApriori.coeffOf_sub φ (fun _ => c) hbgC continuous_const k
    rw [hsub, PDE.coeffOf_const, hbgc, hGRLk, he' k]
    push_cast
    ring
  have hAFMem : PDE.MemHs (n : ℝ) (PDE.coeffOf (PDE.equilibriumGen d s ρβ β⁻¹ f)) := by
    rw [hAcoef]
    exact (PDE.MFAdjoint.hs_add_le (n : ℝ) hRFn0.1 (PDE.MFAdjoint.hs_add_le (n : ℝ) hLapH hcdelta.1).1).1
  have hAFL2 : MeasureTheory.MemLp (PDE.equilibriumGen d s ρβ β⁻¹ f) 2 volume := by
    rw [hAF]; exact PDE.ClassicalAux.memLp_two_of_continuous (hbgC.sub continuous_const)
  have hAFS : MemSobolev (n : ℝ) (PDE.equilibriumGen d s ρβ β⁻¹ f) :=
    PDE.memSobolev_of_memHs _ _ hAFL2 hAFMem
  exact hAFS


/-- Existence form of the weighted coefficient bound (constant independent of the function). -/
theorem fb_coeff_exists (p n : ℕ) (hn : (d : ℝ) / 2 + p < n) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : Torus d → ℝ, Integrable h → MemSobolev (n : ℝ) h →
      Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ p * |Torus.funRealCoeff h l|) ∧
      ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ p * |Torus.funRealCoeff h l| ≤ K * sobolevNorm (n : ℝ) h :=
  ⟨_, by positivity, fun h hi hm => fb_coeff_sum p n hn hi hm⟩

/-- Smoothness of a scaled real mode. -/
theorem fb_mode_smooth (c : ℝ) (j : NonzeroLattice d) : Torus.IsSmooth (fun x => c * Torus.realMode j x) :=
  contDiff_infty.2 fun n => fourierTailA_mul_realMode_isCk c j n

/-- Continuity and Sobolev membership of a smooth function at any natural index. -/
theorem fb_memSob_of_smooth {h : Torus d → ℝ} (hh : Torus.IsSmooth h) (k : ℕ) :
    Continuous h ∧ MemSobolev (k : ℝ) h := by
  obtain ⟨c, m, -⟩ := PDE.MFPair.memSob_of_isCk_ps (PDE.MFPair.isCk_of_smooth_ps hh k)
  exact ⟨c, m⟩

/-- Smoothness of the equilibrium semigroup applied to a smooth function. -/
theorem fb_S_smooth (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (h : Torus d → ℝ) (hh : Torus.IsSmooth h) (v : ℝ) (hv : 0 ≤ v) :
    Torus.IsSmooth (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v h) := by
  have h3 := PDE.ClassicalPart.three_le_mStar d
  refine contDiff_infty.2 fun j => ?_
  obtain ⟨L, hL⟩ : ∃ L : ℕ, L = j + PDE.mStar d + 4 + d := ⟨_, rfl⟩
  have hLm : PDE.mStar d + 4 ≤ L := by omega
  have hjL : (d : ℝ) / 2 + j < L := by
    rw [hL]; push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have : (0 : ℝ) ≤ PDE.mStar d := Nat.cast_nonneg _
    linarith
  obtain ⟨c₀, Λ₀, H⟩ := PDE.MFPair.frozenHyp_of_smooth s hs0 hsd β hβ V hV ρβ hρβ hρS hpos (L + PDE.mStar d)
  obtain ⟨M, c, -, -, hM⟩ := PDE.MFPair.S_cb_bound hd s j L hLm hjL β⁻¹ β⁻¹ c₀ Λ₀
  exact (hM β V ρβ H h (PDE.MFPair.isCk_of_smooth_ps hh L) v hv).1

set_option maxHeartbeats 1000000 in
/-- (D) Decay in `v`, polynomial growth in `⟨j⟩`, of the weighted coefficient sums of `U_v φ_j` and of
`A U_v φ_j`; `C, c` do not depend on `m`, `j`, `v`. -/
theorem fourier_coeff_decay_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (p : ℕ) :
    ∃ C c : ℝ, 0 < C ∧ 0 < c ∧ ∀ (m : ℝ) (j : NonzeroLattice d) (v : ℝ), 0 ≤ v →
      Summable (fun l : NonzeroLattice d => Lattice.jp l.1 ^ p *
        (|Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v
            (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l| +
          |Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹
            (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v
              (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l|)) ∧
      ∑' l : NonzeroLattice d, Lattice.jp l.1 ^ p *
        (|Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v
            (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x)) l| +
          |Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹
            (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v
              (fun x => Lattice.jp j.1 ^ (-m) * Torus.realMode j x))) l|) ≤
        C * Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ)) * Real.exp (-c * v) := by
  -- indices: `n = p + ⌊d/2⌋ + 1`, `N = n + 2`, `J = 2N`
  obtain ⟨n, hn⟩ : ∃ n : ℕ, n = p + d / 2 + 1 := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℕ, N = n + 2 := ⟨_, rfl⟩
  obtain ⟨J, hJ⟩ : ∃ J : ℕ, J = 2 * N := ⟨_, rfl⟩
  have hdn : (d : ℝ) < 2 * ((d / 2 : ℕ) : ℝ) + 2 := by
    have : d < 2 * (d / 2) + 2 := by omega
    exact_mod_cast this
  have hnR : (n : ℝ) = p + ((d / 2 : ℕ) : ℝ) + 1 := by rw [hn]; push_cast; ring
  have hNR : (N : ℝ) = n + 2 := by rw [hN]; push_cast; ring
  have hJR : (J : ℝ) = 2 * N := by rw [hJ]; push_cast; ring
  have hp0 : (0 : ℝ) ≤ p := Nat.cast_nonneg p
  have hq0 : (0 : ℝ) ≤ ((d / 2 : ℕ) : ℝ) := Nat.cast_nonneg _
  have hdn0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hnlt : (d : ℝ) / 2 + p < n := by rw [hnR]; linarith
  have hNlt : (d : ℝ) / 2 + p < N := by rw [hNR]; linarith
  have hJlt : (d : ℝ) / 2 + 4 < J := by rw [hJR, hNR, hnR]; linarith
  have hN1 : N + 1 ≤ p + d + 3 := by omega
  -- frozen data at the three indices
  obtain ⟨c₁, Λ₁, H₁⟩ := PDE.MFPair.frozenHyp_of_smooth s hs0 hsd β hβ V hV ρβ hρβ hρS hpos
    (PDE.mStar d + 5)
  obtain ⟨C0, c0, hC0, hc0, hL2⟩ := PDE.MFAdjoint.exists_frozen_l2_decay hd s β⁻¹ β⁻¹ c₁ Λ₁
  obtain ⟨c₂, Λ₂, H₂⟩ := PDE.MFPair.frozenHyp_of_smooth s hs0 hsd β hβ V hV ρβ hρβ hρS hpos
    (J + PDE.mStar d)
  obtain ⟨CJ, cJ, hCJ, hcJ, hJdec⟩ :=
    PDE.MFAdjoint.exists_frozen_hj_decay' hd s J hJlt β⁻¹ β⁻¹ c₂ Λ₂
  obtain ⟨Cg, hCg, hgen⟩ := equilibriumGen_sobolev_bound_proof hd s hs0 hsd β hβ V hV ρβ hρβ hρS hpos n
  obtain ⟨Kn, hKn, hcoefn⟩ := fb_coeff_exists p n hnlt
  obtain ⟨KN, hKN, hcoefN⟩ := fb_coeff_exists p N hNlt
  have hprob : IsProbDensity ρβ := hρβ.1
  have hρc : Continuous ρβ :=
    Torus.continuous_of_continuous_lift (φ := ρβ) (PDE.MFPair.isCk_of_smooth_ps hρS 0).continuous
  -- the constants of the final bound
  set KQ : ℝ := Real.sqrt (C0 * CJ) * (Real.sqrt 2 + 1) with hKQ
  have hKQ0 : 0 ≤ KQ := mul_nonneg (Real.sqrt_nonneg _) (by positivity)
  have hKN' : 0 ≤ KN + Kn * Cg := add_nonneg hKN (mul_nonneg hKn hCg)
  refine ⟨(KN + Kn * Cg) * KQ + 1, (c0 + cJ) / 2, by nlinarith [mul_nonneg hKN' hKQ0],
    by positivity, ?_⟩
  intro m j v hv
  have hjp1 : ∀ k : Lattice d, 1 ≤ Lattice.jp k := fun k => by
    unfold Lattice.jp
    have : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 := by positivity
    calc (1 : ℝ) = Real.sqrt 1 := Real.sqrt_one.symm
      _ ≤ _ := Real.sqrt_le_sqrt (by linarith)
  set cj : ℝ := Lattice.jp j.1 ^ (-m) with hcj
  have hcj0 : 0 ≤ cj := Real.rpow_nonneg (Torus.jp_pos _).le _
  set φ : Torus d → ℝ := fun x => cj * Torus.realMode j x with hφ
  have hφs : Torus.IsSmooth φ := fb_mode_smooth cj j
  have hφc : Continuous φ := (fb_memSob_of_smooth hφs 0).1
  set g : Torus d → ℝ := PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v φ with hg
  have hgs : Torus.IsSmooth g := fb_S_smooth hd s hs0 hsd β hβ V hV ρβ hρβ hρS hpos φ hφs v hv
  have hgc : Continuous g := (fb_memSob_of_smooth hgs 0).1
  have hg0 : MemSobolev 0 g := by simpa using (fb_memSob_of_smooth hgs 0).2
  have hgN : MemSobolev (N : ℝ) g := (fb_memSob_of_smooth hgs N).2
  have hgJ : MemSobolev (J : ℝ) g := (fb_memSob_of_smooth hgs J).2
  have hgJ2 : MemSobolev (2 * (N : ℝ)) g := by rw [← hJR]; exact hgJ
  -- decay of the H^0 and H^J norms of `g = U_v φ`
  have hmemPsi : MemSobolev ((PDE.mStar d : ℝ) + 2) φ := fb_memSobolev_mode _ _ j
  have hA0 : sobolevNorm 0 g ≤ C0 * Real.exp (-c0 * v) *
      sobolevNorm 2 (projMean (withDensityReal ρβ) φ) :=
    hL2 β V ρβ H₁ φ hφc hmemPsi v hv
  have hAJ0 : sobolevNorm (J : ℝ) g ≤ CJ * Real.exp (-cJ * v) *
      sobolevNorm (J : ℝ) (projMean (withDensityReal ρβ) φ) :=
    (hJdec β V ρβ H₂ φ hφc (fb_memSobolev_mode _ _ j) v hv).2
  have hP2 : sobolevNorm 2 (projMean (withDensityReal ρβ) φ) ≤
      cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ)) :=
    fb_projMean_mode ρβ hprob hρc 2 cj hcj0 j
  have hPJ : sobolevNorm (J : ℝ) (projMean (withDensityReal ρβ) φ) ≤
      cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ)) :=
    fb_projMean_mode ρβ hprob hρc (J : ℝ) cj hcj0 j
  have hE0 : 0 ≤ C0 * Real.exp (-c0 * v) := mul_nonneg hC0.le (Real.exp_pos _).le
  have hEJ : 0 ≤ CJ * Real.exp (-cJ * v) := mul_nonneg hCJ.le (Real.exp_pos _).le
  have hA0' : sobolevNorm 0 g ≤ (C0 * Real.exp (-c0 * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ))) :=
    hA0.trans (mul_le_mul_of_nonneg_left hP2 hE0)
  have hAJ' : sobolevNorm (J : ℝ) g ≤ (CJ * Real.exp (-cJ * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ))) :=
    hAJ0.trans (mul_le_mul_of_nonneg_left hPJ hEJ)
  -- midpoint interpolation `‖g‖_N² ≤ ‖g‖_0 ‖g‖_{2N}`
  have hI := fb_interp (N : ℝ) (Nat.cast_nonneg N) hg0 hgJ2
  rw [← hJR] at hI
  have hX0 : 0 ≤ sobolevNorm (N : ℝ) g := Real.sqrt_nonneg _
  have hA0nn : 0 ≤ sobolevNorm 0 g := Real.sqrt_nonneg _
  have hAJnn : 0 ≤ sobolevNorm (J : ℝ) g := Real.sqrt_nonneg _
  have ha1 : 1 ≤ Lattice.jp j.1 ^ (2 : ℝ) := Real.one_le_rpow (hjp1 j.1) (by norm_num)
  have hb1 : 1 ≤ Lattice.jp j.1 ^ (J : ℝ) := Real.one_le_rpow (hjp1 j.1) (by positivity)
  have hs2 : 0 ≤ Real.sqrt 2 := Real.sqrt_nonneg _
  -- the squared bound
  have hP0nn : 0 ≤ (C0 * Real.exp (-c0 * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ))) :=
    mul_nonneg hE0 (mul_nonneg hcj0 (add_nonneg hs2 (Real.rpow_nonneg (Torus.jp_pos _).le _)))
  have hPJnn : 0 ≤ (CJ * Real.exp (-cJ * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ))) :=
    mul_nonneg hEJ (mul_nonneg hcj0 (add_nonneg hs2 (Real.rpow_nonneg (Torus.jp_pos _).le _)))
  have hprod := mul_le_mul hA0' hAJ' hAJnn hP0nn
  have hsqa : Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ) ≤ (Real.sqrt 2 + 1) * Lattice.jp j.1 ^ (2 : ℝ) := by
    have e : (Real.sqrt 2 + 1) * Lattice.jp j.1 ^ (2 : ℝ) - (Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ)) =
        Real.sqrt 2 * (Lattice.jp j.1 ^ (2 : ℝ) - 1) := by ring
    linarith [mul_nonneg hs2 (sub_nonneg.mpr ha1)]
  have hsqb : Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ) ≤ (Real.sqrt 2 + 1) * Lattice.jp j.1 ^ (J : ℝ) := by
    have e : (Real.sqrt 2 + 1) * Lattice.jp j.1 ^ (J : ℝ) - (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ)) =
        Real.sqrt 2 * (Lattice.jp j.1 ^ (J : ℝ) - 1) := by ring
    linarith [mul_nonneg hs2 (sub_nonneg.mpr hb1)]
  have hBound : (C0 * Real.exp (-c0 * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ))) *
      ((CJ * Real.exp (-cJ * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ)))) ≤
      C0 * CJ * (Real.sqrt 2 + 1) ^ 2 * (Real.exp (-c0 * v) * Real.exp (-cJ * v)) * cj ^ 2 *
        (Lattice.jp j.1 ^ (2 : ℝ) * Lattice.jp j.1 ^ (J : ℝ)) := by
    have hm1 : (Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ)) * (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ)) ≤
        (Real.sqrt 2 + 1) ^ 2 * (Lattice.jp j.1 ^ (2 : ℝ) * Lattice.jp j.1 ^ (J : ℝ)) := by
      have h1 := mul_le_mul hsqa hsqb (add_nonneg hs2 (Real.rpow_nonneg (Torus.jp_pos _).le _))
        (mul_nonneg (add_nonneg hs2 zero_le_one) (Real.rpow_nonneg (Torus.jp_pos _).le _))
      calc _ ≤ _ := h1
        _ = _ := by ring
    have hpos0 : 0 ≤ (C0 * Real.exp (-c0 * v)) * (CJ * Real.exp (-cJ * v)) * cj ^ 2 :=
      mul_nonneg (mul_nonneg hE0 hEJ) (sq_nonneg _)
    have e : (C0 * Real.exp (-c0 * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ))) *
        ((CJ * Real.exp (-cJ * v)) * (cj * (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ)))) =
        (C0 * Real.exp (-c0 * v)) * (CJ * Real.exp (-cJ * v)) * cj ^ 2 *
          ((Real.sqrt 2 + Lattice.jp j.1 ^ (2 : ℝ)) * (Real.sqrt 2 + Lattice.jp j.1 ^ (J : ℝ))) := by ring
    rw [e]
    have e2 : C0 * CJ * (Real.sqrt 2 + 1) ^ 2 * (Real.exp (-c0 * v) * Real.exp (-cJ * v)) * cj ^ 2 *
        (Lattice.jp j.1 ^ (2 : ℝ) * Lattice.jp j.1 ^ (J : ℝ)) =
        (C0 * Real.exp (-c0 * v)) * (CJ * Real.exp (-cJ * v)) * cj ^ 2 *
          ((Real.sqrt 2 + 1) ^ 2 * (Lattice.jp j.1 ^ (2 : ℝ) * Lattice.jp j.1 ^ (J : ℝ))) := by ring
    rw [e2]
    exact mul_le_mul_of_nonneg_left hm1 hpos0
  -- the target bound `Q`
  set cQ : ℝ := (c0 + cJ) / 2 with hcQ
  set KQ : ℝ := Real.sqrt (C0 * CJ) * (Real.sqrt 2 + 1) with hKQdef
  set Q : ℝ := KQ * Real.exp (-cQ * v) * cj * Lattice.jp j.1 ^ ((N : ℝ) + 1) with hQdef
  have hQ0 : 0 ≤ Q := by
    rw [hQdef]
    exact mul_nonneg (mul_nonneg (mul_nonneg hKQ0 (Real.exp_pos _).le) hcj0)
      (Real.rpow_nonneg (Torus.jp_pos _).le _)
  have hQ2 : Q ^ 2 = C0 * CJ * (Real.sqrt 2 + 1) ^ 2 * (Real.exp (-c0 * v) * Real.exp (-cJ * v)) * cj ^ 2 *
      (Lattice.jp j.1 ^ (2 : ℝ) * Lattice.jp j.1 ^ (J : ℝ)) := by
    have hK2 : KQ ^ 2 = C0 * CJ * (Real.sqrt 2 + 1) ^ 2 := by
      rw [hKQdef, mul_pow, Real.sq_sqrt (mul_nonneg hC0.le hCJ.le)]
    have hE : Real.exp (-cQ * v) ^ 2 = Real.exp (-c0 * v) * Real.exp (-cJ * v) := by
      rw [sq, ← Real.exp_add, ← Real.exp_add]; congr 1; rw [hcQ]; ring
    have hJp : (Lattice.jp j.1 ^ ((N : ℝ) + 1)) ^ 2 = Lattice.jp j.1 ^ (2 : ℝ) * Lattice.jp j.1 ^ (J : ℝ) := by
      rw [Torus.jp_rpow_sq, show 2 * ((N : ℝ) + 1) = 2 + (J : ℝ) by rw [hJR]; ring,
        Real.rpow_add (Torus.jp_pos _)]
    rw [hQdef, mul_pow, mul_pow, mul_pow, hK2, hE, hJp]
  have hX2Q : sobolevNorm (N : ℝ) g ≤ Q := by
    calc sobolevNorm (N : ℝ) g = Real.sqrt (sobolevNorm (N : ℝ) g ^ 2) := (Real.sqrt_sq hX0).symm
      _ ≤ Real.sqrt (Q ^ 2) := Real.sqrt_le_sqrt (by rw [hQ2]; exact hI.trans (hprod.trans hBound))
      _ = Q := Real.sqrt_sq hQ0
  -- coefficient sums of `g` and of `A g`
  have hAg := fb_gen_memSobolev hd s hs0 hsd β hβ V hV ρβ hρβ hρS hpos n g hgs
  have hgI : Integrable g := hgc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hAgI : Integrable (PDE.equilibriumGen d s ρβ β⁻¹ g) := hAg.1.integrable one_le_two
  obtain ⟨s1, t1⟩ := hcoefN g hgI hgN
  obtain ⟨s2, t2⟩ := hcoefn (PDE.equilibriumGen d s ρβ β⁻¹ g) hAgI hAg
  have hgen' : sobolevNorm (n : ℝ) (PDE.equilibriumGen d s ρβ β⁻¹ g) ≤ Cg * sobolevNorm (N : ℝ) g := by
    rw [hNR]; exact hgen g hgs
  have hsplit : ∀ l : NonzeroLattice d,
      Lattice.jp l.1 ^ p * (|Torus.funRealCoeff g l| +
          |Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹ g) l|) =
        Lattice.jp l.1 ^ p * |Torus.funRealCoeff g l| +
          Lattice.jp l.1 ^ p * |Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹ g) l| :=
    fun l => mul_add _ _ _
  simp only [hsplit]
  refine ⟨s1.add s2, ?_⟩
  rw [s1.tsum_add s2]
  have hTn : 0 ≤ Real.exp (-cQ * v) * Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ)) :=
    mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg (Torus.jp_pos _).le _)
  have hcjN : cj * Lattice.jp j.1 ^ ((N : ℝ) + 1) ≤ Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ)) := by
    rw [hcj, ← Real.rpow_add (Torus.jp_pos _)]
    have hN1R : (N : ℝ) + 1 ≤ ((p + d + 3 : ℕ) : ℝ) := by exact_mod_cast hN1
    exact Real.rpow_le_rpow_of_exponent_le (hjp1 j.1) (by linarith)
  have hQle : Q ≤ KQ * (Real.exp (-cQ * v) * Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ))) := by
    rw [hQdef]
    calc KQ * Real.exp (-cQ * v) * cj * Lattice.jp j.1 ^ ((N : ℝ) + 1)
        = KQ * Real.exp (-cQ * v) * (cj * Lattice.jp j.1 ^ ((N : ℝ) + 1)) := by ring
      _ ≤ KQ * Real.exp (-cQ * v) * Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ)) :=
          mul_le_mul_of_nonneg_left hcjN (mul_nonneg hKQ0 (Real.exp_pos _).le)
      _ = _ := by ring
  have hfin : (KN + Kn * Cg) * Q ≤
      ((KN + Kn * Cg) * KQ + 1) * (Real.exp (-cQ * v) * Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ))) := by
    calc (KN + Kn * Cg) * Q ≤ (KN + Kn * Cg) * (KQ * (Real.exp (-cQ * v) *
          Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ)))) := mul_le_mul_of_nonneg_left hQle hKN'
      _ = ((KN + Kn * Cg) * KQ) * (Real.exp (-cQ * v) * Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ))) := by
          ring
      _ ≤ ((KN + Kn * Cg) * KQ + 1) * (Real.exp (-cQ * v) *
          Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ))) :=
          mul_le_mul_of_nonneg_right (by linarith [mul_nonneg hKN' hKQ0]) hTn
  have hsumX : KN * sobolevNorm (N : ℝ) g + Kn * sobolevNorm (n : ℝ) (PDE.equilibriumGen d s ρβ β⁻¹ g) ≤
      (KN + Kn * Cg) * sobolevNorm (N : ℝ) g := by
    have h3 : Kn * sobolevNorm (n : ℝ) (PDE.equilibriumGen d s ρβ β⁻¹ g) ≤ Kn * (Cg * sobolevNorm (N : ℝ) g) :=
      mul_le_mul_of_nonneg_left hgen' hKn
    have h4 : (KN + Kn * Cg) * sobolevNorm (N : ℝ) g = KN * sobolevNorm (N : ℝ) g +
        Kn * (Cg * sobolevNorm (N : ℝ) g) := by ring
    linarith
  calc _ ≤ KN * sobolevNorm (N : ℝ) g + Kn * sobolevNorm (n : ℝ) (PDE.equilibriumGen d s ρβ β⁻¹ g) :=
        add_le_add t1 t2
    _ ≤ (KN + Kn * Cg) * sobolevNorm (N : ℝ) g := hsumX
    _ ≤ (KN + Kn * Cg) * Q := mul_le_mul_of_nonneg_left hX2Q hKN'
    _ ≤ ((KN + Kn * Cg) * KQ + 1) * (Real.exp (-cQ * v) *
          Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ))) := hfin
    _ = ((KN + Kn * Cg) * KQ + 1) * Lattice.jp j.1 ^ (-m + ((p + d + 3 : ℕ) : ℝ)) *
          Real.exp (-cQ * v) := by ring



/-- A primitive of a continuous integrand is differentiable (one-sided at `v ≥ 0`) with that integrand. -/
theorem fb_hasDerivWithinAt_of_primitive (F G : ℝ → ℝ) (c0 : ℝ) (hG : Continuous G) {v : ℝ} (hv : 0 ≤ v)
    (hF : ∀ u, 0 ≤ u → u < v + 1 → F u = c0 + ∫ r in (0 : ℝ)..u, G r) :
    HasDerivWithinAt F (G v) (Set.Ici 0) v := by
  have hΦ : HasDerivAt (fun u => c0 + ∫ r in (0 : ℝ)..u, G r) (G v) v :=
    (intervalIntegral.integral_hasDerivAt_right (hG.intervalIntegrable 0 v)
      (hG.stronglyMeasurableAtFilter volume _) hG.continuousAt).const_add c0
  refine hΦ.hasDerivWithinAt.congr_of_eventuallyEq ?_ ?_
  · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (lt_add_one v)), self_mem_nhdsWithin] with u hu1 hu2
    exact hF u hu2 hu1
  · exact hF v hv (lt_add_one v)

/-! ### Regularity: smoothness and `C¹` dependence on `v` of the real Fourier coefficients -/

/-- Path data of the frozen centered semigroup on `[0,T]` (from `frozen_path_data`). -/
theorem fb_path (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (ψ : Torus d → ℝ) (hψ : Torus.IsSmooth ψ) {T : ℝ} (hT : 0 < T) :
    Continuous (fun p : Set.Icc (0 : ℝ) T × Torus d =>
      PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ p.1 ψ p.2) ∧
    Continuous (fun p : Set.Icc (0 : ℝ) T × Torus d =>
      PDE.equilibriumGen d s ρβ β⁻¹ (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ p.1 ψ) p.2) ∧
    ∀ x : Torus d, ∀ σ ∈ Set.Ioo (0 : ℝ) T,
      HasDerivAt (fun σ' => PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ σ' ψ x)
        (PDE.equilibriumGen d s ρβ β⁻¹ (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ σ ψ) x) σ := by
  obtain ⟨c₃, Λ₃, H₃⟩ := PDE.MFPair.frozenHyp_of_smooth s hs0 hsd β hβ V hV ρβ hρβ hρS hpos
    (2 * PDE.mStar d + 4)
  have hψc : Continuous ψ := (fb_memSob_of_smooth hψ 0).1
  have hψm : MemSobolev ((PDE.mStar d : ℝ) + 4) ψ := by
    have := (fb_memSob_of_smooth hψ (PDE.mStar d + 4)).2
    push_cast at this
    exact this
  obtain ⟨-, -, h1, h2, h3⟩ := HRS.PDE.MFLinear.frozen_path_data hd H₃ hψc hψm hT
  exact ⟨h1, h2, h3⟩

/-- Core identities on `[0,T]`: the clamped generator integrand `Gc`, its continuity, the FTC/Fubini
identity for `u ↦ ⟨e_l, U_u ψ⟩`, and the agreement of `Gc` with `⟨e_l, A U_u ψ⟩`. -/
theorem fb_reg_core (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (ψ : Torus d → ℝ) (hψ : Torus.IsSmooth ψ) (l : NonzeroLattice d)
    {T : ℝ} (hT : 0 < T) :
    Continuous (fun r : ℝ => ∫ x, Torus.realMode l x *
      PDE.equilibriumGen d s ρβ β⁻¹ (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ
        (Set.projIcc (0 : ℝ) T hT.le r : ℝ) ψ) x) ∧
    (∀ u ∈ Set.Icc (0 : ℝ) T,
      Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ u ψ) l -
        Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ 0 ψ) l =
      ∫ r in (0 : ℝ)..u, ∫ x, Torus.realMode l x *
        PDE.equilibriumGen d s ρβ β⁻¹ (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ
          (Set.projIcc (0 : ℝ) T hT.le r : ℝ) ψ) x) ∧
    (∀ u ∈ Set.Icc (0 : ℝ) T,
      Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹
        (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ u ψ)) l =
      ∫ x, Torus.realMode l x *
        PDE.equilibriumGen d s ρβ β⁻¹ (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ
          (Set.projIcc (0 : ℝ) T hT.le u : ℝ) ψ) x) := by
  obtain ⟨hC, hD, hE⟩ := fb_path hd s hs0 hsd β hβ V hV ρβ hρβ hρS hpos ψ hψ hT
  set S : ℝ → Torus d → ℝ := fun u => PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ u ψ
    with hSdef
  set A : ℝ → Torus d → ℝ := fun u => PDE.equilibriumGen d s ρβ β⁻¹ (S u) with hAdef
  set P : ℝ → ℝ := fun r => (Set.projIcc (0 : ℝ) T hT.le r : ℝ) with hPdef
  have hPc : Continuous P := continuous_subtype_val.comp continuous_projIcc
  have hPI : ∀ r ∈ Set.Icc (0 : ℝ) T, P r = r := fun r hr => by
    simp only [hPdef]; rw [Set.projIcc_of_mem hT.le hr]
  -- continuity of the clamped integrand `(r, x) ↦ e_l(x) A U_{P r} ψ (x)`
  have hDq : Continuous (fun q : ℝ × Torus d => Torus.realMode l q.2 * A (P q.1) q.2) := by
    have hq : Continuous (fun q : ℝ × Torus d => ((Set.projIcc (0 : ℝ) T hT.le q.1, q.2) :
        Set.Icc (0 : ℝ) T × Torus d)) :=
      Continuous.prodMk (continuous_projIcc.comp continuous_fst) continuous_snd
    exact ((Torus.continuous_realMode l).comp continuous_snd).mul (hD.comp hq)
  have hGc : Continuous (fun r : ℝ => ∫ x, Torus.realMode l x * A (P r) x) := by
    have := continuous_parametric_integral_of_continuous (μ := volume) (f := fun r x =>
      Torus.realMode l x * A (P r) x) hDq isCompact_univ
    simpa [Measure.restrict_univ] using this
  have hSc : ∀ v : ℝ, 0 ≤ v → Continuous (S v) := fun v hv =>
    (fb_memSob_of_smooth (fb_S_smooth hd s hs0 hsd β hβ V hV ρβ hρβ hρS hpos ψ hψ v hv) 0).1
  refine ⟨hGc, ?_, ?_⟩
  · intro u hu
    have hu0 : 0 ≤ u := hu.1
    have huT : u ≤ T := hu.2
    show Torus.funRealCoeff (S u) l - Torus.funRealCoeff (S 0) l =
      ∫ r in (0 : ℝ)..u, ∫ x, Torus.realMode l x * A (P r) x
    -- pointwise fundamental theorem of calculus in the time variable
    have hftc : ∀ x, ∫ r in (0 : ℝ)..u, A r x = S u x - S 0 x := by
      intro x
      have hC_x : ContinuousOn (fun r => S r x) (Set.Icc 0 T) :=
        continuousOn_iff_continuous_restrict.2 (hC.comp (Continuous.prodMk continuous_id continuous_const))
      have hD_x : ContinuousOn (fun r => A r x) (Set.Icc 0 T) :=
        continuousOn_iff_continuous_restrict.2 (hD.comp (Continuous.prodMk continuous_id continuous_const))
      refine intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hu0
        (hC_x.mono (Set.Icc_subset_Icc le_rfl huT)) ?_ ?_
      · intro r hr
        exact (hE x r ⟨hr.1, lt_of_lt_of_le hr.2 huT⟩).hasDerivWithinAt
      · refine ContinuousOn.intervalIntegrable ?_
        rw [Set.uIcc_of_le hu0]
        exact hD_x.mono (Set.Icc_subset_Icc le_rfl huT)
    have hpt : ∀ x, Torus.realMode l x * (S u x - S 0 x) =
        ∫ r in Set.Ioc (0 : ℝ) u, Torus.realMode l x * A (P r) x := by
      intro x
      calc Torus.realMode l x * (S u x - S 0 x) = Torus.realMode l x * ∫ r in (0 : ℝ)..u, A r x := by
            rw [hftc x]
        _ = ∫ r in (0 : ℝ)..u, Torus.realMode l x * A r x :=
            (intervalIntegral.integral_const_mul _ _).symm
        _ = ∫ r in Set.Ioc (0 : ℝ) u, Torus.realMode l x * A r x := intervalIntegral.integral_of_le hu0
        _ = ∫ r in Set.Ioc (0 : ℝ) u, Torus.realMode l x * A (P r) x := by
            refine setIntegral_congr_fun measurableSet_Ioc (fun r hr => ?_)
            rw [hPI r ⟨hr.1.le, hr.2.trans huT⟩]
    have hint : Integrable (Function.uncurry fun (x : Torus d) (r : ℝ) => Torus.realMode l x * A (P r) x)
        (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) u))) := by
      have hcont : Continuous (Function.uncurry fun (x : Torus d) (r : ℝ) => Torus.realMode l x * A (P r) x) :=
        hDq.comp continuous_swap
      have hK : IsCompact (Set.univ ×ˢ Set.Icc (0 : ℝ) u) :=
        (isCompact_univ : IsCompact (Set.univ : Set (Torus d))).prod isCompact_Icc
      have hI : IntegrableOn (Function.uncurry fun (x : Torus d) (r : ℝ) => Torus.realMode l x * A (P r) x)
          (Set.univ ×ˢ Set.Icc (0 : ℝ) u) (volume.prod volume) :=
        hcont.continuousOn.integrableOn_compact hK
      have hmeas : (volume.prod (volume.restrict (Set.Ioc (0 : ℝ) u))) =
          ((volume : Measure (Torus d)).prod (volume : Measure ℝ)).restrict (Set.univ ×ˢ Set.Ioc (0 : ℝ) u) := by
        rw [← Measure.prod_restrict, Measure.restrict_univ]
      rw [hmeas]
      exact hI.mono_set (Set.prod_mono (subset_refl _) Set.Ioc_subset_Icc_self)
    have hfun : (fun x => Torus.realMode l x * (S u x - S 0 x)) =
        fun x => ∫ r in Set.Ioc (0 : ℝ) u, Torus.realMode l x * A (P r) x := funext hpt
    have hsub : ∫ x, Torus.realMode l x * (S u x - S 0 x) =
        Torus.funRealCoeff (S u) l - Torus.funRealCoeff (S 0) l := by
      unfold Torus.funRealCoeff
      rw [← integral_sub]
      · congr 1
        funext x
        ring
      · exact ((Torus.continuous_realMode l).mul (hSc u hu0)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
      · exact ((Torus.continuous_realMode l).mul (hSc 0 le_rfl)).integrable_of_hasCompactSupport
          (HasCompactSupport.of_compactSpace _)
    rw [← hsub, hfun]
    rw [integral_integral_swap hint, intervalIntegral.integral_of_le hu0]
  · intro u hu
    show Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹ (S u)) l =
      ∫ x, Torus.realMode l x * A (P u) x
    unfold Torus.funRealCoeff
    rw [hPI u hu]


/-- (R) Smoothness of `U_v ψ` and `C¹` dependence on `v` of its real Fourier coefficients. -/
theorem fourier_coeff_regular_proof (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 < β) (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρβ : Torus d → ℝ)
    (hρβ : IsThermalDensity (periodicRiesz d s) V β ρβ) (hρS : Torus.IsSmooth ρβ)
    (hpos : ∀ x, 0 < ρβ x) (ψ : Torus d → ℝ) (hψ : Torus.IsSmooth ψ) (l : NonzeroLattice d) :
    (∀ v : ℝ, 0 ≤ v → Torus.IsSmooth (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v ψ)) ∧
    (∀ v : ℝ, 0 ≤ v → HasDerivWithinAt
        (fun u => Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ u ψ) l)
        (Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹
          (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v ψ)) l) (Set.Ici 0) v) ∧
    ContinuousOn (fun v => Torus.funRealCoeff (PDE.equilibriumGen d s ρβ β⁻¹
      (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ v ψ)) l) (Set.Ici 0) := by
  refine ⟨fun v hv => fb_S_smooth hd s hs0 hsd β hβ V hV ρβ hρβ hρS hpos ψ hψ v hv, ?_, ?_⟩
  · intro v hv
    have hT : (0 : ℝ) < v + 1 := by linarith
    obtain ⟨hGc, hFTC, hGeq⟩ := fb_reg_core hd s hs0 hsd β hβ V hV ρβ hρβ hρS hpos ψ hψ l hT
    have hmem : v ∈ Set.Icc (0 : ℝ) (v + 1) := ⟨hv, (lt_add_one v).le⟩
    have key := fb_hasDerivWithinAt_of_primitive
      (fun u => Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ u ψ) l)
      (fun r => ∫ x, Torus.realMode l x * PDE.equilibriumGen d s ρβ β⁻¹
        (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ
          (Set.projIcc (0 : ℝ) (v + 1) hT.le r : ℝ) ψ) x)
      (Torus.funRealCoeff (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ 0 ψ) l)
      hGc hv (fun u hu0 huv => by
        have h1 := hFTC u ⟨hu0, huv.le⟩
        linarith)
    convert key using 1
    exact hGeq v hmem
  · intro v hv0
    have hv : (0 : ℝ) ≤ v := hv0
    have hT : (0 : ℝ) < v + 1 := by linarith
    obtain ⟨hGc, -, hGeq⟩ := fb_reg_core hd s hs0 hsd β hβ V hV ρβ hρβ hρS hpos ψ hψ l hT
    have hcw : ContinuousWithinAt (fun r => ∫ x, Torus.realMode l x * PDE.equilibriumGen d s ρβ β⁻¹
        (PDE.equilibriumSemigroup (PDE.mfData d s hs0 hsd V β hβ) ρβ
          (Set.projIcc (0 : ℝ) (v + 1) hT.le r : ℝ) ψ) x) (Set.Ici 0) v :=
      hGc.continuousAt.continuousWithinAt
    refine hcw.congr_of_eventuallyEq ?_ ?_
    · filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds (lt_add_one v)), self_mem_nhdsWithin] with u hu1 hu2
      exact hGeq u ⟨hu2, hu1.le⟩
    · exact hGeq v ⟨hv, (lt_add_one v).le⟩

end HRS.ME
