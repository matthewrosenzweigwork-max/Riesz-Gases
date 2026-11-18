import HRS.PDE.ForwardEq
import HRS.Analysis.Category

/-!
# Torus PDE layer VI: the constant-coefficient model and the Hadamard obstruction (PDE half)

Sources (HRS periodic main paper, `B:sec:adjoint-symbols`, lines 1766–1822):
* model symbol `B:eq:model-symbol` (1768–1771): with `μ ≡ 1`, `V ≡ 0`, `b = 0` (the kernel has
  zero mean) and `𝒢[e_k] = (2πik)·M^*(2πik) ĝ(k) e_k = -4π²c_{d,s}(2π|k|)^{s-d}(kᵀSk) e_k`;
* model eigenvalue `B:eq:model-eigenvalue` (1772–1775): the solution with datum `e_k` is
  `F(τ) = e^{λ(k)τ} e_k`, `λ(k) = -4π²ν|k|² + 4π²c_{d,s}(2π|k|)^{s-d} kᵀSk`;
* Proposition 3.10 `B:prop:hadamard` (1778–1786): for `d-2 < s < d`, `qᵀSq > 0` for some unit `q`,
  `μ ≡ 1`, `V ≡ 0`, `ν = 0`: for every `τ > 0` and all `m, m' ≥ 0`,
  `sup_{k≠0} ‖F_k(τ)‖_{H^{m'}}/‖e_k‖_{H^m} = sup_k ⟨k⟩^{m'-m} e^{4π²c(2π|k|)^{s-d}(kᵀSk)τ} = ∞`;
  in particular the time-`τ` solution map is not locally bounded from `H^m` to `𝒟'`.

The analytic supremum identity is `HRS.hadamard_sup_eq_top` (ANAL-01, `HRS/Analysis/Category.lean`,
with `hadamardFactor`); this file states the PDE half (ADJ-02): the plane-wave solutions, the
identification of the displayed ratio with `hadamardFactor`, and the `𝒟'`-unboundedness.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-- `kᵀ S k` for the symmetric part `S = ½(M + Mᵀ)`. -/
def quadS (M : Matrix (Fin d) (Fin d) ℝ) (k : Lattice d) : ℝ :=
  ∑ i, ∑ j, (k i : ℝ) * Torus.symPart M i j * (k j : ℝ)

/-- The model eigenvalue `λ(k) = -4π²ν|k|² + 4π²c_{d,s}(2π|k|)^{s-d} kᵀSk` (`B:eq:model-eigenvalue`,
line 1774; `ĝ(k) = c_{d,s}(2π|k|)^{s-d}`, `ĝ(0) = 0`). -/
def modelEigenvalue (d : ℕ) (s ν : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (k : Lattice d) : ℝ :=
  -(4 * Real.pi ^ 2 * ν * Lattice.enorm k ^ 2) + 4 * Real.pi ^ 2 * rieszCoeff d s k * quadS M k

/-- The plane-wave path `F_k(τ) = e^{λ(k)τ} e_k` (coefficients). -/
def planeWaveSol (d : ℕ) (s ν : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (k : Lattice d) (τ : ℝ) :
    Coeff d :=
  fun j => if j = k then (Real.exp (modelEigenvalue d s ν M k * τ) : ℂ) else 0

/-- The constant-coefficient model data: `V ≡ 0`, viscosity `ν`. -/
def modelData (d : ℕ) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ)
    (hν : 0 ≤ ν) : DynData d :=
  ⟨s, M, fun _ => 0, ν, hs0, hsd, hν⟩

/-! ### Auxiliary computations for the constant-density model -/

theorem coeffOf_const (c : ℝ) (j : Lattice d) :
    coeffOf (fun _ : Torus d => c) j = (c : ℂ) * deltaCoeff 0 j := by
  have h := congrFun (coeffOfC_mode (d := d) 0) j
  rw [coeffOfC, funFourierCoeff_eq_int] at h
  simp only [Torus.mode_zero, mul_one] at h
  unfold coeffOf
  rw [funFourierCoeff_eq_int, MeasureTheory.integral_mul_const, h, mul_comm]

theorem mulCoeff_const_delta (c : ℂ) (F : Coeff d) (k : Lattice d) :
    mulCoeff (fun j => c * deltaCoeff 0 j) F k = c * F k := by
  unfold mulCoeff
  rw [tsum_eq_single k]
  · simp [deltaCoeff]
  · intro j hj
    have : k - j ≠ 0 := fun h => hj (by simpa [sub_eq_zero, eq_comm] using h)
    simp [deltaCoeff, this]

theorem quadS_eq_sum (M : Matrix (Fin d) (Fin d) ℝ) (k : Lattice d) :
    quadS M k = ∑ i, ∑ j, (k i : ℝ) * M i j * (k j : ℝ) := by
  unfold quadS Torus.symPart
  simp only [Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
  have : ∑ i, ∑ j, (k i : ℝ) * M j i * (k j : ℝ) = ∑ i, ∑ j, (k i : ℝ) * M i j * (k j : ℝ) := by
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  calc _ = (1/2 : ℝ) * (∑ i, ∑ j, (k i : ℝ) * M i j * (k j : ℝ) +
        ∑ i, ∑ j, (k i : ℝ) * M j i * (k j : ℝ)) := by
        simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
    _ = _ := by rw [this]; ring

theorem quadS_eq_sum' (M : Matrix (Fin d) (Fin d) ℝ) (k : Lattice d) :
    quadS M k = ∑ i, ∑ j, (k i : ℝ) * M j i * (k j : ℝ) := by
  rw [quadS_eq_sum, Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

theorem rieszCoeff_zero (s : ℝ) : rieszCoeff d s 0 = 0 := by simp [rieszCoeff]

/-- the drift vanishes for the constant density and `V ≡ 0`. -/
theorem driftCoeff_const (D : DynData d) (hV : D.V = fun _ => 0) (c : ℝ) (j : Fin d) :
    driftCoeff D (fun _ => c) j = 0 := by
  funext k
  simp only [driftCoeff, gradRieszCoeff, derivCoeff, rieszMult, coeffOf_const, hV,
    Pi.zero_apply, Complex.ofReal_zero]
  by_cases hk : k = 0
  · subst hk; simp [deltaCoeff, rieszCoeff_zero]
  · simp [deltaCoeff, hk]

theorem nonlocalCoeff_const (D : DynData d) (c : ℝ) (F : Coeff d) (k : Lattice d) :
    nonlocalCoeff D (fun _ => c) F k = (c : ℂ) * ∑ i : Fin d, ∑ j : Fin d, ((D.M j i : ℝ) : ℂ) *
      ((2 * Real.pi * Complex.I * (k i : ℂ)) * (((rieszCoeff d D.s k : ℝ) : ℂ) *
        (2 * Real.pi * Complex.I * (k j : ℂ) * F k))) := by
  have hC : coeffOf (fun _ : Torus d => c) = fun j => (c : ℂ) * deltaCoeff 0 j :=
    funext (coeffOf_const c)
  simp only [nonlocalCoeff, hC, mulCoeff_const_delta, gradRieszCoeff, derivCoeff, rieszMult,
    Finset.mul_sum]
  refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring

private theorem mulCoeff_smul_aux (a c : Coeff d) (z : ℂ) :
    mulCoeff a (z • c) = z • mulCoeff a c := by
  funext k
  unfold mulCoeff
  simp only [Pi.smul_apply, smul_eq_mul]
  rw [← tsum_mul_left]
  exact tsum_congr fun j => by ring

private theorem forwardGen_smul_aux (D : DynData d) (ρ : Torus d → ℝ) (c : Coeff d) (z : ℂ) :
    forwardGen D ρ (z • c) = z • forwardGen D ρ c := by
  funext k
  have e : ∀ j, derivCoeff j (z • c) = z • derivCoeff j c := by
    intro j; funext k; simp [PDE.derivCoeff]; ring
  simp only [forwardGen, transportCoeff, nonlocalCoeff, e, mulCoeff_smul_aux, Pi.smul_apply,
    smul_eq_mul]
  simp only [laplaceCoeff, gradRieszCoeff, rieszMult, PDE.derivCoeff, Pi.smul_apply,
    smul_eq_mul]
  simp only [mul_sub, mul_add, Finset.mul_sum]
  congr 1
  · congr 1; ring
  · refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => ?_
    ring

theorem rieszConst_pos' (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) :
    0 < rieszConst d s := by
  have hd' : (0:ℝ) < d := by exact_mod_cast hd
  unfold rieszConst
  split_ifs with h
  · exact mul_pos (mul_pos (by positivity) (by positivity)) (Real.Gamma_pos_of_pos (by positivity))
  · have hs : 0 < s := lt_of_le_of_ne hs0 (Ne.symm h)
    exact div_pos (mul_pos (mul_pos (by positivity) (by positivity))
      (Real.Gamma_pos_of_pos (by linarith))) (Real.Gamma_pos_of_pos (by linarith))

theorem rieszCoeff_pos' (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (k : Lattice d)
    (hk : k ≠ 0) : 0 < rieszCoeff d s k := by
  have h1 := one_le_enorm k hk
  have h2 := rieszConst_pos' hd hs0 hsd
  unfold rieszCoeff
  simp only [hk, ite_false]
  exact mul_pos h2 (Real.rpow_pos_of_pos (by positivity) _)

theorem symNonpos_iff (M : Matrix (Fin d) (Fin d) ℝ) :
    Torus.SymNonpos M ↔ ∀ x : Fin d → ℝ, ∑ i, ∑ j, x i * Torus.symPart M i j * x j ≤ 0 := by
  have hq : ∀ x : Fin d → ℝ, dotProduct (star x) (Matrix.mulVec (-(Torus.symPart M)) x) =
      -∑ i, ∑ j, x i * Torus.symPart M i j * x j := by
    intro x
    simp only [dotProduct, Matrix.mulVec, Matrix.neg_apply, star_trivial, Finset.mul_sum,
      Finset.sum_neg_distrib, neg_mul, mul_neg]
    congr 1
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  constructor
  · intro h x
    have := h.dotProduct_mulVec_nonneg x
    rw [hq] at this
    linarith
  · intro h
    refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
    · ext i j
      simp only [Matrix.conjTranspose_apply, Matrix.neg_apply, star_trivial, Torus.symPart,
        Matrix.smul_apply, Matrix.add_apply, Matrix.transpose_apply, smul_eq_mul]
      ring
    · rw [hq]; linarith [h x]

/-- `B:eq:model-symbol` (lines 1768–1771): with `μ ≡ 1` and `V ≡ 0`, the drift vanishes and the
forward generator acts on `e_k` by `λ(k)`: `𝓛 δ_k = λ(k) δ_k`. -/
theorem forwardGen_const_density (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (hν : 0 ≤ ν) (k : Lattice d) :
    forwardGen (modelData d s hs0 hsd M ν hν) (fun _ => 1) (deltaCoeff k) =
      fun j => ((modelEigenvalue d s ν M k : ℝ) : ℂ) * deltaCoeff k j := by
  funext j
  have hV : (modelData d s hs0 hsd M ν hν).V = fun _ => 0 := rfl
  have hT : transportCoeff (modelData d s hs0 hsd M ν hν) (fun _ => 1) (deltaCoeff k) j = 0 := by
    simp only [transportCoeff, driftCoeff_const _ hV, mulCoeff]
    simp
  have hN := nonlocalCoeff_const (modelData d s hs0 hsd M ν hν) 1 (deltaCoeff k) j
  by_cases hj : j = k
  · subst hj
    rw [forwardGen, hT, hN]
    simp only [modelData, deltaCoeff, ite_true, laplaceCoeff,
      modelEigenvalue, quadS_eq_sum' M j]
    have key : ∀ i j' : Fin d, ((M j' i : ℝ) : ℂ) * (2 * Real.pi * Complex.I * (j i : ℂ) *
        (((rieszCoeff d s j : ℝ) : ℂ) * (2 * Real.pi * Complex.I * (j j' : ℂ) * 1))) =
        -(4 * (Real.pi : ℂ) ^ 2 * ((rieszCoeff d s j : ℝ) : ℂ) *
          ((j i : ℂ) * ((M j' i : ℝ) : ℂ) * (j j' : ℂ))) := by
      intro i j'
      linear_combination (4 * (Real.pi : ℂ) ^ 2 * ((rieszCoeff d s j : ℝ) : ℂ) *
          ((j i : ℂ) * ((M j' i : ℝ) : ℂ) * (j j' : ℂ))) * Complex.I_sq
    simp only [Complex.ofReal_one, one_mul]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j' _ => key i j'))]
    push_cast
    simp only [Finset.sum_neg_distrib, mul_one, Finset.mul_sum]
    ring
  · have : deltaCoeff k j = 0 := by simp [deltaCoeff, hj]
    rw [forwardGen, hT, hN]
    simp [laplaceCoeff, this]

/-- `B:eq:model-eigenvalue` (lines 1772–1775): `F_k(τ) = e^{λ(k)τ} e_k` solves
`B:eq:adjoint-forward` with `μ ≡ 1`, `V ≡ 0`, datum `e_k` (any `ν ≥ 0`, any `t > 0`). -/
theorem planeWave_isForwardSolution (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) (ν : ℝ) (hν : 0 ≤ ν) (k : Lattice d) (t : ℝ) (ht : 0 < t) :
    IsForwardSolution (modelData d s hs0 hsd M ν hν) (fun _ _ => 1) t (deltaCoeff k)
      (planeWaveSol d s ν M k) := by
  set lam := modelEigenvalue d s ν M k with hlam
  have hF : ∀ τ, planeWaveSol d s ν M k τ = ((Real.exp (lam * τ) : ℝ) : ℂ) • deltaCoeff k := by
    intro τ; funext j
    by_cases hj : j = k <;> simp [planeWaveSol, deltaCoeff, hj, hlam]
  have hG : ∀ σ k', forwardGen (modelData d s hs0 hsd M ν hν) (fun _ => 1)
      (planeWaveSol d s ν M k σ) k' =
      (lam : ℂ) * ((Real.exp (lam * σ) : ℝ) : ℂ) * deltaCoeff k k' := by
    intro σ k'
    rw [hF σ, forwardGen_smul_aux, forwardGen_const_density hd s hs0 hsd M ν hν k]
    simp only [Pi.smul_apply, smul_eq_mul]
    ring
  have hcont : Continuous fun σ : ℝ => (lam : ℂ) * ((Real.exp (lam * σ) : ℝ) : ℂ) := by
    fun_prop
  refine ⟨fun τ _ => ?_, fun k' => ?_, fun k' τ hτ => ?_⟩
  · rw [MemHs]
    refine summable_of_ne_finset_zero (s := {k}) fun j hj => ?_
    have : j ≠ k := by simpa using hj
    simp [planeWaveSol, this]
  · simp only [hG]
    exact (Continuous.continuousOn (by fun_prop : Continuous fun σ : ℝ =>
      (lam : ℂ) * ((Real.exp (lam * σ) : ℝ) : ℂ) * deltaCoeff k k')).integrableOn_Icc
  · simp only [hG]
    have hint : ∫ σ in (0 : ℝ)..τ, (lam : ℂ) * ((Real.exp (lam * σ) : ℝ) : ℂ) * deltaCoeff k k' =
        ((Real.exp (lam * τ) - 1 : ℝ) : ℂ) * deltaCoeff k k' := by
      rw [intervalIntegral.integral_mul_const]
      congr 1
      have h1 : ∫ σ in (0 : ℝ)..τ, (lam : ℂ) * ((Real.exp (lam * σ) : ℝ) : ℂ) =
          ((∫ σ in (0 : ℝ)..τ, lam * Real.exp (lam * σ) : ℝ) : ℂ) := by
        rw [← intervalIntegral.integral_ofReal]; push_cast; rfl
      rw [h1]
      congr 1
      have := intervalIntegral.integral_eq_sub_of_hasDerivAt
        (f := fun σ : ℝ => Real.exp (lam * σ)) (f' := fun σ => lam * Real.exp (lam * σ))
        (a := 0) (b := τ) (fun σ _ => by
          have := ((hasDerivAt_id σ).const_mul lam).exp
          simpa [mul_comm] using this)
        (by apply Continuous.intervalIntegrable; fun_prop)
      simpa using this
    rw [hint, hF τ]
    simp only [Pi.smul_apply, smul_eq_mul]
    push_cast
    ring

/-- The second term of `λ(k)` is nonpositive for all `k` iff `S ≤ 0` (line 1776). -/
theorem modelEigenvalue_nonpos_iff (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) :
    (∀ k : Lattice d, 4 * Real.pi ^ 2 * rieszCoeff d s k * quadS M k ≤ 0) ↔ Torus.SymNonpos M := by
  rw [symNonpos_iff]
  constructor
  · intro h x
    by_contra hx
    push Not at hx
    have hx0 : x ≠ 0 := by
      rintro rfl; simp at hx
    set q : Euc d := (‖(WithLp.toLp 2 x : Euc d)‖)⁻¹ • (WithLp.toLp 2 x : Euc d) with hq
    have hn : 0 < ‖(WithLp.toLp 2 x : Euc d)‖ := by
      rw [norm_pos_iff]
      intro h0
      apply hx0
      funext i
      have := congrArg (fun v : Euc d => v i) h0
      simpa using this
    have hq1 : ‖q‖ = 1 := by
      rw [hq, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hn.ne']
    have hqS : 0 < ∑ i, ∑ j, q i * Torus.symPart M i j * q j := by
      have : ∑ i, ∑ j, q i * Torus.symPart M i j * q j =
          (‖(WithLp.toLp 2 x : Euc d)‖⁻¹) ^ 2 * ∑ i, ∑ j, x i * Torus.symPart M i j * x j := by
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [Finset.mul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        simp only [hq, PiLp.smul_apply, smul_eq_mul]
        ring
      rw [this]; positivity
    obtain ⟨k, hk0, hk⟩ := exists_lattice_pos d (Torus.symPart M) ⟨q, hq1, hqS⟩
    have h1 := h k
    have h2 := rieszCoeff_pos' hd hs0 hsd k hk0
    have h3 : quadS M k = ∑ i, ∑ j, (k i : ℝ) * Torus.symPart M i j * (k j : ℝ) := rfl
    have : 0 < 4 * Real.pi ^ 2 * rieszCoeff d s k * quadS M k := by
      rw [h3]; positivity
    linarith
  · intro h k
    have h1 : quadS M k ≤ 0 := h (fun i => (k i : ℝ))
    have h2 : 0 ≤ rieszCoeff d s k := by
      by_cases hk : k = 0
      · simp [hk, rieszCoeff_zero]
      · exact (rieszCoeff_pos' hd hs0 hsd k hk).le
    exact mul_nonpos_of_nonneg_of_nonpos (by positivity) h1

theorem hsNorm_planeWaveSol (s ν : ℝ) (M : Matrix (Fin d) (Fin d) ℝ) (k : Lattice d) (τ m' : ℝ) :
    hsNorm m' (planeWaveSol d s ν M k τ) =
      Real.exp (modelEigenvalue d s ν M k * τ) * hsNorm m' (deltaCoeff k) := by
  set lam := modelEigenvalue d s ν M k with hlam
  have hF : planeWaveSol d s ν M k τ = ((Real.exp (lam * τ) : ℝ) : ℂ) • deltaCoeff k := by
    funext j
    by_cases hj : j = k <;> simp [planeWaveSol, deltaCoeff, hj, hlam]
  rw [hF]
  unfold hsNorm hsNormSq
  simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, mul_pow]
  have : ∀ j, sobWeight m' j * (‖Real.exp (lam * τ)‖ ^ 2 * ‖deltaCoeff k j‖ ^ 2) =
      ‖Real.exp (lam * τ)‖ ^ 2 * (sobWeight m' j * ‖deltaCoeff k j‖ ^ 2) := fun j => by ring
  simp only [this]
  rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (norm_nonneg _),
    Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]

theorem rieszConst_neg_d1 (s : ℝ) (h1 : -1 < s) (h2 : s < 0) : rieszConst 1 s < 0 := by
  unfold rieszConst
  rw [if_neg h2.ne]
  have hG : Real.Gamma (s / 2) < 0 := by
    have h := Real.Gamma_add_one (show s / 2 ≠ 0 by linarith)
    have hp : 0 < Real.Gamma (s / 2 + 1) := Real.Gamma_pos_of_pos (by linarith)
    by_contra hnn
    push Not at hnn
    nlinarith [mul_nonneg_of_nonpos_of_nonpos (show s / 2 ≤ 0 by linarith) (le_refl (0 : ℝ))]
  have : 0 < Real.Gamma (((1 : ℕ) - s) / 2) := Real.Gamma_pos_of_pos (by push_cast; linarith)
  exact div_neg_of_pos_of_neg (by positivity) hG

/-- Why `hadamard_growth` and `hadamard_not_locally_bounded` carry the standing assumption
`0 ≤ s` (implied by `d - 2 < s` only when `d ≥ 2`): for `d = 1` and `-1 < s < 0` one has
`c_{1,s} < 0` and the growth fails, e.g. `s = -1/2`, `M = (1)`, `τ = 1`, `m = m' = 0`. -/
theorem hadamard_growth_false_d1 :
    BddAbove (Set.range fun k : NonzeroLattice 1 =>
      hsNorm 0 (planeWaveSol 1 (-1/2) 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) k.1 1) /
        hsNorm 0 (deltaCoeff k.1)) := by
  refine ⟨1, ?_⟩
  rintro _ ⟨k, rfl⟩
  show hsNorm 0 (planeWaveSol 1 (-1/2) 0 (1 : Matrix (Fin 1) (Fin 1) ℝ) k.1 1) /
        hsNorm 0 (deltaCoeff k.1) ≤ 1
  rw [hsNorm_planeWaveSol]
  have hpos : 0 < hsNorm 0 (deltaCoeff k.1) := by
    rw [hsNorm_deltaCoeff]; positivity
  rw [mul_div_assoc, div_self hpos.ne', mul_one]
  rw [Real.exp_le_one_iff]
  have hc := rieszConst_neg_d1 (-1/2) (by norm_num) (by norm_num)
  have hg : rieszCoeff 1 (-1/2) k.1 ≤ 0 := by
    simp only [rieszCoeff, k.2, ite_false]
    have : 0 < (2 * Real.pi * Lattice.enorm k.1) ^ ((-1/2 : ℝ) - ((1 : ℕ) : ℝ)) :=
      Real.rpow_pos_of_pos (by have := one_le_enorm k.1 k.2; positivity) _
    nlinarith
  have hq : 0 ≤ quadS (1 : Matrix (Fin 1) (Fin 1) ℝ) k.1 := by
    rw [quadS_eq_sum]
    simp [Fin.sum_univ_one]
    nlinarith [sq_nonneg ((k.1 0 : ℤ) : ℝ)]
  unfold modelEigenvalue
  nlinarith [mul_nonneg (mul_nonneg (by positivity : (0:ℝ) ≤ 4 * Real.pi ^ 2) (neg_nonneg.2 hg)) hq]

/-- Proposition 3.10, the displayed ratio (line 1781, first equality): for `ν = 0` and `k ≠ 0`,
`‖F_k(τ)‖_{H^{m'}} / ‖e_k‖_{H^m} = (1+4π²|k|²)^{(m'-m)/2} e^{4π²c_{d,s}(2π|k|)^{s-d}(kᵀSk)τ}
= hadamardFactor d s c_{d,s} τ m m' S k`. -/
theorem hadamard_ratio (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ) (τ m m' : ℝ) (k : Lattice d) (hk : k ≠ 0) :
    hsNorm m' (planeWaveSol d s 0 M k τ) / hsNorm m (deltaCoeff k) =
      hadamardFactor d s (rieszConst d s) τ m m' (Torus.symPart M) k := by
  set lam := modelEigenvalue d s 0 M k with hlam
  have hF : planeWaveSol d s 0 M k τ = ((Real.exp (lam * τ) : ℝ) : ℂ) • deltaCoeff k := by
    funext j
    by_cases hj : j = k <;> simp [planeWaveSol, deltaCoeff, hj, hlam]
  have hnorm := hsNorm_planeWaveSol s 0 M k τ m'
  rw [hnorm, hsNorm_deltaCoeff, hsNorm_deltaCoeff]
  have hnk : Real.sqrt (∑ i, ((k i : ℝ)) ^ 2) = Lattice.enorm k := by
    rw [← enorm_sq_eq_sum, Real.sqrt_sq (by unfold Lattice.enorm; positivity)]
  have hR : rieszCoeff d s k = rieszConst d s * (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)) := by
    simp [rieszCoeff, hk]
  unfold hadamardFactor
  simp only [hnk]
  have hexp : lam * τ = 4 * Real.pi ^ 2 * rieszConst d s * (2 * Real.pi * Lattice.enorm k) ^ (s - (d : ℝ)) *
      (∑ i, ∑ j, (k i : ℝ) * Torus.symPart M i j * (k j : ℝ)) * τ := by
    rw [hlam, modelEigenvalue, hR]
    change _ = _ * (quadS M k) * τ
    ring
  rw [hexp]
  ring

/-- Copy of `HRS.hadamard_sup_eq_top` without the (unused) hypothesis `2 ≤ d`, so that it also
covers `d = 1`. -/
private theorem hadamard_sup_eq_top_aux (d : ℕ) (s : ℝ) (hs1 : (d : ℝ) - 2 < s) (hs2 : s < d)
    (c : ℝ) (hc : 0 < c) (τ : ℝ) (hτ : 0 < τ) (m m' : ℝ) (hm : 0 ≤ m) (hm' : 0 ≤ m')
    (S : Matrix (Fin d) (Fin d) ℝ)
    (hpos : ∃ q : EuclideanSpace ℝ (Fin d), ‖q‖ = 1 ∧ 0 < ∑ i, ∑ j, q i * S i j * q j) :
    ¬ BddAbove (Set.range fun k : {k : Fin d → ℤ // k ≠ 0} => HRS.hadamardFactor d s c τ m m' S k.1) := by
  obtain ⟨q0, hq0, hσ⟩ := HRS.exists_lattice_pos d S hpos
  set σ : ℝ := ∑ i, ∑ j, ((q0 i : ℤ) : ℝ) * S i j * ((q0 j : ℤ) : ℝ) with hσdef
  set T : ℝ := ∑ i, ((q0 i : ℤ) : ℝ) ^ 2 with hTdef
  have hT : 0 < T := by
    obtain ⟨i0, hi0⟩ : ∃ i, q0 i ≠ 0 := by
      by_contra hcon
      push Not at hcon
      exact hq0 (funext hcon)
    refine Finset.sum_pos' (fun i _ => by positivity) ⟨i0, Finset.mem_univ _, ?_⟩
    have : ((q0 i0 : ℤ) : ℝ) ≠ 0 := by exact_mod_cast hi0
    positivity
  set r : ℝ := Real.sqrt T with hrdef
  have hr : 0 < r := Real.sqrt_pos.2 hT
  set A : ℝ := 4 * Real.pi ^ 2 * r ^ 2 with hAdef
  have hA : 0 < A := by positivity
  set θ : ℝ := s - d + 2 with hθdef
  have hθ : 0 < θ := by linarith
  set K : ℝ := 4 * Real.pi ^ 2 * c * (2 * Real.pi * r) ^ (s - d) * σ * τ with hKdef
  have hK : 0 < K := by positivity
  have hlow : ∀ n : ℕ, 1 ≤ n →
      (1 + A) ^ (-(m / 2)) * (Real.exp (K * (n : ℝ) ^ θ) / (n : ℝ) ^ m) ≤
        HRS.hadamardFactor d s c τ m m' S (fun i => (n : ℤ) * q0 i) := by
    intro n hn
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn
    have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
    rw [HRS.hadamardFactor_smul]
    simp only [← hTdef, ← hσdef, ← hrdef]
    have hu : 4 * Real.pi ^ 2 * ((n : ℝ) * r) ^ 2 = A * (n : ℝ) ^ 2 := by rw [hAdef]; ring
    rw [hu]
    have hE : 4 * Real.pi ^ 2 * c * (2 * Real.pi * ((n : ℝ) * r)) ^ (s - d) *
        ((n : ℝ) ^ 2 * σ) * τ = K * (n : ℝ) ^ θ := by
      have e1 : (2 * Real.pi * ((n : ℝ) * r)) = (2 * Real.pi * r) * n := by ring
      rw [e1, Real.mul_rpow (by positivity) hnpos.le, hθdef, Real.rpow_add hnpos, Real.rpow_two,
        hKdef]
      ring
    rw [hE]
    set u : ℝ := 1 + A * (n : ℝ) ^ 2 with hudef
    have hu1 : 1 ≤ u := by rw [hudef]; nlinarith [sq_nonneg (n : ℝ)]
    have hu0 : 0 < u := by linarith
    have hup : 1 ≤ u ^ (m' / 2) := Real.one_le_rpow hu1 (by positivity)
    have hule : u ≤ (1 + A) * (n : ℝ) ^ 2 := by
      rw [hudef]; nlinarith [sq_nonneg (n : ℝ)]
    have hum : u ^ (m / 2) ≤ (1 + A) ^ (m / 2) * (n : ℝ) ^ m := by
      calc u ^ (m / 2) ≤ ((1 + A) * (n : ℝ) ^ 2) ^ (m / 2) :=
            Real.rpow_le_rpow hu0.le hule (by positivity)
        _ = (1 + A) ^ (m / 2) * (n : ℝ) ^ m := by
            rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast (n : ℝ) 2,
              ← Real.rpow_mul hnpos.le]
            congr 2
            push_cast; ring
    have hpos1 : 0 < (1 + A) ^ (m / 2) * (n : ℝ) ^ m := by positivity
    have hexp : 0 < Real.exp (K * (n : ℝ) ^ θ) := Real.exp_pos _
    have hq : 1 / ((1 + A) ^ (m / 2) * (n : ℝ) ^ m) ≤ u ^ (m' / 2) / u ^ (m / 2) := by
      rw [div_le_div_iff₀ hpos1 (by positivity)]
      nlinarith [Real.rpow_pos_of_pos hu0 (m / 2)]
    calc (1 + A) ^ (-(m / 2)) * (Real.exp (K * (n : ℝ) ^ θ) / (n : ℝ) ^ m)
        = 1 / ((1 + A) ^ (m / 2) * (n : ℝ) ^ m) * Real.exp (K * (n : ℝ) ^ θ) := by
          rw [Real.rpow_neg (by positivity)]; field_simp
      _ ≤ _ := by gcongr
  rintro ⟨B, hB⟩
  have ht : Tendsto (fun n : ℕ => (1 + A) ^ (-(m / 2)) *
      (Real.exp (K * (n : ℝ) ^ θ) / (n : ℝ) ^ m)) atTop atTop :=
    Tendsto.const_mul_atTop (by positivity)
      ((HRS.exp_rpow_div_tendsto K θ m hK hθ).comp tendsto_natCast_atTop_atTop)
  have hev := (ht.eventually_gt_atTop B).and (eventually_ge_atTop 1)
  obtain ⟨n, hn1, hn2⟩ := hev.exists
  have hne : (fun i => (n : ℤ) * q0 i) ≠ 0 := by
    intro h0
    apply hq0
    funext i
    have := congrFun h0 i
    simp only [Pi.zero_apply, mul_eq_zero] at this
    rcases this with h | h
    · omega
    · exact h
  have hmem : HRS.hadamardFactor d s c τ m m' S (fun i => (n : ℤ) * q0 i) ∈
      Set.range fun k : {k : Fin d → ℤ // k ≠ 0} => HRS.hadamardFactor d s c τ m m' S k.1 :=
    ⟨⟨_, hne⟩, rfl⟩
  have := hB hmem
  have := hlow n hn2
  linarith

theorem hadamard_growth_aux (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : (d : ℝ) - 2 < s)
    (hsd : s < d) (M : Matrix (Fin d) (Fin d) ℝ)
    (hpos : ∃ q : Euc d, ‖q‖ = 1 ∧ 0 < ∑ i, ∑ j, q i * Torus.symPart M i j * q j)
    (τ : ℝ) (hτ : 0 < τ) (m m' : ℝ) (hm : 0 ≤ m) (hm' : 0 ≤ m') :
    ¬ BddAbove (Set.range fun k : NonzeroLattice d =>
      hsNorm m' (planeWaveSol d s 0 M k.1 τ) / hsNorm m (deltaCoeff k.1)) := by
  rintro ⟨B, hB⟩
  refine hadamard_sup_eq_top_aux d s hs1 hsd (rieszConst d s) (rieszConst_pos' hd hs0 hsd) τ hτ
    m m' hm hm' (Torus.symPart M) hpos ⟨B, ?_⟩
  rintro _ ⟨k, rfl⟩
  show hadamardFactor d s (rieszConst d s) τ m m' (Torus.symPart M) k.1 ≤ B
  rw [← hadamard_ratio hd s hs0 hsd M τ m m' k.1 k.2]
  exact hB ⟨k, rfl⟩

/-- Proposition 3.10 `B:prop:hadamard` (lines 1778–1786), growth: for `0 ≤ s` (standing assumption of the section) and `d-2 < s < d`, `qᵀSq > 0`
for some unit `q`, `μ ≡ 1`, `V ≡ 0`, `ν = 0`, every `τ > 0` and all `m, m' ≥ 0`,
`sup_{k ≠ 0} ‖F_k(τ)‖_{H^{m'}}/‖e_k‖_{H^m} = ∞` (`B:eq:hadamard-growth`), where `F_k` is the
solution with datum `e_k` (`planeWave_isForwardSolution`). -/
theorem hadamard_growth (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : (d : ℝ) - 2 < s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ)
    (hpos : ∃ q : Euc d, ‖q‖ = 1 ∧ 0 < ∑ i, ∑ j, q i * Torus.symPart M i j * q j)
    (τ : ℝ) (hτ : 0 < τ) (m m' : ℝ) (hm : 0 ≤ m) (hm' : 0 ≤ m') :
    ¬ BddAbove (Set.range fun k : NonzeroLattice d =>
      hsNorm m' (planeWaveSol d s 0 M k.1 τ) / hsNorm m (deltaCoeff k.1)) := by
  exact hadamard_growth_aux hd s hs0 hs1 hsd M hpos τ hτ m m' hm hm'

theorem isSmooth_toFun_of_decay (c : Coeff d) (hreal : IsRealCoeff c)
    (hdec : ∀ N : ℕ, MemHs (N : ℝ) c) : Torus.IsSmooth (toFun c) := by
  unfold Torus.IsSmooth Torus.IsCk
  rw [contDiff_infty]
  intro n
  have hm : (d : ℝ) / 2 + n < ((⌈(d : ℝ) / 2 + n⌉₊ + 1 : ℕ) : ℝ) := by
    have := Nat.le_ceil ((d : ℝ) / 2 + n)
    push_cast; linarith
  obtain ⟨C, hC⟩ := toFun_isCk_le (d := d) n ((⌈(d : ℝ) / 2 + n⌉₊ + 1 : ℕ) : ℝ) hm
  exact (hC c (hdec _) hreal).1

theorem summable_nat_decay (N : ℕ) (B κ θ : ℝ) (hB : 0 ≤ B) (hκ : 0 < κ) (hθ : 0 < θ) :
    Summable (fun n : ℕ => B * (n : ℝ) ^ (2 * N) * Real.exp (-(κ * (n : ℝ) ^ θ))) := by
  have hT := (exp_rpow_div_tendsto κ θ ((2 * N + 2 : ℕ) : ℝ) hκ hθ).comp tendsto_natCast_atTop_atTop
  have hev : ∀ᶠ n : ℕ in atTop, B ≤ Real.exp (κ * (n : ℝ) ^ θ) / (n : ℝ) ^ ((2 * N + 2 : ℕ) : ℝ) :=
    hT.eventually (eventually_ge_atTop B)
  have hsum : Summable (fun n : ℕ => (1 : ℝ) / (n : ℝ) ^ 2) := Real.summable_one_div_nat_pow.2 (by norm_num)
  refine Summable.of_norm_bounded_eventually hsum ?_
  rw [Nat.cofinite_eq_atTop]
  filter_upwards [hev, eventually_ge_atTop 1] with n hn hn1
  have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
  rw [Real.rpow_natCast] at hn
  have hE := Real.exp_pos (κ * (n : ℝ) ^ θ)
  rw [le_div_iff₀ (by positivity)] at hn
  rw [Real.norm_eq_abs, abs_of_nonneg (by positivity), Real.exp_neg]
  rw [← sub_nonneg]
  have : 1 / (n : ℝ) ^ 2 - B * (n : ℝ) ^ (2 * N) * (Real.exp (κ * (n : ℝ) ^ θ))⁻¹ =
      (Real.exp (κ * (n : ℝ) ^ θ) - B * (n : ℝ) ^ (2 * N + 2)) /
        ((n : ℝ) ^ 2 * Real.exp (κ * (n : ℝ) ^ θ)) := by
    field_simp
    ring
  rw [this]
  exact div_nonneg (by linarith) (by positivity)

theorem exists_decay_coeff (q0 : Lattice d) (hq0 : q0 ≠ 0) (κ θ : ℝ) (hκ : 0 < κ) (hθ : 0 < θ) :
    ∃ c : Coeff d, IsRealCoeff c ∧ (∀ N : ℕ, MemHs (N : ℝ) c) ∧
      ∀ n : ℕ, c (fun i => ((n : ℤ) + 1) * q0 i) =
        ((Real.exp (-(κ * ((n : ℝ) + 1) ^ θ)) / 2 : ℝ) : ℂ) := by
  classical
  obtain ⟨i0, hi0⟩ : ∃ i, q0 i ≠ 0 := by
    by_contra h; push Not at h; exact hq0 (funext h)
  let e : ℤ → Lattice d := fun z i => z * q0 i
  have hinj : Function.Injective e := by
    intro z z' h
    have := congrFun h i0
    simpa [e, hi0] using this
  let vr : ℤ → ℝ := fun z => if z = 0 then 0 else Real.exp (-(κ * (|(z : ℝ)|) ^ θ)) / 2
  let c : Coeff d := Function.extend e (fun z => (vr z : ℂ)) (fun _ => 0)
  have hce : ∀ z, c (e z) = (vr z : ℂ) := fun z => hinj.extend_apply _ _ z
  have hc0 : ∀ k, (¬ ∃ z, e z = k) → c k = 0 := fun k hk => by
    simp [c, Function.extend_apply' _ _ _ hk]
  have hvr : ∀ z, vr (-z) = vr z := by intro z; simp [vr]
  have hneg : ∀ z, -(e z) = e (-z) := by intro z; funext i; simp [e]
  refine ⟨c, ?_, ?_, ?_⟩
  · intro k
    by_cases hk : ∃ z, e z = k
    · obtain ⟨z, rfl⟩ := hk
      rw [hneg, hce, hce, hvr, Complex.conj_ofReal]
    · have hk' : ¬ ∃ z, e z = -k := by
        rintro ⟨z, hz⟩
        exact hk ⟨-z, by rw [← hneg z, hz, neg_neg]⟩
      rw [hc0 _ hk', hc0 _ hk]; simp
  · intro N
    unfold MemHs
    have hf : ∀ x ∉ Set.range e, sobWeight (N : ℝ) x * ‖c x‖ ^ 2 = 0 := by
      intro x hx
      rw [hc0 x (fun ⟨z, hz⟩ => hx ⟨z, hz⟩)]; simp
    refine (hinj.summable_iff hf).1 ?_
    set R : ℝ := ∑ i, ((q0 i : ℤ) : ℝ) ^ 2 with hR
    have hR0 : 0 ≤ R := Finset.sum_nonneg fun i _ => sq_nonneg _
    set G : ℕ → ℝ := fun n => (1 + 4 * Real.pi ^ 2 * ((n : ℝ) ^ 2 * R)) ^ N *
      (if n = 0 then 0 else Real.exp (-(2 * κ * (n : ℝ) ^ θ)) / 4) with hG
    have hGnn : ∀ n, 0 ≤ G n := by
      intro n; rw [hG]; dsimp only; split_ifs <;> positivity
    have hGle : ∀ n, G n ≤ ((1 + 4 * Real.pi ^ 2 * R) ^ N / 4) * (n : ℝ) ^ (2 * N) *
        Real.exp (-(2 * κ * (n : ℝ) ^ θ)) := by
      intro n
      rw [hG]; dsimp only
      split_ifs with hn
      · simp only [mul_zero]; positivity
      · have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast Nat.one_le_iff_ne_zero.2 hn
        have h1 : (1 + 4 * Real.pi ^ 2 * ((n : ℝ) ^ 2 * R)) ^ N ≤
            (1 + 4 * Real.pi ^ 2 * R) ^ N * (n : ℝ) ^ (2 * N) := by
          rw [pow_mul, ← mul_pow]
          apply pow_le_pow_left₀ (by positivity)
          have : (1 : ℝ) ≤ (n : ℝ) ^ 2 := by nlinarith
          nlinarith [mul_nonneg (by positivity : 0 ≤ 4 * Real.pi ^ 2 * R) (sub_nonneg.2 this)]
        calc (1 + 4 * Real.pi ^ 2 * ((n : ℝ) ^ 2 * R)) ^ N * (Real.exp (-(2 * κ * (n : ℝ) ^ θ)) / 4)
            ≤ ((1 + 4 * Real.pi ^ 2 * R) ^ N * (n : ℝ) ^ (2 * N)) *
                (Real.exp (-(2 * κ * (n : ℝ) ^ θ)) / 4) := by gcongr
          _ = _ := by ring
    have hGs : Summable G := by
      refine Summable.of_nonneg_of_le hGnn hGle ?_
      have := summable_nat_decay N ((1 + 4 * Real.pi ^ 2 * R) ^ N / 4) (2 * κ) θ (by positivity)
        (by positivity) hθ
      exact this
    have hfun : ((fun k => sobWeight (N : ℝ) k * ‖c k‖ ^ 2) ∘ e) = fun z : ℤ => G z.natAbs := by
      funext z
      simp only [Function.comp, hce]
      have habs : ((z.natAbs : ℕ) : ℝ) = |(z : ℝ)| := by simp [Nat.cast_natAbs]
      have h1 : sobWeight (N : ℝ) (e z) = (1 + 4 * Real.pi ^ 2 * ((z.natAbs : ℝ) ^ 2 * R)) ^ N := by
        have hsum : ∑ i, ((e z i : ℤ) : ℝ) ^ 2 = (z.natAbs : ℝ) ^ 2 * R := by
          rw [hR, Finset.mul_sum, habs, sq_abs]
          refine Finset.sum_congr rfl fun i _ => ?_
          simp only [e]; push_cast; ring
        unfold sobWeight
        rw [Real.rpow_natCast, enorm_sq_eq_sum, hsum]
      rw [h1, hG]
      dsimp only
      congr 1
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
      simp only [vr]
      by_cases hz : z = 0
      · simp [hz]
      · have hz' : z.natAbs ≠ 0 := by simpa using hz
        rw [if_neg hz, if_neg hz', div_pow, ← Real.exp_nat_mul]
        rw [← habs]
        congr 2
        push_cast; ring_nf; norm_num
    rw [hfun]
    refine Summable.of_nat_of_neg ?_ ?_
    · simpa using hGs
    · simpa using hGs
  · intro n
    have := hce ((n : ℤ) + 1)
    have hv : vr ((n : ℤ) + 1) = Real.exp (-(κ * ((n : ℝ) + 1) ^ θ)) / 2 := by
      have hne : ((n : ℤ) + 1) ≠ 0 := by omega
      simp only [vr, if_neg hne]
      congr 3
      push_cast
      rw [abs_of_pos (by positivity)]
    rw [hv] at this
    exact this

/-- Proposition 3.10, last sentence (lines 1783–1785; proof lines 1796–1807): for any finite `m`
the time-`τ` solution map is not locally bounded from `H^m(𝕋^d)` to `𝒟'(𝕋^d)`: there are data
`φ_n = ⟨k_n⟩^{-m} e_{k_n}` with `‖φ_n‖_{H^m} = 1` and a smooth real test function `ψ` such that
`|⟨F[φ_n](τ), ψ⟩| → ∞`, where `F[φ_n](τ) = ⟨k_n⟩^{-m} F_{k_n}(τ)` is the solution with datum
`φ_n` (linearity) and `⟨F, ψ⟩ = ∑_k F̂(k) \overline{ψ̂(k)}`. -/
theorem hadamard_not_locally_bounded_aux (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : (d : ℝ) - 2 < s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ)
    (hpos : ∃ q : Euc d, ‖q‖ = 1 ∧ 0 < ∑ i, ∑ j, q i * Torus.symPart M i j * q j)
    (τ : ℝ) (hτ : 0 < τ) (m : ℝ) (hm : 0 ≤ m) :
    ∃ (k : ℕ → Lattice d) (ψ : Torus d → ℝ), Torus.IsSmooth ψ ∧
      (∀ n, k n ≠ 0) ∧
      (∀ n, hsNorm m (fun j => ((Lattice.jp (k n) ^ (-m) : ℝ) : ℂ) * deltaCoeff (k n) j) = 1) ∧
      Tendsto (fun n => ‖distPairing
        (fun j => ((Lattice.jp (k n) ^ (-m) : ℝ) : ℂ) * planeWaveSol d s 0 M (k n) τ j) ψ‖)
        atTop atTop := by
  obtain ⟨q0, hq0, hσ⟩ := exists_lattice_pos d (Torus.symPart M) hpos
  obtain ⟨i0, hi0⟩ : ∃ i, q0 i ≠ 0 := by
    by_contra h; push Not at h; exact hq0 (funext h)
  set r : ℝ := Lattice.enorm q0 with hr
  have hr1 : 1 ≤ r := one_le_enorm q0 hq0
  have hr0 : 0 < r := by linarith
  set σ : ℝ := ∑ i, ∑ j, (q0 i : ℝ) * Torus.symPart M i j * (q0 j : ℝ) with hσdef
  set θ : ℝ := s + 2 - d with hθ
  have hθ0 : 0 < θ := by rw [hθ]; linarith
  have hc0 := rieszConst_pos' hd hs0 hsd
  set K1 : ℝ := 4 * Real.pi ^ 2 * rieszConst d s * (2 * Real.pi * r) ^ (s - (d : ℝ)) * σ with hK1
  have hK10 : 0 < K1 := by rw [hK1]; positivity
  set κ : ℝ := K1 * τ / 2 with hκ
  have hκ0 : 0 < κ := by positivity
  obtain ⟨c, hreal, hdec, hcv⟩ := exists_decay_coeff q0 hq0 κ θ hκ0 hθ0
  have hsumm : Summable fun k => ‖c k‖ := by
    refine summable_norm_of_memHs ((⌈(d : ℝ) / 2⌉₊ + 1 : ℕ) : ℝ) ?_ c (hdec _)
    have := Nat.le_ceil ((d : ℝ) / 2)
    push_cast; linarith
  have hcoeff : coeffOf (toFun c) = c := coeffOf_toFun c hreal hsumm
  set k : ℕ → Lattice d := fun n i => ((n : ℤ) + 1) * q0 i with hk
  have hkne : ∀ n, k n ≠ 0 := by
    intro n h
    have := congrFun h i0
    simp only [hk, Pi.zero_apply, mul_eq_zero] at this
    rcases this with h1 | h1
    · omega
    · exact hi0 h1
  have hkenorm : ∀ n : ℕ, Lattice.enorm (k n) = ((n : ℝ) + 1) * r := by
    intro n
    have h1 : Lattice.enorm (k n) ^ 2 = (((n : ℝ) + 1) * r) ^ 2 := by
      rw [enorm_sq_eq_sum, mul_pow, hr, enorm_sq_eq_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun i _ => ?_
      simp only [hk]; push_cast; ring
    have h2 : 0 ≤ Lattice.enorm (k n) := by unfold Lattice.enorm; positivity
    have h3 : 0 ≤ ((n : ℝ) + 1) * r := by positivity
    exact (pow_left_inj₀ h2 h3 two_ne_zero).1 h1
  have hkq : ∀ n : ℕ, quadS M (k n) = ((n : ℝ) + 1) ^ 2 * σ := by
    intro n
    rw [quadS, hσdef, Finset.mul_sum]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [hk]; push_cast; ring
  have hlam : ∀ n : ℕ, modelEigenvalue d s 0 M (k n) = K1 * ((n : ℝ) + 1) ^ θ := by
    intro n
    have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
    have hg : rieszCoeff d s (k n) = rieszConst d s *
        ((2 * Real.pi * r) ^ (s - (d : ℝ)) * ((n : ℝ) + 1) ^ (s - (d : ℝ))) := by
      simp only [rieszCoeff, hkne n, ite_false]
      rw [hkenorm, show 2 * Real.pi * (((n : ℝ) + 1) * r) = (2 * Real.pi * r) * ((n : ℝ) + 1) by ring,
        Real.mul_rpow (by positivity) hn.le]
    have hpow : ((n : ℝ) + 1) ^ (s - (d : ℝ)) * ((n : ℝ) + 1) ^ 2 = ((n : ℝ) + 1) ^ θ := by
      rw [← Real.rpow_natCast ((n : ℝ) + 1) 2, ← Real.rpow_add hn, hθ]
      congr 1; push_cast; ring
    unfold modelEigenvalue
    rw [hg, hkq, hK1, ← hpow]
    ring
  refine ⟨k, toFun c, isSmooth_toFun_of_decay c hreal hdec, hkne, ?_, ?_⟩
  · intro n
    have hsm : (fun j => ((Lattice.jp (k n) ^ (-m) : ℝ) : ℂ) * deltaCoeff (k n) j) =
        ((Lattice.jp (k n) ^ (-m) : ℝ) : ℂ) • deltaCoeff (k n) := rfl
    rw [hsm]
    have hjp : 0 < Lattice.jp (k n) := Torus.jp_pos _
    have hnorm : hsNorm m (((Lattice.jp (k n) ^ (-m) : ℝ) : ℂ) • deltaCoeff (k n)) =
        |Lattice.jp (k n) ^ (-m)| * hsNorm m (deltaCoeff (k n)) := by
      unfold hsNorm hsNormSq
      simp only [Pi.smul_apply, smul_eq_mul, norm_mul, Complex.norm_real, mul_pow, Real.norm_eq_abs]
      have : ∀ j, sobWeight m j * (|Lattice.jp (k n) ^ (-m)| ^ 2 * ‖deltaCoeff (k n) j‖ ^ 2) =
          |Lattice.jp (k n) ^ (-m)| ^ 2 * (sobWeight m j * ‖deltaCoeff (k n) j‖ ^ 2) :=
        fun j => by ring
      simp only [this]
      rw [tsum_mul_left, Real.sqrt_mul (sq_nonneg _), Real.sqrt_sq (abs_nonneg _)]
    rw [hnorm, hsNorm_deltaCoeff, abs_of_pos (Real.rpow_pos_of_pos hjp _)]
    set X : ℝ := 1 + 4 * Real.pi ^ 2 * Lattice.enorm (k n) ^ 2 with hX
    have hX0 : 0 < X := by positivity
    have hjpX : Lattice.jp (k n) = X ^ ((1 : ℝ) / 2) := by
      rw [← Real.sqrt_eq_rpow]; rfl
    rw [hjpX, ← Real.rpow_mul hX0.le, ← Real.rpow_add hX0]
    have : (1 : ℝ) / 2 * -m + m / 2 = 0 := by ring
    rw [this, Real.rpow_zero]
  · have hnormeq : ∀ n : ℕ, ‖distPairing
        (fun j => ((Lattice.jp (k n) ^ (-m) : ℝ) : ℂ) * planeWaveSol d s 0 M (k n) τ j) (toFun c)‖ =
        Lattice.jp (k n) ^ (-m) / 2 * Real.exp (κ * ((n : ℝ) + 1) ^ θ) := by
      intro n
      have h1 : distPairing
          (fun j => ((Lattice.jp (k n) ^ (-m) : ℝ) : ℂ) * planeWaveSol d s 0 M (k n) τ j) (toFun c) =
          ((Lattice.jp (k n) ^ (-m) : ℝ) : ℂ) * ((Real.exp (modelEigenvalue d s 0 M (k n) * τ) : ℝ) : ℂ) *
            conj (c (k n)) := by
        unfold distPairing
        rw [hcoeff, tsum_eq_single (k n)]
        · simp [planeWaveSol]
        · intro j hj
          simp [planeWaveSol, hj]
      have hkn : c (k n) = ((Real.exp (-(κ * ((n : ℝ) + 1) ^ θ)) / 2 : ℝ) : ℂ) := hcv n
      rw [h1, hkn, Complex.conj_ofReal, norm_mul, norm_mul, Complex.norm_real, Complex.norm_real,
        Complex.norm_real, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs,
        abs_of_pos (Real.rpow_pos_of_pos (Torus.jp_pos _) _), abs_of_pos (Real.exp_pos _),
        abs_of_pos (by positivity : 0 < Real.exp (-(κ * ((n : ℝ) + 1) ^ θ)) / 2), hlam n]
      have : K1 * ((n : ℝ) + 1) ^ θ * τ = 2 * κ * ((n : ℝ) + 1) ^ θ := by rw [hκ]; ring
      rw [this]
      have : Real.exp (2 * κ * ((n : ℝ) + 1) ^ θ) = Real.exp (κ * ((n : ℝ) + 1) ^ θ) *
          Real.exp (κ * ((n : ℝ) + 1) ^ θ) := by rw [← Real.exp_add]; congr 1; ring
      rw [this]
      have h2 : Real.exp (κ * ((n : ℝ) + 1) ^ θ) * Real.exp (-(κ * ((n : ℝ) + 1) ^ θ)) = 1 := by
        rw [← Real.exp_add]; simp
      calc _ = Lattice.jp (k n) ^ (-m) / 2 * Real.exp (κ * ((n : ℝ) + 1) ^ θ) *
            (Real.exp (κ * ((n : ℝ) + 1) ^ θ) * Real.exp (-(κ * ((n : ℝ) + 1) ^ θ))) := by ring
        _ = _ := by rw [h2, mul_one]
    set J : ℝ := Real.sqrt (1 + 4 * Real.pi ^ 2 * r ^ 2) with hJ
    have hJ0 : 0 < J := Real.sqrt_pos.2 (by positivity)
    have hjple : ∀ n : ℕ, Lattice.jp (k n) ≤ J * ((n : ℝ) + 1) := by
      intro n
      have hn1 : (1 : ℝ) ≤ (n : ℝ) + 1 := by linarith [(Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      have hJn : J * ((n : ℝ) + 1) = Real.sqrt ((1 + 4 * Real.pi ^ 2 * r ^ 2) * ((n : ℝ) + 1) ^ 2) := by
        rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity)]
      rw [hJn]
      unfold Lattice.jp
      rw [hkenorm]
      apply Real.sqrt_le_sqrt
      have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ 2 := by nlinarith
      nlinarith [mul_nonneg (by positivity : (0 : ℝ) ≤ 4 * Real.pi ^ 2 * r ^ 2) (sub_nonneg.2 this)]
    have hlow : ∀ n : ℕ, ((J ^ m)⁻¹ / 2) * (Real.exp (κ * ((n : ℝ) + 1) ^ θ) / ((n : ℝ) + 1) ^ m) ≤
        ‖distPairing
        (fun j => ((Lattice.jp (k n) ^ (-m) : ℝ) : ℂ) * planeWaveSol d s 0 M (k n) τ j) (toFun c)‖ := by
      intro n
      rw [hnormeq n]
      have hn : (0 : ℝ) < (n : ℝ) + 1 := by positivity
      have hjp : 0 < Lattice.jp (k n) := Torus.jp_pos _
      have h3 : Lattice.jp (k n) ^ m ≤ J ^ m * ((n : ℝ) + 1) ^ m := by
        rw [← Real.mul_rpow hJ0.le hn.le]
        exact Real.rpow_le_rpow hjp.le (hjple n) hm
      have h4 : (J ^ m * ((n : ℝ) + 1) ^ m)⁻¹ ≤ Lattice.jp (k n) ^ (-m) := by
        rw [Real.rpow_neg hjp.le]
        exact inv_anti₀ (Real.rpow_pos_of_pos hjp _) h3
      have hE := Real.exp_pos (κ * ((n : ℝ) + 1) ^ θ)
      calc ((J ^ m)⁻¹ / 2) * (Real.exp (κ * ((n : ℝ) + 1) ^ θ) / ((n : ℝ) + 1) ^ m)
          = (J ^ m * ((n : ℝ) + 1) ^ m)⁻¹ / 2 * Real.exp (κ * ((n : ℝ) + 1) ^ θ) := by
            rw [mul_inv]; ring
        _ ≤ _ := by gcongr
    have hT : Tendsto (fun n : ℕ => ((J ^ m)⁻¹ / 2) *
        (Real.exp (κ * ((n : ℝ) + 1) ^ θ) / ((n : ℝ) + 1) ^ m)) atTop atTop := by
      refine Tendsto.const_mul_atTop (by positivity) ?_
      exact (exp_rpow_div_tendsto κ θ m hκ0 hθ0).comp
        (tendsto_atTop_add_const_right _ 1 tendsto_natCast_atTop_atTop)
    exact tendsto_atTop_mono hlow hT


/-- Proposition 3.10, last sentence (lines 1783–1785; proof lines 1796–1807): for any finite `m`
the time-`τ` solution map is not locally bounded from `H^m(𝕋^d)` to `𝒟'(𝕋^d)`: there are data
`φ_n = ⟨k_n⟩^{-m} e_{k_n}` with `‖φ_n‖_{H^m} = 1` and a smooth real test function `ψ` such that
`|⟨F[φ_n](τ), ψ⟩| → ∞`, where `F[φ_n](τ) = ⟨k_n⟩^{-m} F_{k_n}(τ)` is the solution with datum
`φ_n` (linearity) and `⟨F, ψ⟩ = ∑_k F̂(k) \overline{ψ̂(k)}`. -/
theorem hadamard_not_locally_bounded (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hs1 : (d : ℝ) - 2 < s) (hsd : s < d)
    (M : Matrix (Fin d) (Fin d) ℝ)
    (hpos : ∃ q : Euc d, ‖q‖ = 1 ∧ 0 < ∑ i, ∑ j, q i * Torus.symPart M i j * q j)
    (τ : ℝ) (hτ : 0 < τ) (m : ℝ) (hm : 0 ≤ m) :
    ∃ (k : ℕ → Lattice d) (ψ : Torus d → ℝ), Torus.IsSmooth ψ ∧
      (∀ n, k n ≠ 0) ∧
      (∀ n, hsNorm m (fun j => ((Lattice.jp (k n) ^ (-m) : ℝ) : ℂ) * deltaCoeff (k n) j) = 1) ∧
      Tendsto (fun n => ‖distPairing
        (fun j => ((Lattice.jp (k n) ^ (-m) : ℝ) : ℂ) * planeWaveSol d s 0 M (k n) τ j) ψ‖)
        atTop atTop := by
  exact hadamard_not_locally_bounded_aux hd s hs0 hs1 hsd M hpos τ hτ m hm

/-- weighted AM-GM / Young: `A x^w ≤ B x + (1-w) A (A w / B)^{w/(1-w)}`. -/
theorem young_aux (w : ℝ) (hw0 : 0 < w) (hw1 : w < 1) (A : ℝ) (hA : 0 ≤ A) (B : ℝ) (hB : 0 < B)
    (x : ℝ) (hx : 0 ≤ x) :
    A * x ^ w ≤ B * x + (1 - w) * A * (A * w / B) ^ (w / (1 - w)) := by
  rcases hA.eq_or_lt with h0 | hApos
  · subst h0
    simp only [zero_mul, mul_zero, zero_div]
    positivity
  · set γ : ℝ := B / (A * w) with hγ
    have hγ0 : 0 < γ := by positivity
    set a : ℝ := γ ^ (1 / (1 - w)) with ha
    have ha0 : 0 < a := Real.rpow_pos_of_pos hγ0 _
    have h1w : 0 < 1 - w := by linarith
    have hawm : a ^ (1 - w) = γ := by
      rw [ha, ← Real.rpow_mul hγ0.le]; field_simp; simp
    have hamw : a ^ (-w) = (A * w / B) ^ (w / (1 - w)) := by
      rw [ha, ← Real.rpow_mul hγ0.le]
      have : A * w / B = γ⁻¹ := by rw [hγ]; field_simp
      rw [this, Real.inv_rpow hγ0.le, ← Real.rpow_neg hγ0.le]
      congr 1; field_simp
    have hamg := Real.geom_mean_le_arith_mean2_weighted (w₁ := w) (w₂ := 1 - w) (p₁ := a * x)
      (p₂ := 1) hw0.le h1w.le (by positivity) zero_le_one (by ring)
    rw [Real.mul_rpow ha0.le hx, Real.one_rpow, mul_one] at hamg
    -- x^w ≤ (w a x + (1-w)) / a^w
    have hawpos : 0 < a ^ w := Real.rpow_pos_of_pos ha0 _
    have hx1 : x ^ w ≤ (w * (a * x) + (1 - w) * 1) * (a ^ (-w)) := by
      rw [Real.rpow_neg ha0.le]
      rw [← div_eq_mul_inv, le_div_iff₀ hawpos]
      linarith
    have key1 : A * (w * a ^ (1 - w)) = B := by
      rw [hawm, hγ]; field_simp
    calc A * x ^ w ≤ A * ((w * (a * x) + (1 - w) * 1) * (a ^ (-w))) := by gcongr
      _ = (A * (w * a ^ (1 - w))) * x + (1 - w) * A * a ^ (-w) := by
          have h5 : a * a ^ (-w) = a ^ (1 - w) := by
            have := Real.rpow_add ha0 1 (-w)
            rw [Real.rpow_one] at this
            rw [← this]; congr 1
          calc A * ((w * (a * x) + (1 - w) * 1) * a ^ (-w))
              = A * (w * (a * a ^ (-w))) * x + (1 - w) * A * a ^ (-w) := by ring
            _ = _ := by rw [h5]
      _ = _ := by rw [key1, hamw]

/-- The contrast noted in the proof (lines 1807–1811): for `ν ≥ ν₀ > 0`, Young's inequality
`C|k|^θ ≤ ν₀(2π|k|)² + Cν₀^{-θ/(2-θ)}` bounds the model growth rates uniformly in `k`:
`λ(k) ≤ C(1 + ν₀^{-θ/(2-θ)})` for all `k` (this is regime R3). -/
theorem modelEigenvalue_bounded_of_viscosity (hd : 1 ≤ d) (s : ℝ) (hs1 : (d : ℝ) - 2 < s)
    (hsd : s < d) (MB : ℝ) :
    ∃ C : ℝ, ∀ (M : Matrix (Fin d) (Fin d) ℝ), MatBound MB M → ∀ (ν ν₀ : ℝ), 0 < ν₀ → ν₀ ≤ ν →
      ∀ k : Lattice d, modelEigenvalue d s ν M k ≤
        C * (1 + ν₀ ^ (-(thetaOrder d s / (2 - thetaOrder d s)))) := by
  set θ := thetaOrder d s with hθ
  have hθ0 : 0 < θ := by rw [hθ, thetaOrder]; linarith
  have hθ2 : θ < 2 := by rw [hθ, thetaOrder]; linarith
  set w : ℝ := θ / 2 with hw
  have hw0 : 0 < w := by positivity
  have hw1 : w < 1 := by rw [hw]; linarith
  have he : w / (1 - w) = θ / (2 - θ) := by
    rw [hw]; field_simp
  set MB' : ℝ := max MB 0 with hMB'
  set A : ℝ := 4 * Real.pi ^ 2 * |rieszConst d s| * (2 * Real.pi) ^ (s - (d : ℝ)) * MB' * d with hA
  have hA0 : 0 ≤ A := by positivity
  refine ⟨(1 - w) * A * (A * w / (4 * Real.pi ^ 2)) ^ (w / (1 - w)), ?_⟩
  intro M hM ν ν₀ hν₀ hνν₀ k
  have hK0 : 0 ≤ (1 - w) * A * (A * w / (4 * Real.pi ^ 2)) ^ (w / (1 - w)) := by
    have : 0 < 1 - w := by linarith
    positivity
  have hpow0 : 0 ≤ ν₀ ^ (-(θ / (2 - θ))) := Real.rpow_nonneg hν₀.le _
  by_cases hk : k = 0
  · subst hk
    have h0 : Lattice.enorm (0 : Lattice d) = 0 := by
      have := enorm_sq_eq_sum (d := d) 0
      simpa using this
    have : modelEigenvalue d s ν M 0 = 0 := by
      simp [modelEigenvalue, h0, rieszCoeff_zero]
    rw [this]
    positivity
  · set r : ℝ := Lattice.enorm k with hr
    have hr1 : 1 ≤ r := one_le_enorm k hk
    have hr0 : 0 < r := by linarith
    -- the bound on the quadratic form
    have hSij : ∀ i j, |Torus.symPart M i j| ≤ MB' := by
      intro i j
      have h1 := hM i j
      have h2 := hM j i
      rw [abs_le] at h1 h2
      have e : Torus.symPart M i j = (M i j + M j i) / 2 := by
        simp [Torus.symPart]; ring
      rw [e, abs_le]
      have := le_max_left MB 0
      constructor <;> linarith [h1.1, h1.2, h2.1, h2.2]
    have hquad : |quadS M k| ≤ MB' * d * r ^ 2 := by
      have hsum : ∀ i j, |(k i : ℝ) * Torus.symPart M i j * (k j : ℝ)| ≤ MB' * (|(k i : ℝ)| * |(k j : ℝ)|) := by
        intro i j
        rw [abs_mul, abs_mul]
        have := hSij i j
        have h1 := abs_nonneg ((k i : ℝ))
        have h2 := abs_nonneg ((k j : ℝ))
        nlinarith [mul_nonneg h1 h2, mul_le_mul_of_nonneg_left this (mul_nonneg h1 h2)]
      calc |quadS M k| ≤ ∑ i, ∑ j, |(k i : ℝ) * Torus.symPart M i j * (k j : ℝ)| := by
            unfold quadS
            refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => ?_)
            exact Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ i, ∑ j, MB' * (|(k i : ℝ)| * |(k j : ℝ)|) :=
            Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => hsum i j
        _ = MB' * (∑ i, |(k i : ℝ)|) ^ 2 := by
            rw [sq, Finset.sum_mul_sum, Finset.mul_sum]
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [Finset.mul_sum]
        _ ≤ MB' * (d * ∑ i, (k i : ℝ) ^ 2) := by
            refine mul_le_mul_of_nonneg_left ?_ (le_max_right _ _)
            have := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin d)))
              (f := fun i => |(k i : ℝ)|)
            simpa [sq_abs] using this
        _ = MB' * d * r ^ 2 := by
            rw [hr, enorm_sq_eq_sum]; ring
    -- the bound on the nonlocal term
    have hg : rieszCoeff d s k = rieszConst d s * ((2 * Real.pi) ^ (s - (d : ℝ)) * r ^ (s - (d : ℝ))) := by
      simp only [rieszCoeff, hk, ite_false]
      rw [Real.mul_rpow (by positivity) hr0.le]
    have hnl : 4 * Real.pi ^ 2 * rieszCoeff d s k * quadS M k ≤ A * (r ^ 2) ^ w := by
      have h1 : 4 * Real.pi ^ 2 * rieszCoeff d s k * quadS M k ≤
          4 * Real.pi ^ 2 * |rieszCoeff d s k| * |quadS M k| := by
        have : 0 ≤ 4 * Real.pi ^ 2 := by positivity
        calc _ ≤ |4 * Real.pi ^ 2 * rieszCoeff d s k * quadS M k| := le_abs_self _
          _ = _ := by rw [abs_mul, abs_mul, abs_of_nonneg this]
      have h2 : |rieszCoeff d s k| = |rieszConst d s| * ((2 * Real.pi) ^ (s - (d : ℝ)) * r ^ (s - (d : ℝ))) := by
        rw [hg, abs_mul, abs_of_nonneg (by positivity : (0:ℝ) ≤ (2 * Real.pi) ^ (s - (d : ℝ)) * r ^ (s - (d : ℝ)))]
      have h3 : (r ^ 2) ^ w = r ^ θ := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_mul hr0.le, hw]
        congr 1; push_cast; ring
      have h4 : r ^ (s - (d : ℝ)) * r ^ 2 = r ^ θ := by
        rw [← Real.rpow_natCast r 2, ← Real.rpow_add hr0, hθ, thetaOrder]
        congr 1; push_cast; ring
      calc _ ≤ _ := h1
        _ ≤ 4 * Real.pi ^ 2 * (|rieszConst d s| * ((2 * Real.pi) ^ (s - (d : ℝ)) * r ^ (s - (d : ℝ)))) *
              (MB' * d * r ^ 2) := by
            rw [h2]; gcongr
        _ = A * (r ^ (s - (d : ℝ)) * r ^ 2) := by rw [hA]; ring
        _ = A * (r ^ 2) ^ w := by rw [h4, h3]
    -- Young
    have hyoung := young_aux w hw0 hw1 A hA0 (4 * Real.pi ^ 2 * ν₀) (by positivity) (r ^ 2) (by positivity)
    have hyoung2 : (A * w / (4 * Real.pi ^ 2 * ν₀)) ^ (w / (1 - w)) =
        (A * w / (4 * Real.pi ^ 2)) ^ (w / (1 - w)) * ν₀ ^ (-(θ / (2 - θ))) := by
      have : A * w / (4 * Real.pi ^ 2 * ν₀) = (A * w / (4 * Real.pi ^ 2)) * ν₀⁻¹ := by
        field_simp
      rw [this, Real.mul_rpow (by positivity) (by positivity), Real.inv_rpow hν₀.le,
        ← Real.rpow_neg hν₀.le, he]
    have hlam : modelEigenvalue d s ν M k =
        -(4 * Real.pi ^ 2 * ν * r ^ 2) + 4 * Real.pi ^ 2 * rieszCoeff d s k * quadS M k := rfl
    have hν2 : 4 * Real.pi ^ 2 * ν₀ * r ^ 2 ≤ 4 * Real.pi ^ 2 * ν * r ^ 2 := by gcongr
    have hKp := mul_nonneg hK0 hpow0
    rw [hyoung2] at hyoung
    rw [hlam]
    have e1 : (1 - w) * A * ((A * w / (4 * Real.pi ^ 2)) ^ (w / (1 - w)) * ν₀ ^ (-(θ / (2 - θ)))) =
        (1 - w) * A * (A * w / (4 * Real.pi ^ 2)) ^ (w / (1 - w)) * ν₀ ^ (-(θ / (2 - θ))) := by ring
    rw [e1] at hyoung
    nlinarith [hyoung, hnl, hν2, hKp]

/-! ### Remark 3.16 `B:rem:forward-regularity` (lines 1996–2007) -/

/-- The nonlocal term `-Div(μ M ∇g*ϱ)` of the forward linearized equation
`B:eq:forward-linearized-comparison` (lines 1998–2002) in coefficients:
`-∑_{i,j} 2πi k_i [μ̂ * (M_{ij} 2πi k_j ĝ ϱ̂)](k)`. -/
def forwardNonlocalCoeff (D : DynData d) (μ : Torus d → ℝ) (F : Coeff d) : Coeff d :=
  fun k => -∑ i : Fin d, ∑ j : Fin d, (2 * Real.pi * Complex.I * (k i : ℂ)) *
    ((D.M i j : ℝ) : ℂ) * mulCoeff (coeffOf μ) (gradRieszCoeff d D.s j F) k

/-- Remark 3.16 (lines 2003–2005): with the coefficient frozen at `μ ≡ μ(x) = c₀`, the leading
nonlocal symbol of the forward equation is `4π²c_{d,s}(2π|k|)^{s-d}(kᵀSk) μ(x)`:
`-Div(c₀ M ∇g*e_k) = 4π² c₀ ĝ(k) (kᵀSk) e_k` (same sign structure as the backward model symbol
`B:eq:model-symbol`, so the sign condition on `S` has the same dissipative meaning). -/
theorem forward_frozen_symbol (hd : 1 ≤ d) (D : DynData d) (c₀ : ℝ) (k : Lattice d) :
    forwardNonlocalCoeff D (fun _ => c₀) (deltaCoeff k) =
      fun j => ((4 * Real.pi ^ 2 * c₀ * rieszCoeff d D.s k * quadS D.M k : ℝ) : ℂ) *
        deltaCoeff k j := by
  funext j
  have hC : coeffOf (fun _ : Torus d => c₀) = fun j => (c₀ : ℂ) * deltaCoeff 0 j :=
    funext (coeffOf_const c₀)
  by_cases hj : j = k
  · subst hj
    have key : ∀ i j' : Fin d, (2 * Real.pi * Complex.I * (j i : ℂ)) * ((D.M i j' : ℝ) : ℂ) *
        ((c₀ : ℂ) * (gradRieszCoeff d D.s j' (deltaCoeff j) j)) =
        -(4 * (Real.pi : ℂ) ^ 2 * c₀ * ((rieszCoeff d D.s j : ℝ) : ℂ) *
          ((j i : ℂ) * ((D.M i j' : ℝ) : ℂ) * (j j' : ℂ))) := by
      intro i j'
      simp only [gradRieszCoeff, derivCoeff, rieszMult, deltaCoeff, ite_true, mul_one]
      linear_combination (4 * (Real.pi : ℂ) ^ 2 * c₀ * ((rieszCoeff d D.s j : ℝ) : ℂ) *
          ((j i : ℂ) * ((D.M i j' : ℝ) : ℂ) * (j j' : ℂ))) * Complex.I_sq
    simp only [forwardNonlocalCoeff, hC, mulCoeff_const_delta]
    rw [Finset.sum_congr rfl (fun i _ => Finset.sum_congr rfl (fun j' _ => key i j'))]
    simp only [deltaCoeff, ite_true, mul_one, quadS_eq_sum]
    push_cast
    simp only [Finset.mul_sum, Finset.sum_neg_distrib]
    rw [neg_neg]
  · have : deltaCoeff k j = 0 := by simp [deltaCoeff, hj]
    simp [forwardNonlocalCoeff, hC, mulCoeff_const_delta, gradRieszCoeff, derivCoeff, rieszMult,
      this]

end HRS.PDE
