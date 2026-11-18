import HRS.Main.Q42Aux1
import HRS.PDE.MeanFieldOneLe

/-!
# Packet Q38b, part 1: the real modes `e_k` as eigenfunctions of the homogeneous operators

Derivatives, Laplacian, Fourier coefficients, the Riesz convolution and the response inverse on
the real mode `realMode k` (cosine and sine cases uniformly).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS

variable {d : ℕ}

open Classical in
/-- The derivative of the real mode (copy of `Q14.q14_partialDeriv_realMode`). -/
lemma q38b_partialDeriv_realMode (j : Fin d) (k : NonzeroLattice d) (x : Torus d) :
    Torus.partialDeriv j (Torus.realMode k) x =
      2 * Real.pi * (k.1 j : ℝ) * Real.sqrt 2 *
        (if Lattice.IsPosHalf k.1 then -Torus.sinMode k.1 x else Torus.cosMode k.1 x) := by
  unfold Torus.partialDeriv
  have hφ : Torus.freqFunctional k.1 (EuclideanSpace.single j 1) = 2 * Real.pi * (k.1 j : ℝ) := by
    rw [Torus.freqFunctional_apply]
    simp [Lattice.dot, PiLp.single_apply]
  by_cases hp : Lattice.IsPosHalf k.1
  · have hl : Torus.lift (Torus.realMode k) =
        fun z => Real.sqrt 2 * Real.cos (Torus.freqFunctional k.1 z) := by
      funext z
      simp [Torus.lift, Torus.realMode, hp, Torus.cosMode_mk, Torus.freqFunctional_apply]
    rw [hl]
    have hd := (((Torus.freqFunctional k.1).hasFDerivAt (x := Torus.rep x)).cos).const_mul
      (Real.sqrt 2)
    rw [hd.fderiv]
    have hs : Real.sin (Torus.freqFunctional k.1 (Torus.rep x)) = Torus.sinMode k.1 x := by
      have h := Torus.sinMode_mk k.1 (Torus.rep x)
      rw [Torus.mk_rep] at h
      rw [h, Torus.freqFunctional_apply]
    simp only [hp, ite_true, ContinuousLinearMap.smul_apply, hφ, hs, smul_eq_mul]
    ring
  · have hl : Torus.lift (Torus.realMode k) =
        fun z => Real.sqrt 2 * Real.sin (Torus.freqFunctional k.1 z) := by
      funext z
      simp [Torus.lift, Torus.realMode, hp, Torus.sinMode_mk, Torus.freqFunctional_apply]
    rw [hl]
    have hd := (((Torus.freqFunctional k.1).hasFDerivAt (x := Torus.rep x)).sin).const_mul
      (Real.sqrt 2)
    rw [hd.fderiv]
    have hs : Real.cos (Torus.freqFunctional k.1 (Torus.rep x)) = Torus.cosMode k.1 x := by
      have h := Torus.cosMode_mk k.1 (Torus.rep x)
      rw [Torus.mk_rep] at h
      rw [h, Torus.freqFunctional_apply]
    simp only [hp, ite_false, ContinuousLinearMap.smul_apply, hφ, hs, smul_eq_mul]
    ring

open Classical in
/-- `∂_j e_k = 2π k_j e_{-k}` (copy of `partialDeriv_realMode_eq`). -/
lemma q38b_partialDeriv_realMode_eq (j : Fin d) (k : NonzeroLattice d) (x : Torus d) :
    Torus.partialDeriv j (Torus.realMode k) x =
      2 * Real.pi * (k.1 j : ℝ) * Torus.realMode ⟨-k.1, neg_ne_zero.2 k.2⟩ x := by
  rw [q38b_partialDeriv_realMode]
  unfold Torus.realMode
  by_cases hp : Lattice.IsPosHalf k.1
  · have hn : ¬ Lattice.IsPosHalf (-k.1) := fun h => ((Torus.isPosHalf_neg k.1 k.2).1 h) hp
    simp only [hp, hn, if_true, if_false, Torus.sinMode_neg]
    ring
  · have hn : Lattice.IsPosHalf (-k.1) := (Torus.isPosHalf_neg k.1 k.2).2 hp
    simp only [hp, hn, if_true, if_false, Torus.cosMode_neg]
    ring

/-- `e_k` is smooth. -/
lemma q38b_isSmooth_realMode (k : NonzeroLattice d) : Torus.IsSmooth (Torus.realMode k) := by
  classical
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

lemma q38b_isCk_realMode (k : NonzeroLattice d) (n : ℕ) : Torus.IsCk n (Torus.realMode k) :=
  PDE.MFSemigroup.isCk_nat_of_isSmooth (q38b_isSmooth_realMode k) n

lemma q38b_continuous_realMode (k : NonzeroLattice d) : Continuous (Torus.realMode k) :=
  Torus.continuous_realMode k

/-- A constant multiple of a `C^n` function is `C^n`. -/
lemma q38b_isCk_const_mul {n : ℕ} {f : Torus d → ℝ} (hf : Torus.IsCk n f) (c : ℝ) :
    Torus.IsCk n (fun y => c * f y) := by
  unfold Torus.IsCk at *
  exact contDiff_const.mul hf

/-- `∂_j (c e_k) = c ∂_j e_k`, expressed through `e_{-k}`. -/
lemma q38b_partialDeriv_c_realMode (j : Fin d) (k : NonzeroLattice d) (c : ℝ) (x : Torus d) :
    Torus.partialDeriv j (fun y => c * Torus.realMode k y) x =
      c * (2 * Real.pi * (k.1 j : ℝ)) * Torus.realMode ⟨-k.1, neg_ne_zero.2 k.2⟩ x := by
  have h1 : Torus.IsCk 1 (Torus.realMode k) := by simpa using q38b_isCk_realMode k 1
  rw [PDE.MFHolder.partialDeriv_const_mul j h1 c x, q38b_partialDeriv_realMode_eq]
  ring

/-- The Laplacian of the real mode: `∑_j ∂_j(1 · ∂_j(c e_k)) = -(2π|k|)² c e_k`. -/
lemma q38b_div_realMode (k : NonzeroLattice d) (c : ℝ) (x : Torus d) :
    ∑ j, Torus.partialDeriv j (fun y' => (1 : ℝ) * Torus.partialDeriv j
        (fun y => c * Torus.realMode k y) y') x =
      -((2 * Real.pi * Lattice.enorm k.1) ^ 2 * (c * Torus.realMode k x)) := by
  set k' : NonzeroLattice d := ⟨-k.1, neg_ne_zero.2 k.2⟩ with hk'
  have h1 : Torus.IsCk 1 (Torus.realMode k') := by simpa using q38b_isCk_realMode k' 1
  have e1 : ∀ j : Fin d, (fun y' => (1 : ℝ) * Torus.partialDeriv j
      (fun y => c * Torus.realMode k y) y') =
      fun y' => (c * (2 * Real.pi * (k.1 j : ℝ))) * Torus.realMode k' y' := by
    intro j
    funext y'
    rw [q38b_partialDeriv_c_realMode, one_mul]
  have e2 : ∀ j : Fin d, Torus.partialDeriv j (fun y' => (c * (2 * Real.pi * (k.1 j : ℝ))) *
      Torus.realMode k' y') x =
      -(c * (2 * Real.pi * (k.1 j : ℝ)) * (2 * Real.pi * (k.1 j : ℝ)) * Torus.realMode k x) := by
    intro j
    rw [PDE.MFHolder.partialDeriv_const_mul j h1, q38b_partialDeriv_realMode_eq]
    have : (⟨-k'.1, neg_ne_zero.2 k'.2⟩ : NonzeroLattice d) = k := by
      apply Subtype.ext
      simp [hk']
    rw [this]
    simp only [hk', Pi.neg_apply, Int.cast_neg]
    ring
  simp_rw [e1, e2]
  have hn : Lattice.enorm k.1 ^ 2 = ∑ j, (k.1 j : ℝ) ^ 2 := by
    unfold Lattice.enorm
    rw [EuclideanSpace.real_norm_sq_eq]
    rfl
  have : (2 * Real.pi * Lattice.enorm k.1) ^ 2 = (2 * Real.pi) ^ 2 * ∑ j, (k.1 j : ℝ) ^ 2 := by
    rw [mul_pow, hn]
  rw [this, Finset.mul_sum, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  ring

open Classical in
/-- Fourier coefficients of the real mode: supported on `±k`. -/
theorem q38b_funFourier_realMode (k : NonzeroLattice d) (j : Lattice d) :
    Torus.funFourierCoeff (fun x => ((Torus.realMode k x : ℝ) : ℂ)) j =
      (if -j + k.1 = 0 then Torus.realCoef k.1 else 0) +
        (if -j + -k.1 = 0 then conj (Torus.realCoef k.1) else 0) := by
  rw [PDE.funFourierCoeff_eq_int]
  have hpt : ∀ x : Torus d, UnitAddTorus.mFourier (-j) x * ((Torus.realMode k x : ℝ) : ℂ) =
      Torus.realCoef k.1 * Torus.mode (-j + k.1) x +
        conj (Torus.realCoef k.1) * Torus.mode (-j + -k.1) x := by
    intro x
    rw [Torus.realMode_cplx, Torus.mode_add, Torus.mode_add]
    show Torus.mode (-j) x * _ = _
    ring
  have i1 : ∫ x : Torus d, Torus.mode (-j + k.1) x = if -j + k.1 = 0 then 1 else 0 :=
    Torus.integral_mode _
  have i2 : ∫ x : Torus d, Torus.mode (-j + -k.1) x = if -j + -k.1 = 0 then 1 else 0 :=
    Torus.integral_mode _
  have hI1 : Integrable (fun x : Torus d => Torus.mode (-j + k.1) x) (volume : Measure (Torus d)) :=
    (Torus.continuous_mode _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hI2 : Integrable (fun x : Torus d => Torus.mode (-j + -k.1) x) (volume : Measure (Torus d)) :=
    (Torus.continuous_mode _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [hpt]
  rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul,
    i1, i2]
  split_ifs <;> simp

/-- Eigenfunction property of the periodic Riesz convolution on every real mode:
`g * e_k = ĝ(k) e_k`. -/
theorem q38b_convFun_realMode (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (k : NonzeroLattice d) :
    convFun (periodicRiesz d s) (fun x => Torus.realMode k x) =
      fun x => rieszCoeff d s k.1 * Torus.realMode k x := by
  have hg := PDE.MFAux.integrable_periodicRiesz hd s hs0 hsd
  have hc : Continuous (fun x => Torus.realMode k x) := Torus.continuous_realMode k
  apply PDE.MFAux.eq_of_funFourierCoeff_eq (PDE.MFAux.continuous_convFun hg hc)
    (continuous_const.mul hc)
  intro j
  show Torus.funFourierCoeff (fun x => (convFun (periodicRiesz d s)
      (fun x => Torus.realMode k x) x : ℂ)) j =
    Torus.funFourierCoeff (fun x => ((rieszCoeff d s k.1 * Torus.realMode k x : ℝ) : ℂ)) j
  rw [PDE.MFAux.funFourierCoeff_convFun hg hc j, periodicRiesz_fourierCoeff hd hs0 hsd j,
    q42_fourier_const_mul, q38b_funFourier_realMode]
  by_cases h1 : j = k.1
  · rw [h1]
  by_cases h2 : j = -k.1
  · rw [h2, rieszCoeff_neg]
  · have e1 : ¬ (-j + k.1 = 0) := fun h => h1 (neg_add_eq_zero.mp h)
    have e2 : ¬ (-j + -k.1 = 0) := fun h => h2 (neg_add_eq_zero.mp h)
    simp [e1, e2]

end HRS
