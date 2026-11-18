import HRS.PDE.EnergyDrift
import HRS.PDE.EnergyTorusLimit

/-!
# The form estimate of Proposition 3.13 / 3.14 (assembly)

`energy_form_estimate`, `energy_torus` and `energy_form_estimate_R2c` live here (rather than in
`Energy.lean`) because their proofs use `Galerkin.lean`, which imports `Energy.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

/-! ### Multinomial expansion of the `H^m` inner product -/

/-- The weight `∏_i (2πk_i)^{2α_i}`. -/
abbrev wtP (α : Fin d → ℕ) (k : Lattice d) : ℝ := ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i)

theorem sobWeight_nat_eq_sum (m : ℕ) (k : Lattice d) :
    sobWeight (m : ℝ) k = ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) * wtP α k := by
  have h1 : sobWeight (m : ℝ) k = (1 + ∑ i, (2 * Real.pi * (k i : ℝ)) ^ 2) ^ m := by
    rw [sobWeight_natCast, four_pi_enorm_sq]
  rw [h1, one_add_sum_pow]
  refine Finset.sum_congr rfl fun α _ => ?_
  congr 1
  exact Finset.prod_congr rfl fun i _ => by rw [← pow_mul]

theorem bilinForm_box {n : ℕ} (w : Lattice d → ℝ) (G F : Coeff d) (hF : IsTrigPoly n F) :
    bilinForm w G F = ∑ k ∈ boxFin d n, ((w k : ℝ) : ℂ) * (G k * conj (F k)) := by
  unfold bilinForm
  refine tsum_eq_sum fun k hk => ?_
  rw [eq_zero_of_isTrigPoly hF hk]; simp

theorem hsInner_box {n : ℕ} (r : ℝ) (G F : Coeff d) (hF : IsTrigPoly n F) :
    hsInner r G F = ∑ k ∈ boxFin d n, ((sobWeight r k : ℝ) : ℂ) * (G k * conj (F k)) := by
  unfold hsInner
  refine tsum_eq_sum fun k hk => ?_
  rw [eq_zero_of_isTrigPoly hF hk]; simp

theorem re_bilinForm_box {n : ℕ} (w : Lattice d → ℝ) (G F : Coeff d) (hF : IsTrigPoly n F) :
    (bilinForm w G F).re = ∑ k ∈ boxFin d n, w k * (G k * conj (F k)).re := by
  rw [bilinForm_box w G F hF, Complex.re_sum]
  exact Finset.sum_congr rfl fun k _ => Complex.re_ofReal_mul _ _

theorem hsInner_eq_sum_bilin {n : ℕ} (m : ℕ) (G F : Coeff d) (hF : IsTrigPoly n F) :
    (hsInner (m : ℝ) G F).re =
      ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) * (bilinForm (wtP α) G F).re := by
  have e : (hsInner (m : ℝ) G F).re =
      ∑ k ∈ boxFin d n, sobWeight (m : ℝ) k * (G k * conj (F k)).re := by
    rw [hsInner_box _ G F hF, Complex.re_sum]
    exact Finset.sum_congr rfl fun k _ => Complex.re_ofReal_mul _ _
  rw [e]
  simp_rw [re_bilinForm_box _ G F hF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sobWeight_nat_eq_sum, Finset.sum_mul]
  exact Finset.sum_congr rfl fun α _ => by ring

theorem bilinForm_laplace (α : Fin d → ℕ) (F : Coeff d) :
    bilinForm (wtP α) (laplaceCoeff F) F = ((-gradDerivL2Sq α F : ℝ) : ℂ) := by
  unfold bilinForm gradDerivL2Sq
  rw [← tsum_neg, Complex.ofReal_tsum]
  refine tsum_congr fun k => ?_
  unfold laplaceCoeff
  have : (F k * conj (F k)) = ((‖F k‖ ^ 2 : ℝ) : ℂ) := by
    rw [Complex.mul_conj']; push_cast; ring
  have hc : (F k * conj (F k)) = ((‖F k‖ ^ 2 : ℝ) : ℂ) := this
  rw [show ((wtP α k : ℝ) : ℂ) * (-(((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ)) * F k *
      conj (F k)) = -(((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2 : ℝ) : ℂ)) * ((wtP α k : ℝ) : ℂ) *
      (F k * conj (F k)) by ring, hc]
  push_cast
  ring

theorem gradDerivL2Sq_box {n : ℕ} (α : Fin d → ℕ) (F : Coeff d) (hF : IsTrigPoly n F) :
    gradDerivL2Sq α F = ∑ k ∈ boxFin d n,
      (4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * wtP α k * ‖F k‖ ^ 2 := by
  unfold gradDerivL2Sq
  refine tsum_eq_sum fun k hk => ?_
  rw [eq_zero_of_isTrigPoly hF hk]; simp

theorem sum_mw_gradDerivL2Sq {n : ℕ} (m : ℕ) (F : Coeff d) (hF : IsTrigPoly n F) :
    ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) * gradDerivL2Sq α F =
      hsNormSq ((m : ℝ) + 1) F - hsNormSq (m : ℝ) F := by
  rw [hsNormSq_of_isTrigPoly hF, hsNormSq_of_isTrigPoly hF, ← Finset.sum_sub_distrib]
  simp_rw [gradDerivL2Sq_box _ F hF, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [sobWeight_add, sobWeight_one, sobWeight_nat_eq_sum]
  have : ∀ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) *
      ((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * wtP α k * ‖F k‖ ^ 2) =
      ((4 * Real.pi ^ 2 * Lattice.enorm k ^ 2) * ‖F k‖ ^ 2) *
        ((multinomialWeight m α : ℝ) * wtP α k) := fun α _ => by ring
  rw [Finset.sum_congr rfl this, ← Finset.mul_sum, ← sobWeight_nat_eq_sum]
  ring

theorem bilinForm_forwardGen {n : ℕ} (D : DynData d) (ρ : Torus d → ℝ) (w : Lattice d → ℝ)
    (F : Coeff d) (hF : IsTrigPoly n F) :
    bilinForm w (forwardGen D ρ F) F = ((D.invβ : ℝ) : ℂ) * bilinForm w (laplaceCoeff F) F +
      bilinForm w (transportCoeff D ρ F) F - bilinForm w (nonlocalCoeff D ρ F) F := by
  simp only [bilinForm_box w _ F hF]
  rw [Finset.mul_sum, ← Finset.sum_add_distrib, ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun k _ => ?_
  simp only [forwardGen]
  ring

/-- The expansion of `Re ⟨𝓛F, F⟩_{H^m}` into viscous, transport and nonlocal parts. -/
theorem re_hsInner_forwardGen {n : ℕ} (D : DynData d) (ρ : Torus d → ℝ) (m : ℕ) (F : Coeff d)
    (hF : IsTrigPoly n F) :
    (hsInner (m : ℝ) (forwardGen D ρ F) F).re =
      -D.invβ * ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) * gradDerivL2Sq α F +
      ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) *
        (bilinForm (wtP α) (transportCoeff D ρ F) F).re -
      ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) *
        (bilinForm (wtP α) (nonlocalCoeff D ρ F) F).re := by
  rw [hsInner_eq_sum_bilin m _ F hF, Finset.mul_sum, ← Finset.sum_add_distrib,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun α _ => ?_
  rw [bilinForm_forwardGen D ρ _ F hF, bilinForm_laplace]
  simp only [Complex.sub_re, Complex.add_re, Complex.re_ofReal_mul, Complex.ofReal_re]
  ring

theorem sum_mw_pos (m : ℕ) : 0 < ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) := by
  have h0 : (0 : Fin d → ℕ) ∈ multiIndices d m := by simp [multiIndices]
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun α => (multinomialWeight m α : ℝ))
    (fun α _ => Nat.cast_nonneg _) h0)
  have := one_le_multinomialWeight m 0 h0
  exact_mod_cast this

/-- Viscous and transport parts of the form estimate. -/
theorem re_hsInner_le_basic {n : ℕ} (D : DynData d) (ρ : Torus d → ℝ) (m : ℕ) (F : Coeff d)
    (hF : IsTrigPoly n F) (CT : ℝ)
    (hT : ∀ α ∈ multiIndices d m,
      |(bilinForm (wtP α) (transportCoeff D ρ F) F).re| ≤ CT * hsNormSq (m : ℝ) F) :
    (hsInner (m : ℝ) (forwardGen D ρ F) F).re ≤
      -(D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α F -
      (D.invβ / 2) * (hsNormSq ((m : ℝ) + 1) F - hsNormSq (m : ℝ) F) +
      (∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ)) * CT * hsNormSq (m : ℝ) F -
      ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) *
        (bilinForm (wtP α) (nonlocalCoeff D ρ F) F).re := by
  rw [re_hsInner_forwardGen D ρ m F hF]
  have hX := sum_mw_gradDerivL2Sq m F hF
  have hXG : ∑ α ∈ multiIndices d m, gradDerivL2Sq α F ≤
      ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) * gradDerivL2Sq α F := by
    refine Finset.sum_le_sum fun α hα => ?_
    have h1 : (1 : ℝ) ≤ multinomialWeight m α := by exact_mod_cast one_le_multinomialWeight m α hα
    have := gradDerivL2Sq_nonneg α F
    nlinarith
  have hTsum : ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) *
      (bilinForm (wtP α) (transportCoeff D ρ F) F).re ≤
      (∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ)) * CT * hsNormSq (m : ℝ) F := by
    rw [mul_assoc, Finset.sum_mul]
    refine Finset.sum_le_sum fun α hα => ?_
    have h0 : (0 : ℝ) ≤ multinomialWeight m α := Nat.cast_nonneg _
    exact mul_le_mul_of_nonneg_left ((le_abs_self _).trans (hT α hα)) h0
  have hν := D.hβ
  rw [← hX] at *
  nlinarith [mul_le_mul_of_nonneg_left hXG hν]

/-! ### Transport and R1 parts as constants independent of the data -/

theorem transport_part (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (MB Λ VB : ℝ) :
    ∃ CT : ℝ, 0 ≤ CT ∧ ∀ (D : DynData d), D.s = s → MatBound MB D.M → VHyp m VB D.V →
      ∀ μ : Torus d → ℝ, IsProbDensity μ → Torus.IsCk (m + 3) μ → Torus.cbNorm (m + 3) μ ≤ Λ →
      ∀ (n : ℕ) (F : Coeff d), IsRealCoeff F → IsTrigPoly n F → ∀ α ∈ multiIndices d m,
        |(bilinForm (wtP α) (transportCoeff D μ F) F).re| ≤ CT * hsNormSq (m : ℝ) F := by
  obtain ⟨B, hB⟩ := exists_driftFuns hd s hs0 hsd m MB Λ VB
  obtain ⟨C0, hC0⟩ := transport_form_bound hd m B
  refine ⟨max C0 0, le_max_right _ _, ?_⟩
  intro D hDs hM hV μ hp hCk hΛ n F hFr hF α hα
  obtain ⟨b, hb1, hb2, hb3⟩ := hB D hDs hM hV μ hp hCk hΛ
  have e : transportCoeff D μ F = fun k => ∑ j, mulCoeff (coeffOf (b j)) (derivCoeff j F) k := by
    funext k; simp only [transportCoeff, hb3]
  rw [e]
  exact (hC0 b hb1 hb2 α hα n F hFr hF).trans
    (mul_le_mul_of_nonneg_right (le_max_left _ _) (hsNormSq_nonnegE _ _))

theorem r1_part (s : ℝ) (hs : s ≤ (d : ℝ) - 2) (m : ℕ) (MB Λ : ℝ) :
    ∃ CR : ℝ, 0 ≤ CR ∧ ∀ (D : DynData d), D.s = s → MatBound MB D.M →
      ∀ μ : Torus d → ℝ, Torus.IsCk (m + 3) μ → Torus.cbNorm (m + 3) μ ≤ Λ →
      ∀ (n : ℕ) (F : Coeff d), IsTrigPoly n F → ∀ α ∈ multiIndices d m,
        |(bilinForm (wtP α) (nonlocalCoeff D μ F) F).re| ≤ CR * hsNormSq (m : ℝ) F := by
  classical
  refine ⟨(1 + ∑ α' ∈ multiIndices d m, r1Const d s MB Λ α') / 2, by
    have : 0 ≤ ∑ α' ∈ multiIndices d m, r1Const d s MB Λ α' :=
      Finset.sum_nonneg fun α' _ => r1Const_nonneg s MB Λ α'
    positivity, ?_⟩
  intro D hDs hM μ hμ hΛ n F hF α hα
  have hαm : ∑ i, α i ≤ m := (Finset.mem_filter.mp hα).2
  have hμ' : ContDiff ℝ ((m + 3 : ℕ) : WithTop ℕ∞) (Torus.lift μ) := by
    unfold Torus.IsCk at hμ; push_cast; exact hμ
  set H := hsNormSq (m : ℝ) F with hH
  have hA : ∑ k ∈ boxFin d n, ‖multiDerivCoeff α F k‖ ^ 2 ≤ H :=
    sum_sq_multiDeriv_le α m hαm F (memHs_of_isTrigPolyE hF _) _
  have hBd : ∑ k ∈ boxFin d n, ‖multiDerivCoeff α (nonlocalCoeff D μ F) k‖ ^ 2 ≤
      r1Const d s MB Λ α * H :=
    nonlocal_R1_fixed s hs m MB Λ D hDs hM μ hμ' hΛ α hαm F hF _
  have hr : r1Const d s MB Λ α ≤ ∑ α' ∈ multiIndices d m, r1Const d s MB Λ α' :=
    Finset.single_le_sum (f := fun α' => r1Const d s MB Λ α') (fun α' _ => r1Const_nonneg s MB Λ α') hα
  have hH0 : 0 ≤ H := hsNormSq_nonnegE _ _
  have e : bilinForm (wtP α) (nonlocalCoeff D μ F) F =
      ∑ k ∈ boxFin d n, conj (multiDerivCoeff α F k) * multiDerivCoeff α (nonlocalCoeff D μ F) k :=
    bilinForm_weight_eq α _ F hF
  calc |(bilinForm (wtP α) (nonlocalCoeff D μ F) F).re|
      ≤ ‖bilinForm (wtP α) (nonlocalCoeff D μ F) F‖ := Complex.abs_re_le_norm _
    _ ≤ ∑ k ∈ boxFin d n, ‖multiDerivCoeff α F k‖ * ‖multiDerivCoeff α (nonlocalCoeff D μ F) k‖ := by
        rw [e]
        refine (norm_sum_le _ _).trans (le_of_eq (Finset.sum_congr rfl fun k _ => ?_))
        rw [norm_mul, RCLike.norm_conj]
    _ ≤ ∑ k ∈ boxFin d n, (‖multiDerivCoeff α F k‖ ^ 2 +
          ‖multiDerivCoeff α (nonlocalCoeff D μ F) k‖ ^ 2) / 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        nlinarith [sq_nonneg (‖multiDerivCoeff α F k‖ - ‖multiDerivCoeff α (nonlocalCoeff D μ F) k‖)]
    _ = (∑ k ∈ boxFin d n, ‖multiDerivCoeff α F k‖ ^ 2 +
          ∑ k ∈ boxFin d n, ‖multiDerivCoeff α (nonlocalCoeff D μ F) k‖ ^ 2) / 2 := by
        rw [← Finset.sum_div, Finset.sum_add_distrib]
    _ ≤ (H + r1Const d s MB Λ α * H) / 2 := by linarith
    _ ≤ _ := by nlinarith

/-! ### Assembly over the regimes -/

theorem H1_sub_nonneg {n : ℕ} (m : ℕ) (F : Coeff d) (hF : IsTrigPoly n F) :
    0 ≤ hsNormSq ((m : ℝ) + 1) F - hsNormSq (m : ℝ) F := by
  rw [← sum_mw_gradDerivL2Sq m F hF]
  exact Finset.sum_nonneg fun α _ => mul_nonneg (Nat.cast_nonneg _) (gradDerivL2Sq_nonneg α F)

theorem neg_sum_le_of_abs (m : ℕ) (N : (Fin d → ℕ) → ℝ) (CR H : ℝ)
    (h : ∀ α ∈ multiIndices d m, |N α| ≤ CR * H) :
    -∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) * N α ≤
      (∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ)) * CR * H := by
  rw [mul_assoc, Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun α hα => ?_
  have h0 : (0 : ℝ) ≤ multinomialWeight m α := Nat.cast_nonneg _
  rw [neg_mul_eq_mul_neg]
  exact mul_le_mul_of_nonneg_left ((neg_le_abs _).trans (h α hα)) h0

theorem neg_sum_le_of_R2 (m : ℕ) (N W : (Fin d → ℕ) → ℝ) (CN H : ℝ)
    (hW : ∀ α ∈ multiIndices d m, 0 ≤ W α)
    (h : ∀ α ∈ multiIndices d m, -N α ≤ -(1 / 2) * W α + CN * H) :
    -∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) * N α ≤
      -(1 / 2) * ∑ α ∈ multiIndices d m, W α +
        (∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ)) * CN * H := by
  rw [mul_assoc, Finset.sum_mul, Finset.mul_sum, ← Finset.sum_neg_distrib, ← Finset.sum_add_distrib]
  refine Finset.sum_le_sum fun α hα => ?_
  have h1 : (1 : ℝ) ≤ multinomialWeight m α := by exact_mod_cast one_le_multinomialWeight m α hα
  have h0 : (0 : ℝ) ≤ multinomialWeight m α := Nat.cast_nonneg _
  rw [neg_mul_eq_mul_neg]
  calc (multinomialWeight m α : ℝ) * -N α ≤ (multinomialWeight m α : ℝ) * (-(1 / 2) * W α + CN * H) :=
        mul_le_mul_of_nonneg_left (h α hα) h0
    _ = (multinomialWeight m α : ℝ) * (-(1 / 2) * W α) + (multinomialWeight m α : ℝ) * (CN * H) := by ring
    _ ≤ -(1 / 2) * W α + (multinomialWeight m α : ℝ) * (CN * H) := by
        have := hW α hα
        nlinarith

/-- The statement of `energy_form_estimate` for a given regime and constant. -/
def FormEst (d : ℕ) (s : ℝ) (m : ℕ) (R : Regime) (MB Λ VB : ℝ) (C : ℝ) : Prop :=
  ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
    (_ : AdjointData s m R MB Λ VB D ν₀ T μ)
    (lam : Fin d → ℝ) (q : Fin d → Euc d) (_ : R.IsR2 → IsSymDiag D.M lam q)
    (r : ℝ) (_ : r ∈ Set.Icc 0 T) (n : ℕ) (F : Coeff d) (_ : IsRealCoeff F) (_ : IsTrigPoly n F),
    (R.IsR2 → WeightedDissipationFinite D m q (μ r) F) ∧
    (hsInner (m : ℝ) (forwardGen D (μ r) F) F).re ≤
      energyRHS R (R.lambdaM C ν₀ (thetaOrder d s)) D m lam q (μ r) F

theorem formEst_R1 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ FormEst d s m .R1 MB Λ VB C := by
  by_cases hs : s ≤ (d : ℝ) - 2
  · obtain ⟨CT, hCT0, hCT⟩ := transport_part hd s hs0 hsd m MB Λ VB
    obtain ⟨CR, hCR0, hCR⟩ := r1_part s hs m MB Λ
    have hc0 := sum_mw_pos (d := d) m
    refine ⟨(∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ)) * (CT + CR) + 1, by positivity, ?_⟩
    intro D ν₀ T μ A lam q _ r hr n F hFr hF
    refine ⟨fun h => absurd h (by simp [Regime.IsR2]), ?_⟩
    have hp := A.hμ.prob r hr
    have hk := A.hμ.smooth r hr
    have hb := A.hμ.bound r hr
    have hbasic := re_hsInner_le_basic D (μ r) m F hF CT
      (hCT D A.hs A.hM A.hV (μ r) hp hk hb n F hFr hF)
    have hNl := neg_sum_le_of_abs m _ CR (hsNormSq (m : ℝ) F)
      (hCR D A.hs A.hM (μ r) hk hb n F hF)
    have hX := H1_sub_nonneg m F hF
    have hH := hsNormSq_nonnegE (m : ℝ) F
    have hν := D.hβ
    have h1 : 0 ≤ (D.invβ / 2) * (hsNormSq ((m : ℝ) + 1) F - hsNormSq (m : ℝ) F) :=
      mul_nonneg (by positivity) hX
    have hno : ¬ Regime.R1.IsR2 := by simp [Regime.IsR2]
    simp only [energyRHS, Regime.lambdaM]
    rw [if_neg hno, sub_zero]
    have h2 : (∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ)) * CT * hsNormSq (m : ℝ) F +
        (∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ)) * CR * hsNormSq (m : ℝ) F ≤
        ((∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ)) * (CT + CR) + 1) *
          hsNormSq (m : ℝ) F := by nlinarith
    have h3 : -(D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α F =
        -((D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α F) := by ring
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro D ν₀ T μ A
    exact absurd A.regime hs

theorem formEst_R2_gen (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (Rg : Regime)
    (hR2 : Rg.IsR2) (hlam : ∀ C ν θ, Rg.lambdaM C ν θ = C) (MB Λ VB : ℝ)
    (Extra : DynData d → (Torus d → ℝ) → Prop)
    (hExtra : ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ),
      AdjointData s m Rg MB Λ VB D ν₀ T μ → ∀ r ∈ Set.Icc 0 T, Extra D (μ r))
    (CN : ℝ)
    (hN : ∀ (D : DynData d), D.s = s → MatBound MB D.M → Torus.SymNonpos D.M →
      ∀ (lam : Fin d → ℝ) (q : Fin d → Euc d), IsSymDiag D.M lam q →
      ∀ μ : Torus d → ℝ, IsProbDensity μ → Torus.IsCk (m + 3) μ → Torus.cbNorm (m + 3) μ ≤ Λ →
      Extra D μ → ∀ (n : ℕ) (F : Coeff d), IsRealCoeff F → IsTrigPoly n F →
      ∀ α ∈ multiIndices d m,
        (∀ l, Summable fun k => symbolK d D.s (q l) k *
          ‖mulCoeff (coeffOf fun x => Real.sqrt (μ x)) (multiDerivCoeff α F) k‖ ^ 2) ∧
        -(bilinForm (wtP α) (nonlocalCoeff D μ F) F).re ≤
          -(1 / 2) * ∑ l, lam l * quadForm (symbolK d D.s (q l))
              (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) (multiDerivCoeff α F)) +
            CN * hsNormSq (m : ℝ) F) :
    ∃ C : ℝ, 0 < C ∧ FormEst d s m Rg MB Λ VB C := by
  obtain ⟨CT, hCT0, hCT⟩ := transport_part hd s hs0 hsd m MB Λ VB
  have hc0 := sum_mw_pos (d := d) m
  refine ⟨(∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ)) * (CT + max CN 0) + 1,
    by positivity, ?_⟩
  intro D ν₀ T μ A lam q hq r hr n F hFr hF
  have hdiag := hq hR2
  have hsn := regime_symNonpos hR2 A.regime
  have hp := A.hμ.prob r hr
  have hk := A.hμ.smooth r hr
  have hb := A.hμ.bound r hr
  have hall := fun α hα => hN D A.hs A.hM hsn lam q hdiag (μ r) hp hk hb (hExtra D ν₀ T μ A r hr)
    n F hFr hF α hα
  refine ⟨fun _ α hα => (hall α hα).1, ?_⟩
  have hbasic := re_hsInner_le_basic D (μ r) m F hF CT
    (hCT D A.hs A.hM A.hV (μ r) hp hk hb n F hFr hF)
  set W : (Fin d → ℕ) → ℝ := fun α => ∑ l, lam l * quadForm (symbolK d D.s (q l))
    (mulCoeff (coeffOf fun x => Real.sqrt (μ r x)) (multiDerivCoeff α F)) with hW
  have hW0 : ∀ α ∈ multiIndices d m, 0 ≤ W α := fun α _ =>
    Finset.sum_nonneg fun l _ => mul_nonneg (hdiag.nonneg l)
      (quadForm_symbolK_nonneg hd D.hs0 D.hsd _ _)
  have hH := hsNormSq_nonnegE (m : ℝ) F
  have hNl := neg_sum_le_of_R2 m (fun α => (bilinForm (wtP α) (nonlocalCoeff D (μ r) F) F).re) W
    (max CN 0) (hsNormSq (m : ℝ) F) hW0 (fun α hα => by
      refine (hall α hα).2.trans ?_
      have := mul_le_mul_of_nonneg_right (le_max_left CN 0) hH
      simp only [hW]
      linarith)
  have hX := H1_sub_nonneg m F hF
  have h1 : 0 ≤ (D.invβ / 2) * (hsNormSq ((m : ℝ) + 1) F - hsNormSq (m : ℝ) F) :=
    mul_nonneg (by have := D.hβ; positivity) hX
  have h2 : (∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ)) * CT * hsNormSq (m : ℝ) F +
      (∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ)) * max CN 0 * hsNormSq (m : ℝ) F ≤
      ((∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ)) * (CT + max CN 0) + 1) *
        hsNormSq (m : ℝ) F := by nlinarith
  have hwd : weightedDissipation D m lam q (μ r) F = ∑ α ∈ multiIndices d m, W α := rfl
  simp only [energyRHS, hlam]
  rw [if_pos hR2, hwd]
  linarith

theorem formEst_R2a (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ FormEst d s m .R2a MB Λ VB C := by
  by_cases hs1 : (d : ℝ) - 2 < s
  · obtain ⟨C2, hC2⟩ := nonlocal_R2_bound hd s hs1 hsd m MB Λ 1 one_pos
    refine formEst_R2_gen hd s hs0 hsd m .R2a trivial (fun _ _ _ => rfl) MB Λ VB
      (fun D _ => Torus.symPart D.M = 0) (fun D ν₀ T μ A r hr => A.regime.2) (max C2 0) ?_
    intro D hs hM hsn lam q hdiag μ hp hk hb hex n F hFr hF α hα
    obtain ⟨h1, h2⟩ := hC2 D hs hM hsn lam q hdiag μ hp hk hb (Or.inl hex) α hα n F hFr hF
    refine ⟨h1, h2.trans ?_⟩
    have := mul_le_mul_of_nonneg_right (le_max_left C2 0) (hsNormSq_nonnegE (m : ℝ) F)
    rw [if_pos hex]
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro D ν₀ T μ A
    exact absurd A.regime.1 hs1

theorem formEst_R2b (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (lam0 MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ FormEst d s m (.R2b lam0) MB Λ VB C := by
  by_cases hc : (d : ℝ) - 2 < s ∧ 0 < lam0
  · obtain ⟨hs1, hl0⟩ := hc
    obtain ⟨C2, hC2⟩ := nonlocal_R2_bound hd s hs1 hsd m MB Λ lam0 hl0
    refine formEst_R2_gen hd s hs0 hsd m (.R2b lam0) trivial (fun _ _ _ => rfl) MB Λ VB
      (fun _ μ' => ∀ x, lam0 ≤ μ' x) (fun D ν₀ T μ A r hr => A.regime.2.2.2 r hr)
      (max C2 0 * (1 + lam0⁻¹)) ?_
    intro D hs hM hsn lam q hdiag μ hp hk hb hex n F hFr hF α hα
    obtain ⟨h1, h2⟩ := hC2 D hs hM hsn lam q hdiag μ hp hk hb (Or.inr hex) α hα n F hFr hF
    refine ⟨h1, h2.trans ?_⟩
    have hH := hsNormSq_nonnegE (m : ℝ) F
    have hite : (1 + (if Torus.symPart D.M = 0 then (0 : ℝ) else lam0⁻¹)) ≤ 1 + lam0⁻¹ := by
      split_ifs
      · have : 0 ≤ lam0⁻¹ := by positivity
        linarith
      · exact le_rfl
    have h3 : C2 * (1 + (if Torus.symPart D.M = 0 then (0 : ℝ) else lam0⁻¹)) ≤
        max C2 0 * (1 + lam0⁻¹) := by
      have hpos : 0 ≤ 1 + (if Torus.symPart D.M = 0 then (0 : ℝ) else lam0⁻¹) := by
        split_ifs
        · norm_num
        · have : 0 ≤ lam0⁻¹ := by positivity
          linarith
      calc _ ≤ max C2 0 * (1 + (if Torus.symPart D.M = 0 then (0 : ℝ) else lam0⁻¹)) :=
            mul_le_mul_of_nonneg_right (le_max_left _ _) hpos
        _ ≤ _ := mul_le_mul_of_nonneg_left hite (le_max_right _ _)
    have := mul_le_mul_of_nonneg_right h3 hH
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro D ν₀ T μ A
    exact absurd ⟨A.regime.1, A.regime.2.2.1⟩ hc

theorem formEst_R2c (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ FormEst d s m .R2c MB Λ VB C := by
  by_cases hc : (d : ℝ) - 2 < s ∧ s ≤ (d : ℝ) - 1
  · obtain ⟨hs1, hs2⟩ := hc
    obtain ⟨C2, hC2⟩ := nonlocal_R2c_bound hd s hs1 hs2 m MB Λ
    refine formEst_R2_gen hd s hs0 hsd m .R2c trivial (fun _ _ _ => rfl) MB Λ VB
      (fun _ _ => True) (fun _ _ _ _ _ _ _ => trivial) (max C2 0) ?_
    intro D hs hM hsn lam q hdiag μ hp hk hb _ n F hFr hF α hα
    obtain ⟨h1, h2⟩ := hC2 D hs hM hsn lam q hdiag μ hp hk hb α hα n F hFr hF
    refine ⟨h1, h2.trans ?_⟩
    have := mul_le_mul_of_nonneg_right (le_max_left C2 0) (hsNormSq_nonnegE (m : ℝ) F)
    linarith
  · refine ⟨1, one_pos, ?_⟩
    intro D ν₀ T μ A
    exact absurd ⟨A.regime.1, A.regime.2.1⟩ hc

theorem neg_sum_le_of_abs' (m : ℕ) (N : (Fin d → ℕ) → ℝ) (Bd : ℝ)
    (h : ∀ α ∈ multiIndices d m, |N α| ≤ Bd) :
    -∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) * N α ≤
      (∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ)) * Bd := by
  rw [Finset.sum_mul, ← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun α hα => ?_
  have h0 : (0 : ℝ) ≤ multinomialWeight m α := Nat.cast_nonneg _
  rw [neg_mul_eq_mul_neg]
  exact mul_le_mul_of_nonneg_left ((neg_le_abs _).trans (h α hα)) h0

theorem formEst_R3 (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ FormEst d s m .R3 MB Λ VB C := by
  by_cases hs1 : (d : ℝ) - 2 < s
  · obtain ⟨CT, hCT0, hCT⟩ := transport_part hd s hs0 hsd m MB Λ VB
    obtain ⟨C3, hC3⟩ := nonlocal_R3_bound hd s hs1 hsd m MB Λ
    have hc0 := sum_mw_pos (d := d) m
    set c₀ : ℝ := ∑ α ∈ multiIndices d m, (multinomialWeight m α : ℝ) with hc₀
    set e : ℝ := thetaOrder d s / (2 - thetaOrder d s) with he
    have hθ0 : 0 < thetaOrder d s := by unfold thetaOrder; linarith
    have hθ2 : 0 < 2 - thetaOrder d s := by unfold thetaOrder; linarith
    have he0 : 0 ≤ e := div_nonneg hθ0.le hθ2.le
    have hm1 : (0 : ℝ) < ((m : ℝ) + 1) ^ d := by positivity
    set δ : ℝ := 2 * ((m : ℝ) + 1) ^ d / c₀ with hδ
    have hδ0 : 0 < δ := by positivity
    set B0 : ℝ := c₀ * max C3 0 * δ ^ (-e) with hB0
    have hB00 : 0 ≤ B0 := by positivity
    have hA0 : 0 ≤ c₀ * CT + 1 / 2 := by positivity
    refine ⟨c₀ * CT + 1 / 2 + B0 + 1, by positivity, ?_⟩
    intro D ν₀ T μ A lam q _ r hr n F hFr hF
    refine ⟨fun h => absurd h (by simp [Regime.IsR2]), ?_⟩
    obtain ⟨-, hν₀, hνν⟩ := A.regime
    have hp := A.hμ.prob r hr
    have hk := A.hμ.smooth r hr
    have hb := A.hμ.bound r hr
    have hbasic := re_hsInner_le_basic D (μ r) m F hF CT
      (hCT D A.hs A.hM A.hV (μ r) hp hk hb n F hFr hF)
    set m₁ : ℝ := min ν₀ 1 with hm₁
    have hm₁0 : 0 < m₁ := lt_min hν₀ one_pos
    have hm₁1 : m₁ ≤ 1 := min_le_right _ _
    have hm₁ν : m₁ ≤ ν₀ := min_le_left _ _
    set ν' : ℝ := δ * m₁ with hν'
    have hν'0 : 0 < ν' := mul_pos hδ0 hm₁0
    set H := hsNormSq (m : ℝ) F with hH
    set H1 := hsNormSq ((m : ℝ) + 1) F with hH1
    have hH0 : 0 ≤ H := hsNormSq_nonnegE _ _
    have hX := H1_sub_nonneg m F hF
    have hNl := neg_sum_le_of_abs' m _ (ν' / (4 * ((m : ℝ) + 1) ^ d) * H1 + C3 * ν' ^ (-e) * H)
      (fun α hα => hC3 D A.hs A.hM (μ r) hk hb ν' hν'0 α hα n F hFr hF)
    -- the arithmetic
    have hκ : c₀ * (ν' / (4 * ((m : ℝ) + 1) ^ d)) = m₁ / 2 := by
      rw [hν', hδ]; field_simp; norm_num
    have hpow : ν' ^ (-e) ≤ δ ^ (-e) * (1 + ν₀ ^ (-e)) := by
      rw [hν', Real.mul_rpow hδ0.le hm₁0.le]
      refine mul_le_mul_of_nonneg_left ?_ (Real.rpow_nonneg hδ0.le _)
      have hν0e : 0 ≤ ν₀ ^ (-e) := Real.rpow_nonneg hν₀.le _
      rcases le_total ν₀ 1 with h | h
      · rw [hm₁, min_eq_left h]; linarith
      · rw [hm₁, min_eq_right h, Real.one_rpow]; linarith
    have hpe : 0 ≤ ν₀ ^ (-e) := Real.rpow_nonneg hν₀.le _
    have hE : c₀ * (C3 * ν' ^ (-e) * H) ≤ B0 * (1 + ν₀ ^ (-e)) * H := by
      have h1 : C3 * ν' ^ (-e) ≤ max C3 0 * (δ ^ (-e) * (1 + ν₀ ^ (-e))) := by
        calc C3 * ν' ^ (-e) ≤ max C3 0 * ν' ^ (-e) :=
              mul_le_mul_of_nonneg_right (le_max_left _ _) (Real.rpow_nonneg hν'0.le _)
          _ ≤ _ := mul_le_mul_of_nonneg_left hpow (le_max_right _ _)
      calc c₀ * (C3 * ν' ^ (-e) * H) = c₀ * (C3 * ν' ^ (-e)) * H := by ring
        _ ≤ c₀ * (max C3 0 * (δ ^ (-e) * (1 + ν₀ ^ (-e)))) * H :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hc0.le) hH0
        _ = _ := by rw [hB0]; ring
    have hβ : 0 ≤ D.invβ := D.hβ
    have h1 : (m₁ / 2) * (H1 - H) ≤ (D.invβ / 2) * (H1 - H) :=
      mul_le_mul_of_nonneg_right (by linarith) hX
    have h2 : (m₁ / 2) * H ≤ (1 / 2) * H := mul_le_mul_of_nonneg_right (by linarith) hH0
    have h3 : (c₀ * CT + 1 / 2 + B0 * (1 + ν₀ ^ (-e))) * H ≤
        (c₀ * CT + 1 / 2 + B0 + 1) * (1 + ν₀ ^ (-e)) * H := by
      refine mul_le_mul_of_nonneg_right ?_ hH0
      nlinarith
    have h4 : c₀ * (ν' / (4 * ((m : ℝ) + 1) ^ d) * H1) = (m₁ / 2) * (H1 - H) + (m₁ / 2) * H := by
      rw [← mul_assoc, hκ]; ring
    have hno : ¬ Regime.R3.IsR2 := by simp [Regime.IsR2]
    simp only [energyRHS, Regime.lambdaM]
    rw [if_neg hno, sub_zero]
    have h5 : c₀ * (ν' / (4 * ((m : ℝ) + 1) ^ d) * H1 + C3 * ν' ^ (-e) * H) =
        (m₁ / 2) * (H1 - H) + (m₁ / 2) * H + c₀ * (C3 * ν' ^ (-e) * H) := by
      rw [mul_add, h4]
    have h6 : -(D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α F =
        -((D.invβ / 2) * ∑ α ∈ multiIndices d m, gradDerivL2Sq α F) := by ring
    nlinarith
  · refine ⟨1, one_pos, ?_⟩
    intro D ν₀ T μ A
    exact absurd A.regime.1 hs1

/-! ### The theorems -/

/-- **Form estimate** (the engine of Prop 3.13 for the Galerkin route; all `m ∈ ℕ`, `m = 0`
included): under the hypotheses of Prop 3.9 at level `m` there is `C` (depending only on
`d, s, m, |M|, Λ, ‖V‖_{C^{m+3}}` and, in R2b, `λ₀`) such that for every real trigonometric
polynomial `F` and every time `r ∈ [0,T]`
(the diagonalisation `S = -∑ λ_l q_l q_lᵀ`, which exists only when `S ≤ 0`, is required only in
regime R2, where `S ≤ 0` holds; in R1/R3 `S` is arbitrary and `lam, q` play no role),
`Re ⟨𝓛^r F, F⟩_{H^m} ≤ Λ_m ‖F‖²_{H^m} - (ν/2)∑_{|α|≤m}‖∇∂^αF‖² - ½ 1_{R2} ∑_{|α|≤m}∑_l λ_l B_l(√μ^r∂^αF, √μ^r∂^αF)`
with `Λ_m = Regime.lambdaM R C ν₀ θ` (`B:eq:LambdaM`), and the retained forms are finite. -/
theorem energy_form_estimate (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ)
    (R : Regime) (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
      (_ : AdjointData s m R MB Λ VB D ν₀ T μ)
      (lam : Fin d → ℝ) (q : Fin d → Euc d) (_ : R.IsR2 → IsSymDiag D.M lam q)
      (r : ℝ) (_ : r ∈ Set.Icc 0 T) (n : ℕ) (F : Coeff d) (_ : IsRealCoeff F) (_ : IsTrigPoly n F),
      (R.IsR2 → WeightedDissipationFinite D m q (μ r) F) ∧
      (hsInner m (forwardGen D (μ r) F) F).re ≤
        energyRHS R (R.lambdaM C ν₀ (thetaOrder d s)) D m lam q (μ r) F := by
  have key : ∃ C : ℝ, 0 < C ∧ FormEst d s m R MB Λ VB C := by
    cases R with
    | R1 => exact formEst_R1 hd s hs0 hsd m MB Λ VB
    | R2a => exact formEst_R2a hd s hs0 hsd m MB Λ VB
    | R2b lam0 => exact formEst_R2b hd s hs0 hsd m lam0 MB Λ VB
    | R2c => exact formEst_R2c hd s hs0 hsd m MB Λ VB
    | R3 => exact formEst_R3 hd s hs0 hsd m MB Λ VB
  obtain ⟨C, hC, h⟩ := key
  exact ⟨C, hC, h⟩

/-- Proposition 3.13 `B:prop:energy-torus` (lines 1865–1871), literal form: under the hypotheses of
Prop 3.9 (level `m ≥ 1`), for a solution `F` of `B:eq:adjoint-forward` regular enough for the
derivative to exist (`F ∈ C([0,t];H^{m+2})`), for all `τ ∈ [0,t]`,
`d/dτ ½‖F(τ)‖²_{H^m} ≤ Λ_m‖F(τ)‖²_{H^m} - (ν/2)∑_{|α|≤m}‖∇∂^αF‖²_{L²} - ½∑_{|α|≤m}∑_l λ_l B_l(√μ∂^αF,√μ∂^αF)`
(`B:eq:energy-torus`), the last sum present only in regime R2; `Λ_m` as in `B:eq:LambdaM`, with the
same constant `C` as in `energy_form_estimate`.  In particular `B:eq:adjoint-torus-bound` follows by
Grönwall (`adjoint_torus_bound_of_regular` in `WellPosed.lean`). -/
theorem energy_torus (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (R : Regime) (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
      (_ : AdjointData s m R MB Λ VB D ν₀ T μ)
      (lam : Fin d → ℝ) (q : Fin d → Euc d) (_ : R.IsR2 → IsSymDiag D.M lam q)
      (t : ℝ) (_ : t ∈ Set.Ioc 0 T) (φc : Coeff d) (F : ℝ → Coeff d)
      (_ : IsForwardSolution D μ t φc F) (_ : ContinuousInHs (m + 2) F t)
      (_ : ∀ τ ∈ Set.Icc 0 t, IsRealCoeff (F τ)),
      ∀ τ ∈ Set.Icc 0 t,
        (R.IsR2 → WeightedDissipationFinite D m q (μ (t - τ)) (F τ)) ∧
        HasDerivWithinAt (fun τ' => (1 / 2) * hsNormSq m (F τ'))
          (hsInner m (forwardGen D (μ (t - τ)) (F τ)) (F τ)).re (Set.Icc 0 t) τ ∧
        (hsInner m (forwardGen D (μ (t - τ)) (F τ)) (F τ)).re ≤
          energyRHS R (R.lambdaM C ν₀ (thetaOrder d s)) D m lam q (μ (t - τ)) (F τ) := by
  obtain ⟨C, hC, h⟩ := energy_form_estimate hd s hs0 hsd m R MB Λ VB
  refine ⟨C, hC, ?_⟩
  intro D ν₀ T μ A lam q hq t ht φc F hF hcont hreal τ hτ
  have hr : t - τ ∈ Set.Icc 0 T := ET.tsub_mem_Icc ht hτ
  have hderiv := ET.energy_deriv hd s hs0 hsd m A ht hF hcont τ hτ
  have hG : MemHs ((m : ℝ) + 2) (F τ) := hcont.1 τ hτ
  have hform := fun n : ℕ => h D ν₀ T μ A lam q hq (t - τ) hr n (truncCoeff n (F τ))
    (ET.isRealCoeff_truncCoeff (hreal τ hτ) n) (isTrigPoly_truncCoeff n (F τ))
  by_cases hR : R.IsR2
  · have hlam : ∀ l, 0 ≤ lam l := (hq hR).nonneg
    have key := ET.form_limit_R2 hd s hs0 hsd m MB Λ VB D A.hs A.hM A.hV (μ (t - τ))
      (A.hμ.prob _ hr) (A.hμ.smooth _ hr) (A.hμ.bound _ hr) lam hlam q
      (R.lambdaM C ν₀ (thetaOrder d s)) (F τ) hG (fun n => by
        refine ⟨(hform n).1 hR, ?_⟩
        have := (hform n).2
        simpa only [energyRHS, if_pos hR] using this)
    refine ⟨fun _ => key.1, hderiv, ?_⟩
    simpa only [energyRHS, if_pos hR] using key.2
  · refine ⟨fun h' => absurd h' hR, hderiv, ?_⟩
    have key := ET.form_limit_nonR2 hd s hs0 hsd m MB Λ VB D A.hs A.hM A.hV (μ (t - τ))
      (A.hμ.prob _ hr) (A.hμ.smooth _ hr) (A.hμ.bound _ hr)
      (R.lambdaM C ν₀ (thetaOrder d s)) (F τ) hG (fun n => by
        have := (hform n).2
        simpa only [energyRHS, if_neg hR, sub_zero] using this)
    simpa only [energyRHS, if_neg hR, sub_zero] using key

/-- Proposition 3.14 `B:prop:R2c` (lines 1942–1944), energy half: for `d-2 < s ≤ d-1` (`0 < θ ≤ 1`),
`S ≤ 0`, under `B:eq:coeff-hypothesis` but **without** any lower bound on `μ`, the form estimate
holds with `Λ_m = C` uniformly in `β ∈ (0,∞]` (constant independent of `β` and of `inf μ`), and
with no dissipation retained (line 1951: "no dissipation retained and no use of `inf μ`"). -/
theorem energy_form_estimate_R2c (hd : 1 ≤ d) (s : ℝ) (hs1 : (d : ℝ) - 2 < s)
    (hs2 : s ≤ (d : ℝ) - 1) (m : ℕ) (MB Λ VB : ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (D : DynData d) (ν₀ T : ℝ) (μ : ℝ → Torus d → ℝ)
      (_ : AdjointData s m .R2c MB Λ VB D ν₀ T μ)
      (r : ℝ) (_ : r ∈ Set.Icc 0 T) (n : ℕ) (F : Coeff d) (_ : IsRealCoeff F) (_ : IsTrigPoly n F),
      (hsInner m (forwardGen D (μ r) F) F).re ≤ C * hsNormSq m F := by
  by_cases hs0 : 0 ≤ s
  · have hsd : s < d := by linarith
    obtain ⟨C, hC, h⟩ := formEst_R2c hd s hs0 hsd m MB Λ VB
    refine ⟨C, hC, ?_⟩
    intro D ν₀ T μ A r hr n F hFr hF
    obtain ⟨lam, q, hdiag⟩ := exists_symDiag (regime_symNonpos (R := .R2c) trivial A.regime)
    have h1 := (h D ν₀ T μ A lam q (fun _ => hdiag) r hr n F hFr hF).2
    refine h1.trans ?_
    exact energyRHS_le hd .R2c _ D m lam q (fun _ l => hdiag.nonneg l) (μ r) F
  · refine ⟨1, one_pos, ?_⟩
    intro D ν₀ T μ A
    exact absurd (A.hs ▸ D.hs0) hs0


end HRS.PDE
