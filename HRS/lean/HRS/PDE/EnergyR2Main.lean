import HRS.PDE.EnergyR2K
import HRS.PDE.EnergyR2Cmp

/-!
# Regime R2: assembly of the per-multi-index bounds
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.R2Aux

variable {d : ℕ}

theorem binomW_zero (α : Fin d → ℕ) : binomW α 0 = 1 := by
  simp [binomW]

theorem zero_mem_leibnizSet (α : Fin d → ℕ) : (0 : Fin d → ℕ) ∈ leibnizSet α :=
  mem_leibnizSet.mpr fun _ => Nat.zero_le _

/-- The Leibniz split: the top term plus the commutator terms (real-part form). -/
theorem bilin_split_re {n : ℕ} (D : DynData d) (μ : Torus d → ℝ) (α : Fin d → ℕ) (F : Coeff d)
    (hF : IsTrigPoly n F) (b : (Fin d → ℕ) → ℝ)
    (hb : ∀ β ∈ (leibnizSet α).erase 0, -(PP D μ α F n β).re ≤ b β) :
    -(bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
        (nonlocalCoeff D μ F) F).re ≤
      -(PP D μ α F n 0).re + ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ) * b β := by
  rw [re_bilin_leibniz D μ α F hF, ← Finset.add_sum_erase _ _ (zero_mem_leibnizSet α),
    binomW_zero]
  simp only [Nat.cast_one, one_mul, neg_add]
  refine add_le_add le_rfl ?_
  rw [← Finset.sum_neg_distrib]
  refine Finset.sum_le_sum fun β hβ => ?_
  have h3 : (0 : ℝ) ≤ (binomW α β : ℝ) := Nat.cast_nonneg _
  have := mul_le_mul_of_nonneg_left (hb β hβ) h3
  linarith

/-- The Leibniz split: the top term plus the commutator terms. -/
theorem bilin_split_bound {n : ℕ} (D : DynData d) (μ : Torus d → ℝ) (α : Fin d → ℕ) (F : Coeff d)
    (hF : IsTrigPoly n F) (b : (Fin d → ℕ) → ℝ)
    (hb : ∀ β ∈ (leibnizSet α).erase 0, ‖PP D μ α F n β‖ ≤ b β) :
    -(bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
        (nonlocalCoeff D μ F) F).re ≤
      -(PP D μ α F n 0).re + ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ) * b β :=
  bilin_split_re D μ α F hF b fun β hβ =>
    ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans (hb β hβ)

theorem PP_eq_sum {n : ℕ} (D : DynData d) (μ : Torus d → ℝ) (α : Fin d → ℕ) (F : Coeff d)
    (β : Fin d → ℕ) :
    PP D μ α F n β = ∑ i, ∑ j, ((D.M j i : ℝ) : ℂ) * ∑ k ∈ boxFin d n,
      conj (multiDerivCoeff α F k) * (Ssym d D.s i k *
        mulCoeff (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) (derivCoeff j F)) k) := by
  unfold PP ct
  simp_rw [gradRieszCoeff_apply, Finset.mul_sum]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem PP_zero_eq {n : ℕ} (D : DynData d) (μ : Torus d → ℝ) (α : Fin d → ℕ) (F : Coeff d) :
    PP D μ α F n 0 = ∑ k ∈ boxFin d n, conj (multiDerivCoeff α F k) *
      nonlocalCoeff D μ (multiDerivCoeff α F) k := by
  unfold PP
  exact Finset.sum_congr rfl fun k _ => by rw [ct_zero]

/-- The sum of the binomial weights of the commutator terms. -/
def binSum (d m : ℕ) : ℝ :=
  ∑ α ∈ multiIndices d m, ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ)

theorem binSum_nonneg (d m : ℕ) : 0 ≤ binSum d m :=
  Finset.sum_nonneg fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _

theorem sum_erase_le_binSum {m : ℕ} {α : Fin d → ℕ} (hα : α ∈ multiIndices d m) :
    ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ) ≤ binSum d m :=
  Finset.single_le_sum (f := fun α : Fin d → ℕ => ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ))
    (fun _ _ => Finset.sum_nonneg fun _ _ => Nat.cast_nonneg _) hα

theorem multiIndices_sum_le {m : ℕ} {α : Fin d → ℕ} (hα : α ∈ multiIndices d m) :
    ∑ i, α i ≤ m := (Finset.mem_filter.mp hα).2

theorem isCk_two_of {m : ℕ} {μ : Torus d → ℝ} (hμ : Torus.IsCk (m + 3) μ) :
    Torus.IsCk 2 μ := hμ.of_le (by exact_mod_cast (by omega : 2 ≤ m + 3))

theorem cbNorm_two_le {m : ℕ} {μ : Torus d → ℝ} {Λ : ℝ} (hΛ : Torus.cbNorm (m + 3) μ ≤ Λ) :
    Torus.cbNorm 2 μ ≤ Λ := (cbNorm_mono' (by omega) μ).trans hΛ

/-- Regime R2c. -/
theorem r2c_main (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hK : R2KernelFacts d s)
    (hs1 : (d : ℝ) - 2 < s) (hs2 : s ≤ (d : ℝ) - 1) (m : ℕ)
    (MB Λ : ℝ) :
    ∃ C : ℝ, ∀ (D : DynData d), D.s = s → MatBound MB D.M →
      ∀ (lam : Fin d → ℝ) (q : Fin d → Euc d), (∀ l, 0 ≤ lam l) → Orthonormal ℝ q →
      (∀ i j, Torus.symPart D.M i j = -∑ l, lam l * q l i * q l j) →
      ∀ (μ : Torus d → ℝ), (∀ x, 0 ≤ μ x) → Torus.IsCk (m + 3) μ → Torus.cbNorm (m + 3) μ ≤ Λ →
      ∀ (α : Fin d → ℕ), α ∈ multiIndices d m →
      ∀ (n : ℕ) (F : Coeff d), IsRealCoeff F → IsTrigPoly n F →
        (∀ l, Summable fun k => symbolK d D.s (q l) k *
          ‖mulCoeff (coeffOf fun x => Real.sqrt (μ x)) (multiDerivCoeff α F) k‖ ^ 2) ∧
        -(bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
            (nonlocalCoeff D μ F) F).re ≤
          -(1 / 2) * ∑ l, lam l * quadForm (symbolK d D.s (q l))
              (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) (multiDerivCoeff α F)) +
            C * hsNormSq m F := by
  have hd1 : 1 ≤ d := hd
  have hsd : s < d := by linarith
  obtain ⟨C₀, hC₀0, hC₀⟩ := leading_bound hd s hs0 hs1 hsd hK MB Λ
  obtain ⟨Cc, hCc0, hCc⟩ := commCrude_term_bound s hs2 m Λ
  set dd : ℝ := (d : ℝ) with hdd
  set MB' : ℝ := |MB| with hMB'
  refine ⟨C₀ + binSum d m * (dd * dd * MB' * Cc), ?_⟩
  intro D hDs hM lam q hlam hq hdiag μ hμ0 hμ hΛ α hα n F hF hFt
  subst hDs
  have hαm := multiIndices_sum_le hα
  have hμ2 := isCk_two_of hμ
  have hΛ2 := cbNorm_two_le hΛ
  set w := multiDerivCoeff α F with hw
  have hwr : IsRealCoeff w := isRealCoeff_multiDerivCoeff hF α
  have hwt : IsTrigPoly n w := isTrigPoly_multiDerivCoeff hFt α
  set N := hsNormSq m F with hN
  have hN0 : 0 ≤ N := hsNormSq_nonnegE _ _
  have hMBnn : 0 ≤ MB' := abs_nonneg _
  have hMBle : ∀ i j, |D.M i j| ≤ MB' := fun i j => (hM i j).trans (le_abs_self _)
  refine ⟨fun l => summable_sqrtK hd1 D.s hs0 hsd (by linarith) (by linarith) μ hμ0 hμ2 (q l) w
    hwr hwt, ?_⟩
  -- the commutator terms
  have hcomm : ∀ β ∈ (leibnizSet α).erase 0,
      ‖PP D μ α F n β‖ ≤ dd * dd * MB' * Cc * N := by
    intro β hβ
    obtain ⟨hβ0, hβl⟩ := Finset.mem_erase.mp hβ
    rw [PP_eq_sum]
    calc ‖∑ i, ∑ j, ((D.M j i : ℝ) : ℂ) * ∑ k ∈ boxFin d n, conj (multiDerivCoeff α F k) *
          (Ssym d D.s i k * mulCoeff (multiDerivCoeff β (coeffOf μ))
            (multiDerivCoeff (α - β) (derivCoeff j F)) k)‖
        ≤ ∑ i : Fin d, ∑ j : Fin d, ‖((D.M j i : ℝ) : ℂ) * ∑ k ∈ boxFin d n,
            conj (multiDerivCoeff α F k) * (Ssym d D.s i k * mulCoeff
              (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) (derivCoeff j F)) k)‖ :=
          (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
      _ ≤ ∑ i : Fin d, ∑ j : Fin d, MB' * (Cc * N) := by
          refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
          rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
          exact mul_le_mul (hMBle j i) (hCc μ hμ hΛ α β hαm hβl hβ0 i j n F hF hFt)
            (norm_nonneg _) hMBnn
      _ = _ := by
          simp [Finset.sum_const, Finset.card_univ, hdd]
          ring
  have hsplit := bilin_split_bound D μ α F hFt (fun _ => dd * dd * MB' * Cc * N) hcomm
  have hlead := hC₀ D rfl hM lam q hlam hq hdiag μ hμ0 hμ2 hΛ2 n w hwr hwt
  rw [PP_zero_eq] at hsplit
  have hN0w : hsNormSq 0 w ≤ N := hsNormSq_zero_multiDeriv_le α m hαm F hFt
  have hX : 0 ≤ ∑ l, lam l * quadForm (symbolK d D.s (q l))
      (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w) :=
    Finset.sum_nonneg fun l _ => mul_nonneg (hlam l)
      (quadForm_symbolK_nonneg' hd1 hs0 hsd _ _)
  have hK : 0 ≤ dd * dd * MB' * Cc * N := by positivity
  have hsum : ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ) * (dd * dd * MB' * Cc * N) ≤
      binSum d m * (dd * dd * MB' * Cc * N) := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_erase_le_binSum hα) hK
  have h1 : C₀ * hsNormSq 0 w ≤ C₀ * N := mul_le_mul_of_nonneg_left hN0w hC₀0
  have h2 : (C₀ + binSum d m * (dd * dd * MB' * Cc)) * N =
      C₀ * N + binSum d m * (dd * dd * MB' * Cc * N) := by ring
  rw [h2]
  linarith

theorem PP_split {n : ℕ} (D : DynData d) (lam : Fin d → ℝ) (q : Fin d → Euc d)
    (hdiag : ∀ i j, Torus.symPart D.M i j = -∑ l, lam l * q l i * q l j)
    (μ : Torus d → ℝ) (α β : Fin d → ℕ) (F : Coeff d) (hF : IsTrigPoly n F) :
    PP D μ α F n β =
      ∑ l, ((lam l : ℝ) : ℂ) * (∑ k ∈ boxFin d n, conj (multiDerivCoeff α F k) *
          (((symbolK d D.s (q l) k : ℝ) : ℂ) * mulCoeff (multiDerivCoeff β (coeffOf μ))
            (multiDerivCoeff (α - β) F) k)) -
      ∑ i, ∑ j, ((D.M j i : ℝ) : ℂ) * (∑ k ∈ boxFin d n, conj (multiDerivCoeff α F k) *
          (Ssym d D.s i k * mulCoeff (derivCoeff j (multiDerivCoeff β (coeffOf μ)))
            (multiDerivCoeff (α - β) F) k)) := by
  have hft : IsTrigPoly n (multiDerivCoeff (α - β) F) := isTrigPoly_multiDerivCoeff hF _
  have hk : ∀ k, ct D μ α F β k =
      ∑ l, ((lam l : ℝ) : ℂ) * (((symbolK d D.s (q l) k : ℝ) : ℂ) *
        mulCoeff (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) F) k) -
      ∑ i, ∑ j, ((D.M j i : ℝ) : ℂ) * (Ssym d D.s i k *
        mulCoeff (derivCoeff j (multiDerivCoeff β (coeffOf μ))) (multiDerivCoeff (α - β) F) k) := by
    intro k
    unfold ct
    simp_rw [multiDerivCoeff_derivCoeff]
    exact ct_decomp D.M D.s lam q hdiag _ _ hft k
  unfold PP
  simp_rw [hk, mul_sub, Finset.sum_sub_distrib, Finset.mul_sum]
  congr 1
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun l _ => Finset.sum_congr rfl fun k _ => by ring
  · rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => Finset.sum_congr rfl fun k _ => by ring

theorem young_aux (a b c : ℝ) (hc : 0 < c) : a * b ≤ c / 2 * a ^ 2 + b ^ 2 / (2 * c) := by
  have h : c / 2 * a ^ 2 + b ^ 2 / (2 * c) - a * b = (c * a - b) ^ 2 / (2 * c) := by
    field_simp
    ring
  have : 0 ≤ (c * a - b) ^ 2 / (2 * c) := by positivity
  linarith

/-- The per-`l` Young step of (ii). -/
theorem lam_step {lam B X c0 R lam0 L : ℝ} (hlam : 0 ≤ lam) (hB : 0 ≤ B) (_hR : 0 ≤ R)
    (hl0 : 0 < lam0) (hc0 : 0 ≤ c0) (hLl : lam ≤ L)
    (hcmp : lam * B ≤ lam * (lam0⁻¹ * X + c0)) :
    lam * (Real.sqrt B * R) ≤ lam * X / 2 + L * (lam0 * c0 / 2 + R ^ 2 / (2 * lam0)) := by
  have h1 := young_aux (Real.sqrt B) R lam0 hl0
  rw [Real.sq_sqrt hB] at h1
  have h2 : lam * (Real.sqrt B * R) ≤ lam * (lam0 / 2 * B + R ^ 2 / (2 * lam0)) :=
    mul_le_mul_of_nonneg_left h1 hlam
  have h3 : lam * (lam0 / 2 * B + R ^ 2 / (2 * lam0)) =
      lam0 / 2 * (lam * B) + lam * (R ^ 2 / (2 * lam0)) := by ring
  have h4 : lam0 / 2 * (lam * B) ≤ lam0 / 2 * (lam * (lam0⁻¹ * X + c0)) :=
    mul_le_mul_of_nonneg_left hcmp (by positivity)
  have h5 : lam0 / 2 * (lam * (lam0⁻¹ * X + c0)) = lam * X / 2 + lam * (lam0 * c0 / 2) := by
    field_simp
  have h6 : lam * (lam0 * c0 / 2 + R ^ 2 / (2 * lam0)) ≤ L * (lam0 * c0 / 2 + R ^ 2 / (2 * lam0)) :=
    mul_le_mul_of_nonneg_right hLl (by positivity)
  nlinarith [h2, h3, h4, h5, h6]

/-- Regime R2 (both R2a and R2b). -/
theorem r2_main (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hK : R2KernelFacts d s)
    (hs1 : (d : ℝ) - 2 < s) (hsd : s < d) (m : ℕ)
    (MB Λ : ℝ) (lam0 : ℝ) (hlam0 : 0 < lam0) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (D : DynData d), D.s = s → MatBound MB D.M →
      ∀ (lam : Fin d → ℝ) (q : Fin d → Euc d), (∀ l, 0 ≤ lam l) → Orthonormal ℝ q →
      (∀ i j, Torus.symPart D.M i j = -∑ l, lam l * q l i * q l j) →
      ∀ (μ : Torus d → ℝ), (∀ x, 0 ≤ μ x) → Torus.IsCk (m + 3) μ → Torus.cbNorm (m + 3) μ ≤ Λ →
      (Torus.symPart D.M = 0 ∨ ∀ x, lam0 ≤ μ x) →
      ∀ (α : Fin d → ℕ), α ∈ multiIndices d m →
      ∀ (n : ℕ) (F : Coeff d), IsRealCoeff F → IsTrigPoly n F →
        (∀ l, Summable fun k => symbolK d D.s (q l) k *
          ‖mulCoeff (coeffOf fun x => Real.sqrt (μ x)) (multiDerivCoeff α F) k‖ ^ 2) ∧
        -(bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
            (nonlocalCoeff D μ F) F).re ≤
          -(1 / 2) * ∑ l, lam l * quadForm (symbolK d D.s (q l))
              (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) (multiDerivCoeff α F)) +
            C * hsNormSq m F := by
  have hd1 : 1 ≤ d := hd
  have hθ0 : 0 ≤ s + 2 - d := by linarith
  have hθ2 : s + 2 - d ≤ 2 := by linarith
  obtain ⟨C₀, hC₀0, hC₀⟩ := leading_bound hd s hs0 hs1 hsd hK MB Λ
  obtain ⟨Cs, hCs0, hCs⟩ := commS_term_bound hd1 s hsd.le m Λ
  obtain ⟨Cρ, hCρ0, hCρ⟩ := Kcomm_term_bound hd1 s hθ0 hθ2 m Λ
  obtain ⟨Cc, hCc0, hCc⟩ := compare_bound hd s hs0 hs1 hsd lam0 hlam0 Λ
  set dd : ℝ := (d : ℝ) with hdd
  set MB' : ℝ := |MB| with hMB'
  set S : ℝ := binSum d m with hS
  have hS0 : 0 ≤ S := binSum_nonneg d m
  have hdd0 : 0 ≤ dd := Nat.cast_nonneg _
  refine ⟨C₀ + dd * dd * MB' * (lam0 * Cc / 2 + S ^ 2 * Cρ / (2 * lam0)) +
    S * (dd * dd * MB' * Cs), by positivity, ?_⟩
  intro D hDs hM lam q hlam hq hdiag μ hμ0 hμ hΛ hcase α hα n F hF hFt
  subst hDs
  have hαm := multiIndices_sum_le hα
  have hμ2 := isCk_two_of hμ
  have hΛ2 := cbNorm_two_le hΛ
  set w := multiDerivCoeff α F with hw
  have hwr : IsRealCoeff w := isRealCoeff_multiDerivCoeff hF α
  have hwt : IsTrigPoly n w := isTrigPoly_multiDerivCoeff hFt α
  set N := hsNormSq m F with hN
  have hN0 : 0 ≤ N := hsNormSq_nonnegE _ _
  have hMBnn : 0 ≤ MB' := abs_nonneg _
  have hMBle : ∀ i j, |D.M i j| ≤ MB' := fun i j => (hM i j).trans (le_abs_self _)
  refine ⟨fun l => summable_sqrtK hd1 D.s hs0 hsd hθ0 hθ2 μ hμ0 hμ2 (q l) w hwr hwt, ?_⟩
  have hN0w : hsNormSq 0 w ≤ N := hsNormSq_zero_multiDeriv_le α m hαm F hFt
  have hlamle : ∀ l, lam l ≤ dd * MB' := fun l =>
    (lam_le hd1 MB D.M hM lam q hdiag hq l).trans (by gcongr; exact le_abs_self _)
  -- the dissipation terms
  have hBw0 : ∀ l, 0 ≤ quadForm (symbolK d D.s (q l)) w :=
    fun l => quadForm_symbolK_nonneg' hd1 hs0 hsd _ _
  have hcmp : ∀ l, lam l * quadForm (symbolK d D.s (q l)) w ≤ lam l *
      (lam0⁻¹ * quadForm (symbolK d D.s (q l))
        (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w) + Cc * N) := by
    intro l
    rcases hcase with h0 | hlow
    · rw [lam_eq_zero D.M lam q hdiag hq h0 l]; simp
    · refine mul_le_mul_of_nonneg_left ?_ (hlam l)
      have := hCc (q l) (hq.1 l).le μ hlow hμ2 hΛ2 n w hwr hwt
      refine this.trans ?_
      have : Cc * hsNormSq 0 w ≤ Cc * N := mul_le_mul_of_nonneg_left hN0w hCc0
      linarith
  set R : ℝ := Real.sqrt (Cρ * N) with hR
  have hR0 : 0 ≤ R := Real.sqrt_nonneg _
  have hR2 : R ^ 2 = Cρ * N := Real.sq_sqrt (by positivity)
  -- commutator terms
  have hcomm : ∀ β ∈ (leibnizSet α).erase 0, -(PP D μ α F n β).re ≤
      ∑ l, lam l * (Real.sqrt (quadForm (symbolK d D.s (q l)) w) * R) +
        dd * dd * MB' * Cs * N := by
    intro β hβ
    obtain ⟨hβ0, hβl⟩ := Finset.mem_erase.mp hβ
    rw [PP_split D lam q hdiag μ α β F hFt]
    have hPK : ∀ l, ‖∑ k ∈ boxFin d n, conj (w k) * (((symbolK d D.s (q l) k : ℝ) : ℂ) *
        mulCoeff (multiDerivCoeff β (coeffOf μ)) (multiDerivCoeff (α - β) F) k)‖ ≤
        Real.sqrt (quadForm (symbolK d D.s (q l)) w) * R := by
      intro l
      refine Kpair_bound (symbolK d D.s (q l)) (symbolK_nonneg' hd1 hs0 hsd (q l)) w _ _ _
        (Real.sqrt_nonneg _) hR0 ?_ ?_
      · rw [Real.sq_sqrt (hBw0 l), quadForm_eq_box _ hwt]
      · rw [hR2]
        exact hCρ (q l) (hq.1 l).le μ hμ hΛ α β hαm hβl hβ0 n F hF hFt
    have hPS : ∀ i j, ‖∑ k ∈ boxFin d n, conj (w k) * (Ssym d D.s i k *
        mulCoeff (derivCoeff j (multiDerivCoeff β (coeffOf μ))) (multiDerivCoeff (α - β) F) k)‖ ≤
        Cs * N := fun i j => hCs μ hμ hΛ α β hαm hβl hβ0 i j n F hF hFt
    refine ((neg_le_abs _).trans (Complex.abs_re_le_norm _)).trans ((norm_sub_le _ _).trans
      (add_le_add ?_ ?_))
    · refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun l _ => ?_)
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (hlam l)]
      exact mul_le_mul_of_nonneg_left (hPK l) (hlam l)
    · calc ‖∑ i, ∑ j, ((D.M j i : ℝ) : ℂ) * (∑ k ∈ boxFin d n, conj (w k) * (Ssym d D.s i k *
            mulCoeff (derivCoeff j (multiDerivCoeff β (coeffOf μ))) (multiDerivCoeff (α - β) F) k))‖
          ≤ ∑ i : Fin d, ∑ j : Fin d, ‖((D.M j i : ℝ) : ℂ) * (∑ k ∈ boxFin d n, conj (w k) *
              (Ssym d D.s i k * mulCoeff (derivCoeff j (multiDerivCoeff β (coeffOf μ)))
                (multiDerivCoeff (α - β) F) k))‖ :=
            (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => norm_sum_le _ _)
        _ ≤ ∑ i : Fin d, ∑ j : Fin d, MB' * (Cs * N) := by
            refine Finset.sum_le_sum fun i _ => Finset.sum_le_sum fun j _ => ?_
            rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
            exact mul_le_mul (hMBle j i) (hPS i j) (norm_nonneg _) hMBnn
        _ = _ := by
            simp [Finset.sum_const, Finset.card_univ, hdd]
            ring
  have hb0 : 0 ≤ ∑ l, lam l * (Real.sqrt (quadForm (symbolK d D.s (q l)) w) * R) +
      dd * dd * MB' * Cs * N :=
    add_nonneg (Finset.sum_nonneg fun l _ => mul_nonneg (hlam l)
      (mul_nonneg (Real.sqrt_nonneg _) hR0)) (by positivity)
  have hsplit := bilin_split_re D μ α F hFt _ hcomm
  rw [PP_zero_eq] at hsplit
  have hlead := hC₀ D rfl hM lam q hlam hq hdiag μ hμ0 hμ2 hΛ2 n w hwr hwt
  have hsum : ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ) *
      (∑ l, lam l * (Real.sqrt (quadForm (symbolK d D.s (q l)) w) * R) +
        dd * dd * MB' * Cs * N) ≤
      S * (∑ l, lam l * (Real.sqrt (quadForm (symbolK d D.s (q l)) w) * R) +
        dd * dd * MB' * Cs * N) := by
    rw [← Finset.sum_mul]
    exact mul_le_mul_of_nonneg_right (sum_erase_le_binSum hα) hb0
  -- Young
  have hyoung : ∑ l, lam l * (Real.sqrt (quadForm (symbolK d D.s (q l)) w) * (S * R)) ≤
      (∑ l, lam l * quadForm (symbolK d D.s (q l))
        (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w)) / 2 +
      dd * (dd * MB' * (lam0 * (Cc * N) / 2 + (S * R) ^ 2 / (2 * lam0))) := by
    calc ∑ l, lam l * (Real.sqrt (quadForm (symbolK d D.s (q l)) w) * (S * R))
        ≤ ∑ l : Fin d, (lam l * quadForm (symbolK d D.s (q l))
            (mulCoeff (coeffOf fun x => Real.sqrt (μ x)) w) / 2 +
          (dd * MB') * (lam0 * (Cc * N) / 2 + (S * R) ^ 2 / (2 * lam0))) := by
          refine Finset.sum_le_sum fun l _ => ?_
          exact lam_step (hlam l) (hBw0 l) (mul_nonneg hS0 hR0) hlam0 (by positivity) (hlamle l)
            (hcmp l)
      _ = _ := by
          rw [Finset.sum_add_distrib, ← Finset.sum_div]
          simp [Finset.sum_const, Finset.card_univ, hdd]
  have hSR : (S * R) ^ 2 = S ^ 2 * Cρ * N := by rw [mul_pow, hR2]; ring
  have e1 : S * (∑ l, lam l * (Real.sqrt (quadForm (symbolK d D.s (q l)) w) * R) +
        dd * dd * MB' * Cs * N) =
      ∑ l, lam l * (Real.sqrt (quadForm (symbolK d D.s (q l)) w) * (S * R)) +
        S * (dd * dd * MB' * Cs * N) := by
    rw [mul_add, Finset.mul_sum]
    congr 1
    refine Finset.sum_congr rfl fun l _ => by ring
  have h1 : C₀ * hsNormSq 0 w ≤ C₀ * N := mul_le_mul_of_nonneg_left hN0w hC₀0
  rw [hSR] at hyoung
  have h2 : dd * (dd * MB' * (lam0 * (Cc * N) / 2 + S ^ 2 * Cρ * N / (2 * lam0))) =
      dd * dd * MB' * (lam0 * Cc / 2 + S ^ 2 * Cρ / (2 * lam0)) * N := by
    field_simp
  have h3 : (C₀ + dd * dd * MB' * (lam0 * Cc / 2 + S ^ 2 * Cρ / (2 * lam0)) +
      S * (dd * dd * MB' * Cs)) * N =
      C₀ * N + dd * dd * MB' * (lam0 * Cc / 2 + S ^ 2 * Cρ / (2 * lam0)) * N +
        S * (dd * dd * MB' * Cs * N) := by ring
  rw [h3]
  linarith

end HRS.PDE.R2Aux
