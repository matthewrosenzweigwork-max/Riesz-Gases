import HRS.PDE.EnergyLeib

/-!
# The transport form bound (`B:eq:transport-est`)
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE

variable {d : ℕ}

theorem multiDerivCoeff_derivCoeff (α : Fin d → ℕ) (j : Fin d) (F : Coeff d) :
    multiDerivCoeff α (derivCoeff j F) = derivCoeff j (multiDerivCoeff α F) := by
  funext k
  simp only [derivCoeff, multiDerivCoeff_apply]
  ring

theorem sum_sub_add_single (α β : Fin d → ℕ) (hβ : ∀ i, β i ≤ α i) (j : Fin d) :
    ∑ i, ((α - β + Pi.single j 1 : Fin d → ℕ) i) + ∑ i, β i = ∑ i, α i + 1 := by
  have h1 : ∑ i, (α - β) i + ∑ i, β i = ∑ i, α i := by
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => by simp [Nat.sub_add_cancel (hβ i)]
  have h2 : ∑ i, ((α - β + Pi.single j 1 : Fin d → ℕ) i) = ∑ i, (α - β) i + 1 := by
    simp [Finset.sum_add_distrib]
  omega

theorem transport_bound_fixed (m : ℕ) (K : ℝ) (hK : 0 ≤ K) (b : Fin d → Torus d → ℝ)
    (hb : ∀ j, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Torus.lift (b j)))
    (hB : ∀ j, Torus.cbNorm (m + 1) (b j) ≤ K)
    (α : Fin d → ℕ) (hα : ∑ i, α i ≤ m) {n : ℕ} (F : Coeff d) (hF : IsTrigPoly n F) :
    |(bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
        (fun k => ∑ j, mulCoeff (coeffOf (b j)) (derivCoeff j F) k) F).re| ≤
      ((d : ℝ) * (K / 2 + ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ) * K)) *
        hsNormSq (m : ℝ) F := by
  classical
  set N := hsNormSq (m : ℝ) F with hNdef
  have hMem : MemHs (m : ℝ) F := memHs_of_isTrigPolyE hF _
  have hN : 0 ≤ N := hsNormSq_nonnegE _ _
  set w := multiDerivCoeff α F with hwdef
  have hw : IsTrigPoly n w := isTrigPoly_multiDerivCoeff hF α
  have hwN : ∑ k ∈ boxFin d n, ‖w k‖ ^ 2 ≤ (Real.sqrt N) ^ 2 := by
    rw [Real.sq_sqrt hN]; exact sum_sq_multiDeriv_le α m hα F hMem _
  have hder : ∀ j, IsTrigPoly n (derivCoeff j F) := fun j => by
    rw [derivCoeff_eq_multi]; exact isTrigPoly_multiDerivCoeff hF _
  set T : Fin d → (Fin d → ℕ) → ℂ := fun j β =>
    ∑ k ∈ boxFin d n, conj (w k) * mulCoeff (multiDerivCoeff β (coeffOf (b j)))
      (multiDerivCoeff (α - β) (derivCoeff j F)) k with hT
  have hQ : bilinForm (fun k => ∏ i, (2 * Real.pi * (k i : ℝ)) ^ (2 * α i))
        (fun k => ∑ j, mulCoeff (coeffOf (b j)) (derivCoeff j F) k) F =
      ∑ j, ∑ β ∈ leibnizSet α, (binomW α β : ℂ) * T j β := by
    rw [bilinForm_weight_eq α _ F hF]
    have h2 : ∀ k, multiDerivCoeff α (fun k => ∑ j, mulCoeff (coeffOf (b j)) (derivCoeff j F) k) k =
        ∑ j, ∑ β ∈ leibnizSet α, (binomW α β : ℂ) *
          mulCoeff (multiDerivCoeff β (coeffOf (b j))) (multiDerivCoeff (α - β) (derivCoeff j F)) k := by
      intro k
      rw [multiDerivCoeff_apply, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      rw [← multiDerivCoeff_apply, multiDerivCoeff_mulCoeff α _ _ (hder j)]
    simp_rw [h2, Finset.mul_sum]
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [Finset.sum_comm]
    refine Finset.sum_congr rfl fun β _ => ?_
    simp only [hT, Finset.mul_sum]
    refine Finset.sum_congr rfl fun k _ => ?_
    ring
  -- bound for β ≠ 0
  have hlow : ∀ j, ∀ β ∈ (leibnizSet α).erase 0, ‖T j β‖ ≤ K * N := by
    intro j β hβ
    have hβ0 : β ≠ 0 := (Finset.mem_erase.mp hβ).1
    have hβα := mem_leibnizSet.mp (Finset.mem_erase.mp hβ).2
    have hsβ : 1 ≤ ∑ i, β i := by
      by_contra h
      apply hβ0
      funext i
      have : ∑ i, β i = 0 := by omega
      simpa using (Finset.sum_eq_zero_iff.mp this) i (Finset.mem_univ i)
    have hsβ' : ∑ i, β i ≤ ∑ i, α i := Finset.sum_le_sum fun i _ => hβα i
    obtain ⟨φ, hφc, hφ, hφK⟩ := exists_derivFun (b j) (m + 1) (hb j) β (by omega)
    have hφK' : ∀ x, |φ x| ≤ K := fun x => (hφK x).trans (hB j)
    have hc' : IsTrigPoly n (multiDerivCoeff (α - β) (derivCoeff j F)) :=
      isTrigPoly_multiDerivCoeff (hder j) _
    have hcN : ∑ k ∈ boxFin d n, ‖multiDerivCoeff (α - β) (derivCoeff j F) k‖ ^ 2 ≤
        (Real.sqrt N) ^ 2 := by
      rw [Real.sq_sqrt hN, derivCoeff_eq_multi, ← multiDerivCoeff_add]
      refine sum_sq_multiDeriv_le _ m ?_ F hMem _
      have := sum_sub_add_single α β hβα j
      omega
    have := pairing_bound φ hφc K hφK' (multiDerivCoeff (α - β) (derivCoeff j F)) hc' (boxFin d n) w
      (Real.sqrt N) (Real.sqrt N) (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hwN hcN
    rw [hφ] at this
    simpa [hT, Real.mul_self_sqrt hN, ← sq] using this
  have h0mem : (0 : Fin d → ℕ) ∈ leibnizSet α := mem_leibnizSet.mpr fun i => Nat.zero_le _
  have htop : ∀ j, |(T j 0).re| ≤ K * N / 2 := by
    intro j
    have hT0 : T j 0 = ∑ k ∈ boxFin d n, conj (w k) *
        mulCoeff (coeffOf (b j)) (derivCoeff j w) k := by
      simp only [hT, multiDerivCoeff_zero, tsub_zero, hwdef, multiDerivCoeff_derivCoeff]
    rw [hT0, re_top_term (b j) w hw j]
    obtain ⟨φ, hφc, hφ, hφK⟩ := exists_derivFun (b j) (m + 1) (hb j) (Pi.single j 1) (by simp)
    have hφK' : ∀ x, |φ x| ≤ K := fun x => (hφK x).trans (hB j)
    have := pairing_bound φ hφc K hφK' w hw (boxFin d n) w (Real.sqrt N) (Real.sqrt N)
      (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) hwN hwN
    rw [hφ, ← derivCoeff_eq_multi, Real.mul_self_sqrt hN] at this
    have h2 := (Complex.abs_re_le_norm _).trans this
    rw [abs_mul]
    have : |-(1 / 2 : ℝ)| = 1 / 2 := by norm_num
    rw [this]
    linarith
  rw [hQ]
  have hsplit : ∀ j, ∑ β ∈ leibnizSet α, (binomW α β : ℂ) * T j β =
      T j 0 + ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℂ) * T j β := by
    intro j
    rw [← Finset.add_sum_erase _ _ h0mem]
    simp [binomW]
  simp_rw [hsplit]
  have hj : ∀ j, |(T j 0 + ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℂ) * T j β).re| ≤
      K * N / 2 + ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ) * K * N := by
    intro j
    have hR : ‖∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℂ) * T j β‖ ≤
        ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ) * K * N := by
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun β hβ => ?_)
      rw [norm_mul, Complex.norm_natCast]
      calc (binomW α β : ℝ) * ‖T j β‖ ≤ (binomW α β : ℝ) * (K * N) :=
            mul_le_mul_of_nonneg_left (hlow j β hβ) (Nat.cast_nonneg _)
        _ = _ := by ring
    rw [Complex.add_re]
    calc |(T j 0).re + (∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℂ) * T j β).re|
        ≤ |(T j 0).re| + |(∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℂ) * T j β).re| :=
          abs_add_le _ _
      _ ≤ K * N / 2 + ‖∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℂ) * T j β‖ :=
          add_le_add (htop j) (Complex.abs_re_le_norm _)
      _ ≤ _ := by linarith
  rw [Complex.re_sum]
  calc |∑ j, (T j 0 + ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℂ) * T j β).re|
      ≤ ∑ j, |(T j 0 + ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℂ) * T j β).re| :=
        Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _j : Fin d, (K * N / 2 + ∑ β ∈ (leibnizSet α).erase 0, (binomW α β : ℝ) * K * N) :=
        Finset.sum_le_sum fun j _ => hj j
    _ = _ := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        rw [← Finset.sum_mul, ← Finset.sum_mul]
        ring

end HRS.PDE
