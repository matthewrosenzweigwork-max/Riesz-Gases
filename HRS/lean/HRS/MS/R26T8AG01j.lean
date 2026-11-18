import HRS.MS.R26T8AG01i
import HRS.MS.R26T8AG01d

/-!
# S8.2 observed-time layer, packet T8A.G01 (helper j): derivative bounds of the pair product

With `α_i X = Σ_{j>i} 1/‖X i - X j‖`, `A X = Σ_i α_i X`, `Q X = Σ_i Σ_{j>i} (1/‖X i - X j‖)²`, the pair product
`P_n X = ∏_i ∏_{j>i} ψ(m² ‖X i - X j‖²)` satisfies
`‖∂P_n X‖ ≤ 8 K₁ Λ A X` and `‖∂²P_n X‖ ≤ (8K₁+64K₂) Λ² Q X + (N+1)(8K₁ Λ A X)²`,
where `Λ` bounds the norms of the linear maps `proj i - proj j`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

theorem r26t8a_g01j_P {d N : ℕ} {K1 K2 Λ : ℝ}
    (hK1 : ∀ t : ℝ, |deriv r26t8a_g01a_psi t| ≤ K1) (hK2 : ∀ t : ℝ, |deriv (deriv r26t8a_g01a_psi) t| ≤ K2)
    (hK1n : 0 ≤ K1) (hK2n : 0 ≤ K2) (hΛ0 : 0 ≤ Λ)
    (hΛ : ∀ i j : Fin N, ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
      ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j‖ ≤ Λ)
    (n : ℕ) (X : EucConfig d N) :
    ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N => ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤
      8 * K1 * Λ * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖ ∧
    ‖iteratedFDeriv ℝ 2 (fun y : EucConfig d N => ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤
      (8 * K1 + 64 * K2) * Λ ^ 2 * (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2) +
        ((N : ℝ) + 1) * (8 * K1 * Λ * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖) ^ 2 := by
  -- the inner products `g_i`
  have hpsi01 : ∀ t : ℝ, 0 ≤ r26t8a_g01a_psi t ∧ r26t8a_g01a_psi t ≤ 1 := fun t =>
    ⟨r26t8a_g01a_nonneg t, r26t8a_g01a_le_one t⟩
  have hpsi_cd : ∀ i j : Fin N, ContDiff ℝ ∞ (fun y : EucConfig d N =>
      r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) := fun i j => by
    have hL : ContDiff ℝ ∞ (fun y : EucConfig d N => ‖y i - y j‖ ^ 2) :=
      (contDiff_norm_sq ℝ).comp
        ((ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
          ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j).contDiff)
    exact r26t8a_g01a_contDiff.comp (contDiff_const.mul hL)
  -- bounds for the derivatives of each factor, in terms of `1/‖X i - X j‖`
  have hfac : ∀ i j : Fin N, ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N =>
        r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤ 8 * K1 * Λ * (1 / ‖X i - X j‖) ∧
      ‖iteratedFDeriv ℝ 2 (fun y : EucConfig d N =>
        r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤
          (8 * K1 + 64 * K2) * Λ ^ 2 * (1 / ‖X i - X j‖) ^ 2 := by
    intro i j
    obtain ⟨h1, h2⟩ := r26t8a_g01i_pair hK1 hK2 hK1n hK2n n i j X
    have hL := hΛ i j
    have hL0 : 0 ≤ ‖ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i -
        ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j‖ := norm_nonneg _
    have hinv : 0 ≤ 1 / ‖X i - X j‖ := by positivity
    have hc : 0 ≤ 8 * K1 + 64 * K2 := by positivity
    constructor
    · refine h1.trans ?_
      rw [div_eq_mul_one_div]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hL (by positivity)) hinv
    · refine h2.trans ?_
      have e : ∀ x y : ℝ, x / y ^ 2 = x * (1 / y) ^ 2 := fun x y => by rw [one_div_pow]; ring
      rw [e]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (pow_le_pow_left₀ hL0 hL 2) hc)
        (sq_nonneg _)
  -- the inner products over `j > i`
  have hinner : ∀ i : Fin N,
      ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N => ∏ j ∈ Finset.univ.filter (fun j => i < j),
          r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤
        8 * K1 * Λ * ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖ ∧
      ‖iteratedFDeriv ℝ 2 (fun y : EucConfig d N => ∏ j ∈ Finset.univ.filter (fun j => i < j),
          r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤
        (8 * K1 + 64 * K2) * Λ ^ 2 * (∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2) +
          (8 * K1 * Λ * ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖) ^ 2 := by
    intro i
    have hd := r26t8a_g01d_prod (ι := Fin N) (Finset.univ.filter (fun j => i < j))
      (fun j (y : EucConfig d N) => r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2))
      (fun j => hpsi_cd i j) X (fun j => by rw [abs_of_nonneg (hpsi01 _).1]; exact (hpsi01 _).2)
    obtain ⟨d1, d2⟩ := hd
    have s1 : ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N =>
          r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤
        8 * K1 * Λ * ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖ := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => (hfac i j).1
    have s2 : ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ‖iteratedFDeriv ℝ 2 (fun y : EucConfig d N =>
          r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤
        (8 * K1 + 64 * K2) * Λ ^ 2 * ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2 := by
      rw [Finset.mul_sum]
      exact Finset.sum_le_sum fun j _ => (hfac i j).2
    have s0 : 0 ≤ ∑ j ∈ Finset.univ.filter (fun j => i < j),
        ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N =>
          r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ :=
      Finset.sum_nonneg fun j _ => norm_nonneg _
    constructor
    · exact d1.trans s1
    · exact (d2.trans (add_le_add s2 (pow_le_pow_left₀ s0 s1 2))).trans_eq' rfl
  -- the outer product over `i`
  have hval : ∀ i : Fin N, |∏ j ∈ Finset.univ.filter (fun j => i < j),
      r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖X i - X j‖ ^ 2)| ≤ 1 := by
    intro i
    rw [abs_of_nonneg (Finset.prod_nonneg fun j _ => (hpsi01 _).1)]
    exact Finset.prod_le_one₀ (fun j _ => (hpsi01 _).1) fun j _ => (hpsi01 _).2
  have hd := r26t8a_g01d_prod (ι := Fin N) Finset.univ
    (fun i (y : EucConfig d N) => ∏ j ∈ Finset.univ.filter (fun j => i < j),
      r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2))
    (fun i => contDiff_prod fun j _ => hpsi_cd i j) X hval
  obtain ⟨o1, o2⟩ := hd
  set α : Fin N → ℝ := fun i => ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖ with hαdef
  set β : Fin N → ℝ := fun i => ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2 with hβdef
  have hα0 : ∀ i, 0 ≤ α i := fun i => Finset.sum_nonneg fun j _ => by positivity
  have hβ0 : ∀ i, 0 ≤ β i := fun i => Finset.sum_nonneg fun j _ => by positivity
  set A : ℝ := ∑ i : Fin N, α i with hAdef
  have hA0 : 0 ≤ A := Finset.sum_nonneg fun i _ => hα0 i
  have hαA : ∀ i, α i ≤ A := fun i =>
    Finset.single_le_sum (f := fun k => α k) (fun k _ => hα0 k) (Finset.mem_univ i)
  have hK0 : 0 ≤ 8 * K1 * Λ := by positivity
  -- first derivative
  have hT1 : ∑ i : Fin N, ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N =>
      ∏ j ∈ Finset.univ.filter (fun j => i < j), r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤
      8 * K1 * Λ * A := by
    rw [hAdef, Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => (hinner i).1
  have hfirst : ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N => ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j),
      r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤ 8 * K1 * Λ * A :=
    o1.trans hT1
  -- second derivative
  have hsq : ∑ i : Fin N, (8 * K1 * Λ * α i) ^ 2 ≤ (N : ℝ) * (8 * K1 * Λ * A) ^ 2 := by
    calc ∑ i : Fin N, (8 * K1 * Λ * α i) ^ 2 ≤ ∑ _i : Fin N, (8 * K1 * Λ * A) ^ 2 :=
          Finset.sum_le_sum fun i _ => pow_le_pow_left₀ (by positivity)
            (mul_le_mul_of_nonneg_left (hαA i) hK0) 2
      _ = (N : ℝ) * (8 * K1 * Λ * A) ^ 2 := by simp
  have hsecond1 : ∑ i : Fin N, ‖iteratedFDeriv ℝ 2 (fun y : EucConfig d N =>
      ∏ j ∈ Finset.univ.filter (fun j => i < j), r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤
      ∑ i : Fin N, ((8 * K1 + 64 * K2) * Λ ^ 2 * β i + (8 * K1 * Λ * α i) ^ 2) :=
    Finset.sum_le_sum fun i _ => (hinner i).2
  have hQeq : ∑ i : Fin N, (8 * K1 + 64 * K2) * Λ ^ 2 * β i =
      (8 * K1 + 64 * K2) * Λ ^ 2 * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2 := by
    rw [Finset.mul_sum, hβdef]
  have hsecond : ‖iteratedFDeriv ℝ 2 (fun y : EucConfig d N => ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j),
      r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤
      (8 * K1 + 64 * K2) * Λ ^ 2 * (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2) +
        ((N : ℝ) + 1) * (8 * K1 * Λ * ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖) ^ 2 := by
    have hsum1 : ∑ i : Fin N, ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N =>
        ∏ j ∈ Finset.univ.filter (fun j => i < j), r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤
        8 * K1 * Λ * A := hT1
    have hsn : 0 ≤ ∑ i : Fin N, ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N =>
        ∏ j ∈ Finset.univ.filter (fun j => i < j), r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ :=
      Finset.sum_nonneg fun i _ => norm_nonneg _
    have hsq2 := pow_le_pow_left₀ hsn hsum1 2
    have hAq : (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2) =
        ∑ i : Fin N, β i := rfl
    have hsum2 : ∑ i : Fin N, ((8 * K1 + 64 * K2) * Λ ^ 2 * β i + (8 * K1 * Λ * α i) ^ 2) =
        (8 * K1 + 64 * K2) * Λ ^ 2 * (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2) +
          ∑ i : Fin N, (8 * K1 * Λ * α i) ^ 2 := by
      rw [Finset.sum_add_distrib, hQeq]
    have hfin : ‖iteratedFDeriv ℝ 2 (fun y : EucConfig d N => ∏ i : Fin N, ∏ j ∈ Finset.univ.filter (fun j => i < j),
        r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤
        ∑ i : Fin N, ‖iteratedFDeriv ℝ 2 (fun y : EucConfig d N =>
          ∏ j ∈ Finset.univ.filter (fun j => i < j), r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ +
          (∑ i : Fin N, ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N =>
            ∏ j ∈ Finset.univ.filter (fun j => i < j), r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖) ^ 2 := o2
    have hnum : (∑ i : Fin N, ‖iteratedFDeriv ℝ 1 (fun y : EucConfig d N =>
            ∏ j ∈ Finset.univ.filter (fun j => i < j), r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖) ^ 2 ≤
        (8 * K1 * Λ * A) ^ 2 := pow_le_pow_left₀ hsn hsum1 2
    have hfin' : ∑ i : Fin N, ‖iteratedFDeriv ℝ 2 (fun y : EucConfig d N =>
          ∏ j ∈ Finset.univ.filter (fun j => i < j), r26t8a_g01a_psi (((n : ℝ) + 1) ^ 2 * ‖y i - y j‖ ^ 2)) X‖ ≤
        (8 * K1 + 64 * K2) * Λ ^ 2 * (∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), (1 / ‖X i - X j‖) ^ 2) +
          (N : ℝ) * (8 * K1 * Λ * A) ^ 2 := by
      linarith [hsecond1, hsum2, hsq]
    have hfinal : (N : ℝ) * (8 * K1 * Λ * A) ^ 2 + (8 * K1 * Λ * A) ^ 2 = ((N : ℝ) + 1) * (8 * K1 * Λ * A) ^ 2 := by
      ring
    have hAeq : A = ∑ i : Fin N, ∑ j ∈ Finset.univ.filter (fun j => i < j), 1 / ‖X i - X j‖ := rfl
    rw [← hAeq]
    linarith [hfin, hfin', hnum, hfinal]
  exact ⟨hfirst, hsecond⟩

end HRS.MS.R26T8A

end
