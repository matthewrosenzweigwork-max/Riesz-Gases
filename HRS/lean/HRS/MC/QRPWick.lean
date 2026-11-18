import HRS.MC.QRPWickAux2

/-!
# QRPWick: `qrs_wick_var_fin_proof` (finite Wick variance bound)

Relocated proof of `HRS.MC.QRSpec.qrs_wick_var_fin`.  Route: Isserlis pairing in the Gaussian linear space spanned by
the `ξ_i` (`QRPWickAux1`), the operator bound `|Σ a|² ≤ K² |a|²` obtained from `aᵀΣa ≤ K|a|²` by a discriminant
argument, and the matrix inequality of `QRPWickAux2`.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.QRSpec.Wick

section Fin

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
variable {ι : Type} [Fintype ι]

lemma qrpw_int_sq_sum {κ : Type} [Fintype κ] (Y : κ → Ω → ℝ) (hY : ∀ p, MemLp (Y p) 2 P)
    (c : κ → ℝ) :
    ∫ ω, (∑ p, c p * Y p ω) ^ 2 ∂P = ∑ p, ∑ q, c p * c q * ∫ ω, Y p ω * Y q ω ∂P := by
  have e : ∀ ω, (∑ p, c p * Y p ω) ^ 2 = ∑ p, ∑ q, c p * c q * (Y p ω * Y q ω) := by
    intro ω
    rw [sq, Finset.sum_mul_sum]
    refine Finset.sum_congr rfl fun p _ => Finset.sum_congr rfl fun q _ => ?_
    ring
  simp_rw [e]
  have hi : ∀ p q, Integrable (fun ω => c p * c q * (Y p ω * Y q ω)) P :=
    fun p q => ((hY p).integrable_mul (hY q)).const_mul _
  rw [integral_finsetSum _ (fun p _ => integrable_finset_sum _ fun q _ => hi p q)]
  refine Finset.sum_congr rfl fun p _ => ?_
  rw [integral_finsetSum _ (fun q _ => hi p q)]
  refine Finset.sum_congr rfl fun q _ => ?_
  rw [integral_const_mul]

variable (ξ : ι → Ω → ℝ)

/-- Linear combinations of the `ξ_i`. -/
def qrpwY (a : ι → ℝ) : Ω → ℝ := fun ω => ∑ i, a i * ξ i ω

lemma qrpw_int_lin {X : Ω → ℝ} (hX : MemLp X 4 P) (h4 : ∀ i, MemLp (ξ i) 4 P) (c : ι → ℝ) :
    ∫ ω, X ω * qrpwY ξ c ω ∂P = ∑ i, c i * ∫ ω, X ω * ξ i ω ∂P := by
  have e : ∀ ω, X ω * qrpwY ξ c ω = ∑ i, c i * (X ω * ξ i ω) := by
    intro ω
    simp only [qrpwY, Finset.mul_sum]
    exact Finset.sum_congr rfl fun i _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ (fun i _ => (qrpw_int_mul hX (h4 i)).const_mul _)]
  exact Finset.sum_congr rfl fun i _ => integral_const_mul _ _

/-- The operator bound `|Σ a|² ≤ K² |a|²` from the form bound `aᵀΣa ≤ K|a|²`. -/
lemma qrpw_hop {S : Submodule ℝ (Ω → ℝ)} (hS : QrpwG4 P S) (hlin : ∀ a, qrpwY ξ a ∈ S)
    (hx : ∀ i, ξ i ∈ S) (K : ℝ)
    (hK : ∀ a : ι → ℝ, ∫ ω, (∑ i, a i * ξ i ω) ^ 2 ∂P ≤ K * ∑ i, a i ^ 2) (a : ι → ℝ) :
    ∑ k, (∑ i, (∫ ω, ξ k ω * ξ i ω ∂P) * a i) ^ 2 ≤ K ^ 2 * ∑ i, a i ^ 2 := by
  have h4 : ∀ i, MemLp (ξ i) 4 P := fun i => (hS _ (hx i)).1
  set b : ι → ℝ := fun k => ∑ i, (∫ ω, ξ k ω * ξ i ω ∂P) * a i with hb
  set N : ℝ := ∑ k, b k ^ 2 with hN
  have hbk : ∀ k, ∫ ω, ξ k ω * qrpwY ξ a ω ∂P = b k := by
    intro k
    rw [qrpw_int_lin ξ (h4 k) h4 a, hb]
    exact Finset.sum_congr rfl fun i _ => mul_comm _ _
  have hAB : ∫ ω, qrpwY ξ a ω * qrpwY ξ b ω ∂P = N := by
    rw [qrpw_int_lin ξ (hS _ (hlin a)).1 h4 b, hN]
    simp_rw [sq]
    refine Finset.sum_congr rfl fun k _ => ?_
    have : ∫ ω, qrpwY ξ a ω * ξ k ω ∂P = b k := by
      rw [← hbk k]; simp_rw [mul_comm (qrpwY ξ a _)]
    rw [this]
  have hA2 : ∫ ω, qrpwY ξ a ω ^ 2 ∂P ≤ K * ∑ i, a i ^ 2 := hK a
  have hB2 : ∫ ω, qrpwY ξ b ω ^ 2 ∂P ≤ K * N := hK b
  have hquad : ∀ c : ℝ, 0 ≤ (K * N) * (c * c) + (-2 * N) * c + K * ∑ i, a i ^ 2 := by
    intro c
    have h0 : 0 ≤ ∫ ω, (qrpwY ξ a ω + (-c) * qrpwY ξ b ω) ^ 2 ∂P :=
      integral_nonneg fun ω => sq_nonneg _
    rw [qrpw_Bsq hS (hlin a) (hlin b) (-c), hAB] at h0
    have : (-c) ^ 2 * ∫ ω, qrpwY ξ b ω ^ 2 ∂P ≤ (-c) ^ 2 * (K * N) :=
      mul_le_mul_of_nonneg_left hB2 (sq_nonneg _)
    nlinarith
  have hd := discrim_le_zero hquad
  unfold discrim at hd
  have hN0 : 0 ≤ N := Finset.sum_nonneg fun k _ => sq_nonneg _
  have hmain : N * N ≤ (K ^ 2 * ∑ i, a i ^ 2) * N := by nlinarith
  show N ≤ K ^ 2 * ∑ i, a i ^ 2
  rcases hN0.eq_or_lt with h | h
  · rw [← h]; positivity
  · exact le_of_mul_le_mul_right hmain h

lemma qrpw_space (hξ : HasGaussianLaw (fun ω i => ξ i ω) P) (hc : ∀ i, ∫ ω, ξ i ω ∂P = 0) :
    ∃ S : Submodule ℝ (Ω → ℝ), QrpwG4 P S ∧ (∀ a, qrpwY ξ a ∈ S) ∧ (∀ i, ξ i ∈ S) := by
  refine ⟨Submodule.span ℝ (Set.range ξ), ?_, ?_, ?_⟩
  · intro W hW
    obtain ⟨c, hc'⟩ := (Submodule.mem_span_range_iff_exists_fun ℝ).1 hW
    have hWe : W = qrpwY ξ c := by
      rw [← hc']; funext ω; simp [qrpwY, Finset.sum_apply]
    subst hWe
    let L : (ι → ℝ) →L[ℝ] ℝ := ∑ i, c i • (ContinuousLinearMap.proj i : (ι → ℝ) →L[ℝ] ℝ)
    have hg : HasGaussianLaw (qrpwY ξ c) P := by
      have := hξ.map_fun L
      convert this using 1
      funext ω; simp [qrpwY, L]
    have hm : ∫ ω, qrpwY ξ c ω ∂P = 0 := by
      simp only [qrpwY]
      rw [integral_finsetSum _ (fun i _ => ((hξ.eval i).integrable).const_mul _)]
      simp [integral_const_mul, hc]
    exact qrpw_gauss4 hg hm
  · intro a
    have : qrpwY ξ a = ∑ i, a i • ξ i := by
      funext ω; simp [qrpwY, Finset.sum_apply]
    rw [this]
    exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)
  · intro i
    exact Submodule.subset_span ⟨i, rfl⟩

end Fin

/-- Relocated proof of `HRS.MC.QRSpec.qrs_wick_var_fin`. -/
theorem qrs_wick_var_fin_proof {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ι : Type} [Fintype ι] (ξ : ι → Ω → ℝ) (hξ : HasGaussianLaw (fun ω i => ξ i ω) P)
    (hc : ∀ i, ∫ ω, ξ i ω ∂P = 0) (K : ℝ)
    (hK : ∀ a : ι → ℝ, ∫ ω, (∑ i, a i * ξ i ω) ^ 2 ∂P ≤ K * ∑ i, a i ^ 2)
    (A : ι → ι → ℝ) :
    MemLp (fun ω => ∑ i, ∑ j, A i j * (ξ i ω * ξ j ω - ∫ ω', ξ i ω' * ξ j ω' ∂P)) 2 P ∧
    ∫ ω, (∑ i, ∑ j, A i j * (ξ i ω * ξ j ω - ∫ ω', ξ i ω' * ξ j ω' ∂P)) ^ 2 ∂P ≤
      2 * K ^ 2 * ∑ i, ∑ j, A i j ^ 2 := by
  obtain ⟨S, hS, hlin, hx⟩ := qrpw_space ξ hξ hc
  have h4 : ∀ i, MemLp (ξ i) 4 P := fun i => (hS _ (hx i)).1
  obtain ⟨Sg, hSg⟩ : ∃ Sg : ι → ι → ℝ, ∀ i j, Sg i j = ∫ ω, ξ i ω * ξ j ω ∂P :=
    ⟨_, fun _ _ => rfl⟩
  have hs : ∀ i j, Sg i j = Sg j i := fun i j => by
    rw [hSg, hSg]; simp_rw [mul_comm (ξ i _)]
  have hop : ∀ a : ι → ℝ, ∑ k, (∑ i, Sg k i * a i) ^ 2 ≤ K ^ 2 * ∑ i, a i ^ 2 := by
    intro a
    simp_rw [hSg]
    exact qrpw_hop ξ hS hlin hx K hK a
  simp_rw [← hSg]
  let Y : ι × ι → Ω → ℝ := fun p ω => ξ p.1 ω * ξ p.2 ω - Sg p.1 p.2
  have hY2 : ∀ p, MemLp (Y p) 2 P := fun p =>
    (qrpw_memLp2_mul (h4 p.1) (h4 p.2)).sub (memLp_const _)
  have hZ : ∀ ω, ∑ i, ∑ j, A i j * (ξ i ω * ξ j ω - Sg i j) =
      ∑ p : ι × ι, A p.1 p.2 * Y p ω := fun ω => by rw [Fintype.sum_prod_type]
  simp_rw [hZ]
  have hcov : ∀ i j k l, ∫ ω, (ξ i ω * ξ j ω - Sg i j) * (ξ k ω * ξ l ω - Sg k l) ∂P =
      Sg i k * Sg j l + Sg i l * Sg j k := by
    intro i j k l
    have e : (fun ω => (ξ i ω * ξ j ω - Sg i j) * (ξ k ω * ξ l ω - Sg k l)) = fun ω =>
        ξ i ω * ξ j ω * (ξ k ω * ξ l ω) - Sg k l * (ξ i ω * ξ j ω) -
          Sg i j * (ξ k ω * ξ l ω) + Sg i j * Sg k l := by
      funext ω; ring
    have I1 := qrpw_int_mul4 (h4 i) (h4 j) (h4 k) (h4 l)
    have I2 : Integrable (fun ω => Sg k l * (ξ i ω * ξ j ω)) P :=
      (qrpw_int_mul (h4 i) (h4 j)).const_mul _
    have I3 : Integrable (fun ω => Sg i j * (ξ k ω * ξ l ω)) P :=
      (qrpw_int_mul (h4 k) (h4 l)).const_mul _
    have J1 : Integrable (fun ω => ξ i ω * ξ j ω * (ξ k ω * ξ l ω) -
        Sg k l * (ξ i ω * ξ j ω)) P := I1.sub I2
    have J2 : Integrable (fun ω => ξ i ω * ξ j ω * (ξ k ω * ξ l ω) -
        Sg k l * (ξ i ω * ξ j ω) - Sg i j * (ξ k ω * ξ l ω)) P := J1.sub I3
    rw [e, integral_add J2 (integrable_const _), integral_sub J1 I3, integral_sub I1 I2,
      integral_const_mul, integral_const_mul, integral_const, qrpw_wick4 hS (hx i) (hx j) (hx k) (hx l)]
    simp only [← hSg]
    simp
    ring
  constructor
  · exact memLp_finsetSum _ fun p _ => (hY2 p).const_mul _
  · rw [qrpw_int_sq_sum Y hY2 (fun p => A p.1 p.2)]
    have h := qrpw_alg_bound Sg A hs K hop
    refine le_trans (le_of_eq ?_) h
    simp only [Fintype.sum_prod_type]
    simp only [Y, hcov]

end HRS.MC.QRSpec.Wick

end
