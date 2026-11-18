import HRS.MS.SpecAux8

/-!
# S8P: the PSD-root relative bound (S8.7, packet C1)

Namespace `HRS.MS.Spec`, helper prefix `s8p_`.  `s8p_psd_root_relative`: for a symmetric positive Hilbert–Schmidt `S` with
nonnegative square-root structure, a Hilbert basis `b` and `E b_i = e_i b_i` (`e_i > 0`, `∑ e_i² < ∞`),
`‖S - E‖²_HS ≤ 4 ∑_{i,j} (⟨S b_i, S b_j⟩ - e_i² δ_{ij})² / (e_i² + e_j²)`  (in `ℝ≥0∞`).
This is the estimate needed to bound `E‖Σ^{1/2} - D^{1/2}‖²_HS` by the relative quadratic form (proof: docs/S8_PLAN.md §2.4).
-/

noncomputable section

open Filter Topology
open scoped RealInnerProductSpace ENNReal

namespace HRS.MS.Spec

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {ι : Type*}

theorem s8p_tendsto_prod [DecidableEq ι] :
    Tendsto (fun F : Finset ι => F ×ˢ F) atTop atTop := by
  rw [tendsto_atTop_atTop]
  intro s
  refine ⟨s.image Prod.fst ∪ s.image Prod.snd, fun F hF p hp => ?_⟩
  rw [Finset.mem_product]
  exact ⟨hF (Finset.mem_union_left _ (Finset.mem_image_of_mem _ hp)),
    hF (Finset.mem_union_right _ (Finset.mem_image_of_mem _ hp))⟩

/-- Real core: `∑ ‖ξ_j‖² ≤ 4 ∑ Z_{ij}²` with `Z_{ij} = Δ_{ij}/(e_i+e_j)`. -/
theorem s8p_psd_root_core [DecidableEq ι] (S : H →L[ℝ] H) (hSs : ∀ x y, ⟪S x, y⟫ = ⟪x, S y⟫)
    (hS : ∀ x, 0 ≤ ⟪S x, x⟫) (e : ι → ℝ) (he : ∀ i, 0 < e i) (b : HilbertBasis ι ℝ H)
    (hA : Summable fun j => ‖s8p_xi S e b j‖ ^ 2)
    (hZ : Summable fun p : ι × ι =>
      ((⟪s8p_xi S e b p.1, s8p_xi S e b p.2⟫ + (e p.1 + e p.2) * s8p_x S e b p.1 p.2) /
        (e p.1 + e p.2)) ^ 2) :
    ∑' j, ‖s8p_xi S e b j‖ ^ 2 ≤ 4 * ∑' p : ι × ι,
      ((⟪s8p_xi S e b p.1, s8p_xi S e b p.2⟫ + (e p.1 + e p.2) * s8p_x S e b p.1 p.2) /
        (e p.1 + e p.2)) ^ 2 := by
  set x := s8p_x S e b with hx
  set ξ := s8p_xi S e b with hξ
  set A := ∑' j, ‖ξ j‖ ^ 2 with hAdef
  set Z : ι × ι → ℝ := fun p =>
    (⟪ξ p.1, ξ p.2⟫ + (e p.1 + e p.2) * x p.1 p.2) / (e p.1 + e p.2) with hZdef
  set Q := ∑' p, Z p ^ 2 with hQ
  have hA0 : 0 ≤ A := tsum_nonneg fun j => sq_nonneg _
  have hQ0 : 0 ≤ Q := tsum_nonneg fun p => sq_nonneg _
  -- the matrix `x²` is summable with sum `A`
  have hcol : ∀ i, HasSum (fun j => x i j ^ 2) (‖ξ i‖ ^ 2) := by
    intro i
    have := s8p_x_col S e b i
    have e1 : (fun j => x i j ^ 2) = fun j => x j i ^ 2 := by
      funext j; rw [hx, s8p_x_symm S hSs e b i j]
    rw [e1]; exact this
  have hxs : Summable fun p : ι × ι => x p.1 p.2 ^ 2 := by
    rw [summable_prod_of_nonneg (fun p => sq_nonneg _)]
    refine ⟨fun i => (hcol i).summable, ?_⟩
    simpa [fun i => (hcol i).tsum_eq] using hA
  have hxt : ∑' p : ι × ι, x p.1 p.2 ^ 2 = A := by
    rw [hxs.tsum_prod' fun i => (hcol i).summable]
    exact tsum_congr fun i => (hcol i).tsum_eq
  -- finite sections
  have hZx : ∀ p : ι × ι, Z p = x p.1 p.2 + ⟪ξ p.1, ξ p.2⟫ / (e p.1 + e p.2) := by
    intro p
    have : e p.1 + e p.2 ≠ 0 := by linarith [he p.1, he p.2]
    simp only [hZdef]; field_simp; ring
  have hsec : ∀ F : Finset ι,
      (∑ p ∈ F ×ˢ F, x p.1 p.2 ^ 2) - (1 / 2) * ∑ i ∈ F, ‖ξ i‖ ^ 2 ≤
        ∑ p ∈ F ×ˢ F, Z p * x p.1 p.2 := by
    intro F
    have h1 := s8p_finite_ineq S hSs hS e he b F
    rw [Finset.sum_product, Finset.sum_product]
    have h2 : ∀ i j, Z (i, j) * x i j = x i j ^ 2 +
        (x i j / (e i + e j)) * ⟪ξ i, ξ j⟫ := by
      intro i j
      rw [hZx]; simp only; ring
    simp_rw [h2, Finset.sum_add_distrib]
    linarith
  have hcs : ∀ F : Finset ι,
      (∑ p ∈ F ×ˢ F, Z p * x p.1 p.2) ^ 2 ≤ Q * ∑ p ∈ F ×ˢ F, x p.1 p.2 ^ 2 := by
    intro F
    have h1 := Finset.sum_mul_sq_le_sq_mul_sq (F ×ˢ F) (fun p => Z p) (fun p => x p.1 p.2)
    have h2 : ∑ p ∈ F ×ˢ F, Z p ^ 2 ≤ Q := hZ.sum_le_tsum _ fun p _ => sq_nonneg _
    have h3 : 0 ≤ ∑ p ∈ F ×ˢ F, x p.1 p.2 ^ 2 := Finset.sum_nonneg fun p _ => sq_nonneg _
    exact h1.trans (mul_le_mul_of_nonneg_right h2 h3)
  -- limits
  have hta : Tendsto (fun F : Finset ι => ∑ p ∈ F ×ˢ F, x p.1 p.2 ^ 2) atTop (𝓝 A) := by
    rw [← hxt]; exact hxs.hasSum.comp s8p_tendsto_prod
  have htc : Tendsto (fun F : Finset ι => ∑ i ∈ F, ‖ξ i‖ ^ 2) atTop (𝓝 A) := hA.hasSum
  have hu : ∀ F : Finset ι, (max ((∑ p ∈ F ×ˢ F, x p.1 p.2 ^ 2) -
      (1 / 2) * ∑ i ∈ F, ‖ξ i‖ ^ 2) 0) ^ 2 ≤ Q * ∑ p ∈ F ×ˢ F, x p.1 p.2 ^ 2 := by
    intro F
    refine le_trans ?_ (hcs F)
    rcases le_total ((∑ p ∈ F ×ˢ F, x p.1 p.2 ^ 2) - (1 / 2) * ∑ i ∈ F, ‖ξ i‖ ^ 2) 0 with h | h
    · rw [max_eq_right h]; nlinarith [sq_nonneg (∑ p ∈ F ×ˢ F, Z p * x p.1 p.2)]
    · rw [max_eq_left h]
      exact pow_le_pow_left₀ h (hsec F) 2
  have hlim := le_of_tendsto_of_tendsto' (((hta.sub (htc.const_mul (1 / 2))).max
    tendsto_const_nhds).pow 2) (hta.const_mul Q) hu
  have hmax : max (A - 1 / 2 * A) 0 = A / 2 := by
    rw [max_eq_left (by linarith)]; ring
  rw [hmax] at hlim
  by_cases hA' : A = 0
  · rw [hA']; linarith
  · have hApos : 0 < A := lt_of_le_of_ne hA0 (Ne.symm hA')
    nlinarith

end HRS.MS.Spec
