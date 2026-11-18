import HRS.MC.E718B5

/-!
# Row 7.18 (packet e718b), file 6: the sections in two Hilbert bases are `L²`-close
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal

noncomputable section

set_option linter.unusedSectionVars false

namespace HRS.MC.E718B

section

variable {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {W : H → Ω → ℝ}

lemma sections_close (hW : IsIsonormal P W) (A : H →L[ℝ] H)
    (hA : ∀ x y, inner ℝ (A x) y = inner ℝ x (A y)) (e e' : HilbertBasis ℕ ℝ H)
    (hHS : Summable fun i => ‖A (e i)‖ ^ 2) (hHS' : Summable fun i => ‖A (e' i)‖ ^ 2)
    (L : ℕ) (hL : 0 < L) :
    ∫⁻ ω, ‖isoSection A W e' L ω - isoSection A W e L ω‖ₑ ^ 2 ∂P ≤
      ENNReal.ofReal (∑' j, ‖Tb e L A (e j)‖ ^ 2 + ∑' j, ‖Tb e' L A (e' j)‖ ^ 2) := by
  obtain ⟨m, f, hm, hf, hspan, hspan'⟩ := exists_common_basis (fun i => e i) (fun i => e' i)
    (fun i => e.orthonormal.ne_zero i) L hL
  have r := hW.rep f hf L (fun i => e i) e.orthonormal hspan (fun i j => inner ℝ (e i) (A (e j)))
  have r' := hW.rep f hf L (fun i => e' i) e'.orthonormal hspan' (fun i j => inner ℝ (e' i) (A (e' j)))
  set c : Fin m → Fin m → ℝ := fun k l => inner ℝ (f k) (Pb e L (A (Pb e L (f l)))) with hc
  set c' : Fin m → Fin m → ℝ := fun k l => inner ℝ (f k) (Pb e' L (A (Pb e' L (f l)))) with hc'
  have hcc : (fun k l => ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      inner ℝ (e i) (A (e j)) * inner ℝ (f k) (e i) * inner ℝ (f l) (e j)) = c :=
    funext₂ fun k l => sec_coeff e L A (f k) (f l)
  have hcc' : (fun k l => ∑ i ∈ Finset.range L, ∑ j ∈ Finset.range L,
      inner ℝ (e' i) (A (e' j)) * inner ℝ (f k) (e' i) * inner ℝ (f l) (e' j)) = c' :=
    funext₂ fun k l => sec_coeff e' L A (f k) (f l)
  simp only [hcc] at r
  simp only [hcc'] at r'
  set D : Fin m → Fin m → ℝ := fun k l =>
    inner ℝ (f k) (Tb e L A (f l)) - inner ℝ (f k) (Tb e' L A (f l)) with hD
  have hDc : ∀ k l, c' k l - c k l = D k l := by
    intro k l
    simp only [hD, hc, hc', Tb_apply, inner_sub_right]
    ring
  have hDs : ∀ k l, D k l = D l k := by
    intro k l
    have h1 : ∀ (b : HilbertBasis ℕ ℝ H) (k l : Fin m),
        inner ℝ (f k) (Tb b L A (f l)) = inner ℝ (f l) (Tb b L A (f k)) := by
      intro b k l
      rw [← Tb_symm b L A hA]
      exact real_inner_comm _ _
    simp only [hD]
    rw [h1 e k l, h1 e' k l]
  -- the difference of the sections is `Phi f D`
  have hdiff : (fun ω => isoSection A W e' L ω - isoSection A W e L ω) =ᵐ[P] Phi W f D := by
    filter_upwards [r, r'] with ω h h'
    have h2 : isoSection A W e L ω = Phi W f c ω := h
    have h2' : isoSection A W e' L ω = Phi W f c' ω := h'
    rw [h2, h2', Phi_sub]
    simp only [hDc]
  obtain ⟨hmem, hint⟩ := hW.Phi_memLp_integral hm f hf D hDs
  have hl : ∫⁻ ω, ‖isoSection A W e' L ω - isoSection A W e L ω‖ₑ ^ 2 ∂P = ENNReal.ofReal
      ((1 / 2) * ∑ k, ∑ l, D k l ^ 2) := by
    rw [← hint, ← lintegral_enorm_sq_of_memLp hmem]
    refine lintegral_congr_ae ?_
    filter_upwards [hdiff] with ω h
    simp only [h]
  rw [hl]
  refine ENNReal.ofReal_le_ofReal ?_
  -- Bessel bounds
  have hsT : ∀ (b : HilbertBasis ℕ ℝ H), Summable (fun j => ‖A (b j)‖ ^ 2) →
      Summable fun j => ‖Tb b L A (b j)‖ ^ 2 := fun b hb =>
    Summable.of_nonneg_of_le (fun j => sq_nonneg _) (fun j => Tb_sq_le b L A j) hb
  have hB := sum_sq_le e (Tb e L A) (Tb_symm e L A hA) (hsT e hHS) f hf
  have hB' := sum_sq_le e' (Tb e' L A) (Tb_symm e' L A hA) (hsT e' hHS') f hf
  have hcol : ∀ l, ∑ k, D k l ^ 2 ≤ 2 * ‖Tb e L A (f l)‖ ^ 2 + 2 * ‖Tb e' L A (f l)‖ ^ 2 := by
    intro l
    have h1 := hf.sum_inner_products_le (s := Finset.univ) (x := Tb e L A (f l) - Tb e' L A (f l))
    have h2 : ∀ k, D k l = inner ℝ (f k) (Tb e L A (f l) - Tb e' L A (f l)) := fun k => by
      simp only [hD, inner_sub_right]
    simp only [h2, Real.norm_eq_abs, sq_abs] at h1 ⊢
    have h3 : ‖Tb e L A (f l) - Tb e' L A (f l)‖ ^ 2 ≤
        2 * ‖Tb e L A (f l)‖ ^ 2 + 2 * ‖Tb e' L A (f l)‖ ^ 2 := by
      have := norm_sub_le (Tb e L A (f l)) (Tb e' L A (f l))
      nlinarith [norm_nonneg (Tb e L A (f l) - Tb e' L A (f l)), norm_nonneg (Tb e L A (f l)),
        norm_nonneg (Tb e' L A (f l)), sq_nonneg (‖Tb e L A (f l)‖ - ‖Tb e' L A (f l)‖)]
    exact h1.trans h3
  rw [Finset.sum_comm]
  calc (1 / 2) * ∑ l, ∑ k, D k l ^ 2 ≤ (1 / 2) * ∑ l, (2 * ‖Tb e L A (f l)‖ ^ 2 + 2 * ‖Tb e' L A (f l)‖ ^ 2) :=
        mul_le_mul_of_nonneg_left (Finset.sum_le_sum fun l _ => hcol l) (by norm_num)
    _ = ∑ l, ‖Tb e L A (f l)‖ ^ 2 + ∑ l, ‖Tb e' L A (f l)‖ ^ 2 := by
        rw [Finset.sum_add_distrib, ← Finset.mul_sum, ← Finset.mul_sum]; ring
    _ ≤ _ := add_le_add hB hB'

end

end HRS.MC.E718B
