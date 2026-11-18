import HRS.Sections.AdjKAAux8
import HRS.Uniform.Q14Aux6

/-!
# ADJKA part 9: finite-rank coordinate maps and trace bounds for the particle covariation
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.AdjK

open HRS HRS.Uniform HRS.Uniform.Q54 HRS.Uniform.Q48b

variable {d : ℕ}

open Classical in
/-- The coordinate projection of `E_γ` onto the modes in `S`. -/
def adjkP (γ : ℝ) (S : Finset (NonzeroLattice d)) : NegSobolev d γ →L[ℝ] NegSobolev d γ :=
  ∑ k ∈ S, (innerSL ℝ (q48bBasis γ k)).smulRight (q48bBasis γ k)

open Classical in
/-- The finite-rank map `E_m → E_j` that keeps the modes in `S` and multiplies by `⟨k⟩^{m-j}`. -/
def adjkR (m j : ℝ) (S : Finset (NonzeroLattice d)) : NegSobolev d m →L[ℝ] NegSobolev d j :=
  ∑ k ∈ S, (innerSL ℝ (q48bBasis m k)).smulRight ((q48bW k ^ (m - j)) • q48bBasis j k)

theorem adjka_inner_basis {γ : ℝ} (k : NonzeroLattice d) (x : NegSobolev d γ) :
    inner ℝ (q48bBasis γ k) x = NegSobolev.coord x k := by
  classical
  unfold q48bBasis
  have := lp.inner_single_left (𝕜 := ℝ) (G := fun _ : NonzeroLattice d => ℝ) k (1 : ℝ)
    (x : lp (fun _ : NonzeroLattice d => ℝ) 2)
  refine this.trans ?_
  simp [NegSobolev.coord]

theorem adjkP_coord {γ : ℝ} (S : Finset (NonzeroLattice d)) (x : NegSobolev d γ) (l : NonzeroLattice d) :
    NegSobolev.coord (adjkP γ S x) l = if l ∈ S then NegSobolev.coord x l else 0 := by
  classical
  unfold adjkP
  rw [ContinuousLinearMap.sum_apply, q48b_coord_sum]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, adjka_inner_basis,
    q48b_coord_smul, q48b_coord_basis]
  by_cases hl : l ∈ S
  · rw [if_pos hl, Finset.sum_eq_single l]
    · simp
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; exact absurd hl h
  · rw [if_neg hl]
    refine Finset.sum_eq_zero fun k hk => ?_
    have : l ≠ k := fun h => hl (h ▸ hk)
    simp [this]

theorem adjkR_coord (m j : ℝ) (S : Finset (NonzeroLattice d)) (x : NegSobolev d m) (l : NonzeroLattice d) :
    NegSobolev.coord (adjkR m j S x) l = if l ∈ S then q48bW l ^ (m - j) * NegSobolev.coord x l else 0 := by
  classical
  unfold adjkR
  rw [ContinuousLinearMap.sum_apply, q48b_coord_sum]
  simp only [ContinuousLinearMap.smulRight_apply, innerSL_apply_apply, adjka_inner_basis,
    q48b_coord_smul, q48b_coord_basis]
  by_cases hl : l ∈ S
  · rw [if_pos hl, Finset.sum_eq_single l]
    · simp [mul_comm]
    · intro k _ hk; simp [Ne.symm hk]
    · intro h; exact absurd hl h
  · rw [if_neg hl]
    refine Finset.sum_eq_zero fun k hk => ?_
    have : l ≠ k := fun h => hl (h ▸ hk)
    simp [this]

/-- `ι ∘ R_S = P_S`. -/
theorem adjka_emb_adjkR {j m : ℝ} (hjm : j ≤ m) (S : Finset (NonzeroLattice d)) (x : NegSobolev d m) :
    adjkEmb d hjm (adjkR m j S x) = adjkP m S x := by
  refine lp.ext (funext fun l => ?_)
  show NegSobolev.coord (NegSobolev.embed m (adjkR m j S x)) l = NegSobolev.coord (adjkP m S x) l
  rw [adjka_embed_coord hjm, adjkP_coord]
  have hz : NegSobolev.fourierCoeff (adjkR m j S x) l = q48bW l ^ j * NegSobolev.coord (adjkR m j S x) l := rfl
  rw [hz, adjkR_coord]
  have hw := q48bW_pos l
  by_cases hl : l ∈ S
  · simp only [if_pos hl]
    calc q48bW l ^ (-m) * (q48bW l ^ j * (q48bW l ^ (m - j) * NegSobolev.coord x l))
        = (q48bW l ^ (-m) * q48bW l ^ j * q48bW l ^ (m - j)) * NegSobolev.coord x l := by ring
      _ = NegSobolev.coord x l := by
          rw [← Real.rpow_add hw, ← Real.rpow_add hw]
          have : -m + j + (m - j) = 0 := by ring
          rw [this, Real.rpow_zero, one_mul]
  · simp [hl]


section Trace

variable {K : Type} [NormedAddCommGroup K] [InnerProductSpace ℝ K] [CompleteSpace K]
  [MeasurableSpace K] [BorelSpace K] [SecondCountableTopology K]

theorem adjka_formComp_eq {m q : ℝ} (hm : (d : ℝ) / 2 + 2 < m) (hq : 0 ≤ q) {μ : Measure (Torus d)}
    [IsFiniteMeasure μ] (L : NegSobolev d m →L[ℝ] K) (x y : K) :
    Kot.formComp (ContinuousLinearMap.adjoint L) (covForm m q μ) x y =
      ∑ l : Fin d, ∫ a, inner ℝ (L (Real.sqrt (2 * q) • bVec m l a)) x *
        inner ℝ (L (Real.sqrt (2 * q) • bVec m l a)) y ∂μ := by
  rw [Kot.formComp_apply, Q14.q14_covForm_apply hm hq μ]
  refine Finset.sum_congr rfl fun l _ => ?_
  refine integral_congr_ae (Filter.Eventually.of_forall fun a => ?_)
  simp only [ContinuousLinearMap.adjoint_inner_right]

theorem adjka_trace_family {m q : ℝ} (hm : (d : ℝ) / 2 + 2 < m) (hq : 0 ≤ q) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (L : NegSobolev d m →L[ℝ] K) (B : ℝ) (hB0 : 0 ≤ B)
    (hB : ∀ (l : Fin d) (a : Torus d), ‖L (Real.sqrt (2 * q) • bVec m l a)‖ ^ 2 ≤ B) :
    traceNormForm (Kot.formComp (ContinuousLinearMap.adjoint L) (covForm m q μ)) ≤ d * B := by
  have hbm : ∀ l : Fin d, Measurable fun a => L (Real.sqrt (2 * q) • bVec m l a) := fun l =>
    L.continuous.measurable.comp ((Q14.q14_continuous_bVec hm l).const_smul (Real.sqrt (2 * q))).measurable
  obtain ⟨ι, hι, e, -⟩ := HilbertCLTAux.exists_hilbertBasis_type (H := K)
  have := hι
  obtain ⟨-, h2⟩ := Q14.q14_form_of_family (ξ := μ) (u := fun l a => L (Real.sqrt (2 * q) • bVec m l a))
    hbm (M := Real.sqrt B) (fun l a => le_trans (le_abs_self _) (Real.abs_le_sqrt (hB l a)))
    (C := Kot.formComp (ContinuousLinearMap.adjoint L) (covForm m q μ))
    (fun x y => adjka_formComp_eq hm hq L x y) e
  rw [h2]
  calc ∑ l : Fin d, ∫ a, ‖L (Real.sqrt (2 * q) • bVec m l a)‖ ^ 2 ∂μ
      ≤ ∑ _l : Fin d, ∫ _a, B ∂μ := by
        refine Finset.sum_le_sum fun l _ => ?_
        refine integral_mono ?_ (integrable_const _) (fun a => hB l a)
        refine Integrable.of_bound (C := B) ((hbm l).norm.pow_const 2).aestronglyMeasurable
          (Filter.Eventually.of_forall fun a => ?_)
        rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
        exact hB l a
    _ = d * B := by simp

end Trace


section Bounds

variable {j m : ℝ}

theorem adjka_coordR_bVec (hj : (d : ℝ) / 2 + 1 < j) (hm : (d : ℝ) / 2 + 1 < m)
    (S : Finset (NonzeroLattice d)) (l : Fin d) (a : Torus d) (k : NonzeroLattice d) :
    NegSobolev.coord (adjkR m j S (bVec m l a)) k =
      if k ∈ S then NegSobolev.coord (bVec j l a) k else 0 := by
  rw [adjkR_coord, Q14.q14_coord_bVec hm, Q14.q14_coord_bVec hj]
  have hw := q48bW_pos k
  by_cases hk : k ∈ S
  · simp only [if_pos hk]
    have h1 : Lattice.jp k.1 = q48bW k := rfl
    rw [h1]
    calc q48bW k ^ (m - j) * (q48bW k ^ (-m) * Torus.partialDeriv l (Torus.realMode k) a)
        = (q48bW k ^ (m - j) * q48bW k ^ (-m)) * Torus.partialDeriv l (Torus.realMode k) a := by ring
      _ = q48bW k ^ (-j) * Torus.partialDeriv l (Torus.realMode k) a := by
          rw [← Real.rpow_add hw]; congr 2; ring
  · simp [hk]

theorem adjka_normR_le (hj : (d : ℝ) / 2 + 2 < j) (hm : (d : ℝ) / 2 + 2 < m)
    (S : Finset (NonzeroLattice d)) (l : Fin d) (a : Torus d) :
    ‖adjkR m j S (bVec m l a)‖ ^ 2 ≤ 2 * Q14.q14S d (j - 1) := by
  have hj1 : (d : ℝ) / 2 + 1 < j := by linarith
  have hm1 : (d : ℝ) / 2 + 1 < m := by linarith
  obtain ⟨hs1, hn1⟩ := NegSobolev.coord_sq (adjkR m j S (bVec m l a))
  obtain ⟨hs2, hn2⟩ := NegSobolev.coord_sq (bVec j l a)
  rw [hn1]
  refine le_trans ?_ (hn2 ▸ Q14.q14_norm_bVec_sq_le hj l a)
  refine Summable.tsum_le_tsum (fun k => ?_) hs1 hs2
  rw [adjka_coordR_bVec hj1 hm1]
  by_cases hk : k ∈ S
  · simp [hk]
  · simp [hk, sq_nonneg]

theorem adjka_normTail_le (hj : (d : ℝ) / 2 + 2 < j) (hm : (d : ℝ) / 2 + 2 < m)
    (S : Finset (NonzeroLattice d)) {ε : ℝ} (hε0 : 0 ≤ ε)
    (hε : ∀ k : NonzeroLattice d, k ∉ S → Lattice.jp k.1 ^ (-(2 * (m - j))) ≤ ε)
    (l : Fin d) (a : Torus d) :
    ‖(ContinuousLinearMap.id ℝ (NegSobolev d m) - adjkP m S) (bVec m l a)‖ ^ 2 ≤
      ε * (2 * Q14.q14S d (j - 1)) := by
  have hj1 : (d : ℝ) / 2 + 1 < j := by linarith
  have hm1 : (d : ℝ) / 2 + 1 < m := by linarith
  obtain ⟨hs1, hn1⟩ := NegSobolev.coord_sq ((ContinuousLinearMap.id ℝ (NegSobolev d m) - adjkP m S) (bVec m l a))
  obtain ⟨hs2, hn2⟩ := NegSobolev.coord_sq (bVec j l a)
  rw [hn1]
  have h2 : ε * ‖bVec j l a‖ ^ 2 ≤ ε * (2 * Q14.q14S d (j - 1)) :=
    mul_le_mul_of_nonneg_left (Q14.q14_norm_bVec_sq_le hj l a) hε0
  refine le_trans ?_ h2
  rw [hn2, ← tsum_mul_left]
  refine Summable.tsum_le_tsum (fun k => ?_) hs1 (hs2.mul_left ε)
  have hc : NegSobolev.coord ((ContinuousLinearMap.id ℝ (NegSobolev d m) - adjkP m S) (bVec m l a)) k =
      if k ∈ S then 0 else NegSobolev.coord (bVec m l a) k := by
    rw [ContinuousLinearMap.sub_apply, ContinuousLinearMap.id_apply]
    have e : NegSobolev.coord (bVec m l a - adjkP m S (bVec m l a)) k =
        NegSobolev.coord (bVec m l a) k - NegSobolev.coord (adjkP m S (bVec m l a)) k :=
      Q14.q14_coord_sub _ _ k
    rw [e, adjkP_coord]
    by_cases hk : k ∈ S <;> simp [hk]
  rw [hc]
  by_cases hk : k ∈ S
  · simp only [if_pos hk]
    nlinarith [sq_nonneg (NegSobolev.coord (bVec j l a) k)]
  · simp only [if_neg hk]
    have hw := q48bW_pos k
    rw [Q14.q14_coord_bVec hm1, Q14.q14_coord_bVec hj1]
    have h1 : Lattice.jp k.1 = q48bW k := rfl
    have e2 : (Lattice.jp k.1 ^ (-m) * Torus.partialDeriv l (Torus.realMode k) a) ^ 2 =
        Lattice.jp k.1 ^ (-(2 * (m - j))) * (Lattice.jp k.1 ^ (-j) * Torus.partialDeriv l (Torus.realMode k) a) ^ 2 := by
      rw [h1]
      rw [mul_pow, mul_pow, q48b_rpow_sq hw, q48b_rpow_sq hw, ← mul_assoc, ← Real.rpow_add hw]
      congr 2; ring
    rw [e2]
    exact mul_le_mul_of_nonneg_right (hε k hk) (sq_nonneg _)

end Bounds

end HRS.AdjK
