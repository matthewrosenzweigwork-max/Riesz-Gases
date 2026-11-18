import HRS.Sections.AdjKGlue

/-!
# ADJKB Aux1: compactness of `E_{m₁}`-balls in `E_m` (`m₁ < m`) and of the Arzelà-Ascoli set
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

variable {d : ℕ}

lemma adjkb_totallyBounded_of_approx {α : Type*} [PseudoMetricSpace α] (B : Set α)
    (h : ∀ ε > 0, ∃ K : Set α, IsCompact K ∧ ∀ x ∈ B, ∃ y ∈ K, dist x y ≤ ε) :
    TotallyBounded B := by
  rw [Metric.totallyBounded_iff]
  intro ε hε
  obtain ⟨K, hK, hKB⟩ := h (ε / 2) (by positivity)
  obtain ⟨t, htf, hKt⟩ := Metric.totallyBounded_iff.1 hK.totallyBounded (ε / 2) (by positivity)
  refine ⟨t, htf, fun x hx => ?_⟩
  obtain ⟨y, hyK, hxy⟩ := hKB x hx
  have := hKt hyK
  simp only [mem_iUnion, Metric.mem_ball] at this ⊢
  obtain ⟨z, hz, hyz⟩ := this
  exact ⟨z, hz, by linarith [dist_triangle x y z]⟩

/-- finite-support truncation of `F` to the modes in `S` -/
def adjkbTrunc (m : ℝ) (S : Finset (NonzeroLattice d)) (F : NegSobolev d m) : NegSobolev d m :=
  (∑ k ∈ S, lp.single 2 k (NegSobolev.coord F k) : lp (fun _ : NonzeroLattice d => ℝ) 2)

lemma adjkbTrunc_coord (m : ℝ) (S : Finset (NonzeroLattice d)) (F : NegSobolev d m)
    (k : NonzeroLattice d) :
    NegSobolev.coord (adjkbTrunc m S F) k = if k ∈ S then NegSobolev.coord F k else 0 := by
  unfold adjkbTrunc NegSobolev.coord
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.coeFn_single, Finset.sum_pi_single]

lemma adjkb_tail (m : ℝ) (S : Finset (NonzeroLattice d)) (F : NegSobolev d m)
    (w : NonzeroLattice d → ℝ) (hw0 : ∀ k, 0 ≤ w k) (Λ : ℝ) (hΛ : 0 < Λ)
    (hw : ∀ k, k ∉ S → Λ ≤ w k) (R2 : ℝ) (hR2 : 0 ≤ R2)
    (hF : ∀ s : Finset (NonzeroLattice d), ∑ k ∈ s, w k * NegSobolev.coord F k ^ 2 ≤ R2) :
    ‖F - adjkbTrunc m S F‖ ^ 2 ≤ R2 / Λ := by
  obtain ⟨-, h2⟩ := NegSobolev.coord_sq (F - adjkbTrunc m S F)
  rw [h2]
  refine tsum_le_of_sum_le' (div_nonneg hR2 hΛ.le) fun s => ?_
  have hco : ∀ k, NegSobolev.coord (F - adjkbTrunc m S F) k =
      if k ∈ S then 0 else NegSobolev.coord F k := by
    intro k
    have h1 := adjkbTrunc_coord m S F k
    have : NegSobolev.coord (F - adjkbTrunc m S F) k =
        NegSobolev.coord F k - NegSobolev.coord (adjkbTrunc m S F) k := rfl
    rw [this, h1]
    split_ifs <;> simp
  calc ∑ k ∈ s, NegSobolev.coord (F - adjkbTrunc m S F) k ^ 2
      ≤ ∑ k ∈ s, (w k / Λ) * NegSobolev.coord F k ^ 2 := by
        refine Finset.sum_le_sum fun k _ => ?_
        rw [hco k]
        by_cases hk : k ∈ S
        · rw [if_pos hk, zero_pow two_ne_zero]
          exact mul_nonneg (div_nonneg (hw0 k) hΛ.le) (sq_nonneg _)
        · rw [if_neg hk]
          have h1 : 1 ≤ w k / Λ := by rw [le_div_iff₀ hΛ]; linarith [hw k hk]
          nlinarith [sq_nonneg (NegSobolev.coord F k)]
    _ = (∑ k ∈ s, w k * NegSobolev.coord F k ^ 2) / Λ := by
        rw [Finset.sum_div]; refine Finset.sum_congr rfl fun k _ => ?_; ring
    _ ≤ R2 / Λ := div_le_div_of_nonneg_right (hF s) hΛ.le

lemma adjkb_finite_lowWeight (m m₁ : ℝ) (hm : m₁ < m) (Λ : ℝ) (hΛ : 0 < Λ) :
    {k : NonzeroLattice d | Lattice.jp k.1 ^ (2 * (m - m₁)) < Λ}.Finite := by
  set e : ℝ := 2 * (m - m₁) with he
  have hepos : 0 < e := by rw [he]; linarith
  set K0 : ℝ := Λ ^ (1 / e) with hK0
  have hK0pos : 0 < K0 := Real.rpow_pos_of_pos hΛ _
  have hfin := InitialDataAux.finite_modes (d := d) (s := (d : ℝ) + 1) (K := K0)
    (by linarith) hK0pos (by positivity)
  refine hfin.subset fun k hk => ?_
  simp only [mem_setOf_eq] at hk ⊢
  by_contra hcon
  push_neg at hcon
  have h1 : K0 ^ e < Lattice.jp k.1 ^ e := Real.rpow_lt_rpow hK0pos.le hcon hepos
  have h2 : K0 ^ e = Λ := by
    rw [hK0, ← Real.rpow_mul hΛ.le, one_div, inv_mul_cancel₀ hepos.ne', Real.rpow_one]
  linarith

theorem adjkb_ball_isCompact (m m₁ R : ℝ) (hm : m₁ < m) :
    IsCompact {F : NegSobolev d m | adjkEnergy m₁ m F ≤ ENNReal.ofReal (R ^ 2)} := by
  set B : Set (NegSobolev d m) := {F | adjkEnergy m₁ m F ≤ ENNReal.ofReal (R ^ 2)} with hB
  have hclosed : IsClosed B :=
    (adjkEnergy_lsc (d := d) m₁ m).isClosed_preimage (ENNReal.ofReal (R ^ 2))
  set w : NonzeroLattice d → ℝ := fun k => Lattice.jp k.1 ^ (2 * (m - m₁)) with hw
  have hw1 : ∀ k, 1 ≤ w k := fun k =>
    Real.one_le_rpow (Torus.jp_ge_one k.1) (by linarith)
  have hpart : ∀ F ∈ B, ∀ s : Finset (NonzeroLattice d),
      ∑ k ∈ s, w k * NegSobolev.coord F k ^ 2 ≤ R ^ 2 := by
    intro F hF s
    have h1 : ∑ k ∈ s, ENNReal.ofReal (w k * NegSobolev.coord F k ^ 2) ≤ ENNReal.ofReal (R ^ 2) :=
      (ENNReal.sum_le_tsum s).trans hF
    rw [← ENNReal.ofReal_sum_of_nonneg (fun k _ => by
      have := hw1 k; positivity)] at h1
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 h1
  have htb : TotallyBounded B := by
    refine adjkb_totallyBounded_of_approx B fun ε hε => ?_
    set Λ : ℝ := R ^ 2 / ε ^ 2 + 1 with hΛ
    have hΛpos : 0 < Λ := by positivity
    have hfin := adjkb_finite_lowWeight (d := d) m m₁ hm Λ hΛpos
    set S : Finset (NonzeroLattice d) := hfin.toFinset with hS
    set g : (NonzeroLattice d → ℝ) → lp (fun _ : NonzeroLattice d => ℝ) 2 := fun c =>
      (∑ k ∈ S, lp.single 2 k (c k) : lp (fun _ : NonzeroLattice d => ℝ) 2) with hg
    have hgc : Continuous g := by
      refine continuous_finset_sum _ fun k _ => ?_
      exact (lp.singleContinuousLinearMap ℝ (fun _ : NonzeroLattice d => ℝ) 2 k).continuous.comp
        (continuous_apply k)
    refine ⟨g '' (Set.pi univ fun _ => Icc (-|R|) |R|),
      (isCompact_univ_pi fun _ => isCompact_Icc).image hgc, fun F hF => ?_⟩
    refine ⟨adjkbTrunc m S F, ⟨fun k => NegSobolev.coord F k, ?_, rfl⟩, ?_⟩
    · intro k _
      have h1 := hpart F hF {k}
      simp only [Finset.sum_singleton] at h1
      have h2 : NegSobolev.coord F k ^ 2 ≤ R ^ 2 := by
        nlinarith [hw1 k, sq_nonneg (NegSobolev.coord F k)]
      exact abs_le.1 (sq_le_sq.1 h2)
    · rw [dist_eq_norm]
      have := adjkb_tail m S F w (fun k => by have := hw1 k; linarith) Λ hΛpos
        (fun k hk => by
          by_contra hcon
          push_neg at hcon
          exact hk (hfin.mem_toFinset.2 hcon)) (R ^ 2) (by positivity) (hpart F hF)
      have h3 : R ^ 2 / Λ ≤ ε ^ 2 := by
        rw [div_le_iff₀ hΛpos, hΛ]
        have : R ^ 2 / ε ^ 2 * ε ^ 2 = R ^ 2 := by field_simp
        nlinarith [sq_nonneg ε]
      by_contra hcon
      push_neg at hcon
      nlinarith [norm_nonneg (F - adjkbTrunc m S F)]
  exact htb.isCompact_of_isComplete hclosed.isComplete

end HRS.AdjK
