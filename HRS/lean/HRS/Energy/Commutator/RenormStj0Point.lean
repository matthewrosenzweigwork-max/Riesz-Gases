import HRS.Energy.Commutator.RenormStj0Local

/-!
# Route S, packet STJ: the pointwise-in-`l` master inequality for `d = 1`, `s = 0`
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

/-- the self-block majorant (pointwise bound of `selfB`, no self energy) -/
def SBmaj {N : ℕ} (Ksg L : ℝ) (η : Fin N → ℝ) (l : ℝ) : ℝ :=
  (1 / (N : ℝ)) ^ 2 * ∑ i, L * (4 * Ksg * η i) * mass 1 l (η i)

/-- the part of the per-slice majorant that does not involve the field term (`d = 1`, `s = 0`) -/
def Amaj0 {N : ℕ} (CQ Ksg L : ℝ) (X : Config 1 N) (η : Fin N → ℝ) (μ : Measure (Torus 1)) (Λ : ℝ)
    (l : ℝ) : ℝ :=
  CQ * L * Ebar0 X η μ Λ l + SBmaj Ksg L η l + (2 / (N : ℝ)) * ∑ i, Λ * L * muMaj 1 l (η i)

theorem P_pointwise0 :
    ∃ CQ Ksg : ℝ, 0 ≤ CQ ∧ 0 ≤ Ksg ∧ ∀ {N : ℕ}, N ≠ 0 → ∀ {l : ℝ}, 0 < l → ∀ {X : Config 1 N} {η : Fin N → ℝ},
      (∀ i, 0 < η i ∧ η i ≤ 1 / 8) →
      (∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j)) →
      ∀ {μ : Measure (Torus 1)} [IsFiniteMeasure μ] {Λ : ℝ}, 0 ≤ Λ →
      μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus 1)) → μ Set.univ = 1 →
      ∀ {L : ℝ}, 0 ≤ L → ∀ {v : Torus 1 → Euc 1}, IsLipschitzVF L v →
      |offDiagPairing (commKernel (SliceAux.sgv l) v) X μ| ≤
        Amaj0 CQ Ksg L X η μ Λ l +
          (2 / (N : ℝ)) * ∑ i, |fieldT l v X (chS 1 l (η i) (X i)) μ i| := by
  obtain ⟨CQ, hCQ, hQ⟩ := Q_bound 1 le_rfl
  obtain ⟨Ksg, hKsg0, hKsg⟩ := sgv_unif_bound (d := 1) le_rfl
  refine ⟨CQ, Ksg, hCQ.le, hKsg0, ?_⟩
  intro N hN l hl X η hη hdisj μ _ Λ hΛ0 hμ hμ1 L hL v hv
  have hη2 : ∀ i, 0 < η i ∧ η i < 1 / 2 := fun i => ⟨(hη i).1, by linarith [(hη i).2]⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hc : ENNReal.ofReal Λ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hS := sliceCharges_stj (d := 1) le_rfl hl hη2 hdisj
  have hdec := slice_decomp (d := 1) le_rfl hN hl.le hS hc hμ hL hv
  have hQb := hQ hN hl.le hS hc hμ hμ1 hL hv
  have hE := energy_le_Ebar0 hN hl hη hdisj hΛ0 hμ hμ1
  have hmass : ∀ i, (chS 1 l (η i) (X i)).real Set.univ = mass 1 l (η i) := fun i => chS_real_univ l (η i) (X i)
  have hm1 : ∀ i, mass 1 l (η i) ≤ 1 := fun i => mass_le_one le_rfl hl (hη2 i).1 (hη2 i).2
  have hm0 : ∀ i, 0 ≤ mass 1 l (η i) := fun i => by rw [← hmass i]; exact measureReal_nonneg
  -- self blocks
  have hSBi : ∀ i, |selfB l v (chS 1 l (η i) (X i))| ≤ L * (4 * Ksg * η i) * mass 1 l (η i) := by
    intro i
    haveI := isFiniteMeasure_chS (d := 1) le_rfl hl (hη2 i).1 (hη2 i).2 (X i)
    have hK2 : ∀ z : Torus 1, KernelGrad.tdist z 0 ≤ 2 * η i →
        KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ ≤ 4 * Ksg * η i := by
      intro z hz
      by_cases hz0 : z = 0
      · subst hz0
        rw [CoercAux.tdist_self, zero_mul]; have := (hη i).1; positivity
      · have h := hKsg l hl.le z hz0
        simp only [Nat.cast_one, sub_self, Real.rpow_zero] at h
        have ht := KernelGrad.tdist_nonneg z 0
        calc KernelGrad.tdist z 0 * ‖SliceAux.sgv l z‖ ≤ (2 * η i) * (Ksg * (1 + 1)) :=
              mul_le_mul hz h (norm_nonneg _) (by have := (hη i).1; positivity)
          _ = 4 * Ksg * η i := by ring
    have h := selfB_pointwise hl.le hL hv (a := X i) (η := η i)
      (hS.supp i) hK2
    rw [hmass i] at h
    refine h.trans ?_
    have : mass 1 l (η i) ^ 2 ≤ mass 1 l (η i) := by nlinarith [hm0 i, hm1 i]
    have hk : 0 ≤ L * (4 * Ksg * η i) := by have := (hη i).1; positivity
    exact mul_le_mul_of_nonneg_left this hk
  have hMUi : ∀ i, |muB l v (chS 1 l (η i) (X i)) μ (X i)| ≤ Λ * L * muMaj 1 l (η i) := by
    intro i
    haveI := isFiniteMeasure_chS (d := 1) le_rfl hl (hη2 i).1 (hη2 i).2 (X i)
    have h := muB_bound le_rfl hl.le hL hv (a := X i) (hη i).1.le
      (σ := chS 1 l (η i) (X i)) (hS.supp i) (hS.rep i) hc hμ
    rw [ENNReal.toReal_ofReal hΛ0, hmass i] at h
    exact h
  have hlin : ∀ a b c d' : ℝ, |a - b - c + d'| ≤ |a| + |b| + |c| + |d'| := by
    intro a b c d'
    rw [abs_le]
    constructor <;> nlinarith [neg_abs_le a, neg_abs_le b, neg_abs_le c, neg_abs_le d', le_abs_self a,
      le_abs_self b, le_abs_self c, le_abs_self d']
  rw [hdec]
  refine (hlin _ _ _ _).trans ?_
  have hA : |quadForm (commKernel (SliceAux.sgv l) v) (avgM fun i => chS 1 l (η i) (X i)) μ| ≤
      CQ * L * Ebar0 X η μ Λ l := by
    refine hQb.trans ?_
    exact mul_le_mul_of_nonneg_left hE (mul_nonneg hCQ.le hL)
  have hB : |(1 / (N : ℝ)) ^ 2 * ∑ i, selfB l v (chS 1 l (η i) (X i))| ≤ SBmaj Ksg L η l := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    unfold SBmaj
    exact mul_le_mul_of_nonneg_left
      ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hSBi i)) (by positivity)
  have hC : |(2 / (N : ℝ)) * ∑ i, muB l v (chS 1 l (η i) (X i)) μ (X i)| ≤
      (2 / (N : ℝ)) * ∑ i, Λ * L * muMaj 1 l (η i) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hMUi i)) (by positivity)
  have hD : |(2 / (N : ℝ)) * ∑ i, fieldT l v X (chS 1 l (η i) (X i)) μ i| ≤
      (2 / (N : ℝ)) * ∑ i, |fieldT l v X (chS 1 l (η i) (X i)) μ i| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
  unfold Amaj0
  linarith [hA, hB, hC, hD]

end HRS.Commutator.Stj
