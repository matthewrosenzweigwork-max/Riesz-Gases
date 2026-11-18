import HRS.Energy.Commutator.RenormStjLocal

/-!
# Route S, packet STJ: the pointwise-in-`l` master inequality
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

variable {d : ℕ}

/-- the majorant of the `μ`-term of one ball -/
def muMaj (d : ℕ) (l ρ : ℝ) : ℝ := Wt d l ρ + mass d l ρ * (Wt d l (2 * ρ) + ρ * Wb d l (2 * ρ))

/-- the part of the per-slice majorant that does not involve the field term -/
def Amaj (d : ℕ) {N : ℕ} (CQ Cs L : ℝ) (X : Config d N) (η : Fin N → ℝ) (μ : Measure (Torus d)) (Λ : ℝ)
    (l : ℝ) : ℝ :=
  CQ * L * Ebar d X η μ Λ l + Cs * L * Ubar d η Λ l + 2 * L * (1 / (N : ℝ)) * Jl d l +
    (2 / (N : ℝ)) * ∑ i, Λ * L * muMaj d l (η i)

theorem P_pointwise (hd : 1 ≤ d) :
    ∃ CQ Cs : ℝ, 0 ≤ CQ ∧ 0 ≤ Cs ∧ ∀ {N : ℕ}, N ≠ 0 → ∀ {l : ℝ}, 0 < l → ∀ {X : Config d N} {η : Fin N → ℝ},
      (∀ i, 0 < η i ∧ η i ≤ 1 / 8) →
      (∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j)) →
      ∀ {μ : Measure (Torus d)} [IsFiniteMeasure μ] {Λ : ℝ}, 0 ≤ Λ →
      μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d)) → μ Set.univ = 1 →
      ∀ {L : ℝ}, 0 ≤ L → ∀ {v : Torus d → Euc d}, IsLipschitzVF L v →
      |offDiagPairing (commKernel (SliceAux.sgv l) v) X μ| ≤
        Amaj d CQ Cs L X η μ Λ l +
          (2 / (N : ℝ)) * ∑ i, |fieldT l v X (chS d l (η i) (X i)) μ i| := by
  obtain ⟨CQ, hCQ, hQ⟩ := Q_bound d hd
  obtain ⟨Cs, hCs, hSB⟩ := selfB_bound d hd
  refine ⟨CQ, Cs, hCQ.le, hCs.le, ?_⟩
  intro N hN l hl X η hη hdisj μ _ Λ hΛ0 hμ hμ1 L hL v hv
  have hη2 : ∀ i, 0 < η i ∧ η i < 1 / 2 := fun i => ⟨(hη i).1, by linarith [(hη i).2]⟩
  have hNr : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hc : ENNReal.ofReal Λ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hS := sliceCharges_stj hd hl hη2 hdisj
  have hdec := slice_decomp hd hN hl.le hS hc hμ hL hv
  have hQb := hQ hN hl.le hS hc hμ hμ1 hL hv
  have hE := energy_le_Ebar hd hN hl hη hdisj hΛ0 hμ hμ1
  have hmass : ∀ i, (chS d l (η i) (X i)).real Set.univ = mass d l (η i) := fun i => chS_real_univ l (η i) (X i)
  have hm1 : ∀ i, mass d l (η i) ≤ 1 := fun i => mass_le_one hd hl (hη2 i).1 (hη2 i).2
  have hm0 : ∀ i, 0 ≤ mass d l (η i) := fun i => by rw [← hmass i]; exact measureReal_nonneg
  -- self blocks
  have hSBi : ∀ i, |selfB l v (chS d l (η i) (X i))| ≤
      Cs * L * ((∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d (η i))).toReal + Fint d l (η i)) +
        2 * L * Jl d l := by
    intro i
    haveI := isFiniteMeasure_chS hd hl (hη2 i).1 (hη2 i).2 (X i)
    have h := hSB hl.le hL hv (σ := chS d l (η i) (X i))
      (fun h2 => fun x => chS_atom h2 l (hη2 i).1 (X i) x) (hS.Gii i)
    rw [quadForm_chS_eq hd hl (hη2 i).1 (hη2 i).2 (X i), hmass i] at h
    refine h.trans (add_le_add ?_ ?_)
    · exact mul_le_mul_of_nonneg_left (Self_le_dom hd hl (hη i).1 (hη i).2) (mul_nonneg hCs.le hL)
    · have hJ := Jl_nonneg (d := d) l
      have : mass d l (η i) ^ 2 ≤ 1 := by
        have := hm0 i; have := hm1 i; nlinarith
      nlinarith [mul_le_mul_of_nonneg_left this (mul_nonneg (by norm_num : (0 : ℝ) ≤ 2) hL), mul_nonneg hL hJ]
  -- the `μ`-blocks
  have hMUi : ∀ i, |muB l v (chS d l (η i) (X i)) μ (X i)| ≤ Λ * L * muMaj d l (η i) := by
    intro i
    haveI := isFiniteMeasure_chS hd hl (hη2 i).1 (hη2 i).2 (X i)
    have h := muB_bound hd hl.le hL hv (a := X i) (hη i).1.le
      (σ := chS d l (η i) (X i)) (hS.supp i) (hS.rep i) hc hμ
    rw [ENNReal.toReal_ofReal hΛ0, hmass i] at h
    exact h
  have hlin : ∀ a b c d' : ℝ, |a - b - c + d'| ≤ |a| + |b| + |c| + |d'| := by
    intro a b c d'
    rw [abs_le]
    constructor <;> nlinarith [neg_abs_le a, neg_abs_le b, neg_abs_le c, neg_abs_le d', le_abs_self a,
      le_abs_self b, le_abs_self c, le_abs_self d']
  rw [hdec]
  refine (hlin _ _ _ _).trans ?_
  have hA : |quadForm (commKernel (SliceAux.sgv l) v) (avgM fun i => chS d l (η i) (X i)) μ| ≤
      CQ * L * Ebar d X η μ Λ l := by
    refine hQb.trans ?_
    exact mul_le_mul_of_nonneg_left hE (mul_nonneg hCQ.le hL)
  have hB : |(1 / (N : ℝ)) ^ 2 * ∑ i, selfB l v (chS d l (η i) (X i))| ≤
      Cs * L * Ubar d η Λ l + 2 * L * (1 / (N : ℝ)) * Jl d l := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    have h1 : |∑ i, selfB l v (chS d l (η i) (X i))| ≤
        ∑ i, (Cs * L * ((∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d (η i))).toReal + Fint d l (η i)) +
          2 * L * Jl d l) :=
      (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hSBi i)
    have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 / (N : ℝ)) ^ 2)
    refine h2.trans ?_
    have h4 : 0 ≤ (2 * Λ / N) * ∑ i, Fint d l (η i) :=
      mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Fint_nonneg d l (η i))
    rw [Finset.sum_add_distrib, ← Finset.mul_sum, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
      nsmul_eq_mul]
    unfold Ubar
    have hCL : 0 ≤ Cs * L := mul_nonneg hCs.le hL
    have h5 := mul_le_mul_of_nonneg_left h4 hCL
    have e1 : (1 / (N : ℝ)) ^ 2 * (Cs * L * ∑ i, ((∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d (η i))).toReal +
        Fint d l (η i)) + (N : ℝ) * (2 * L * Jl d l)) =
        Cs * L * ((1 / (N : ℝ)) ^ 2 * ∑ i, ((∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d (η i))).toReal +
        Fint d l (η i))) + 2 * L * (1 / (N : ℝ)) * Jl d l := by
      field_simp
    rw [e1]
    nlinarith [h5]
  have hC : |(2 / (N : ℝ)) * ∑ i, muB l v (chS d l (η i) (X i)) μ (X i)| ≤
      (2 / (N : ℝ)) * ∑ i, Λ * L * muMaj d l (η i) := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left
      ((Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum fun i _ => hMUi i)) (by positivity)
  have hD : |(2 / (N : ℝ)) * ∑ i, fieldT l v X (chS d l (η i) (X i)) μ i| ≤
      (2 / (N : ℝ)) * ∑ i, |fieldT l v X (chS d l (η i) (X i)) μ i| := by
    rw [abs_mul, abs_of_nonneg (by positivity)]
    exact mul_le_mul_of_nonneg_left (Finset.abs_sum_le_sum_abs _ _) (by positivity)
  unfold Amaj
  linarith [hA, hB, hC, hD]

end HRS.Commutator.Stj
