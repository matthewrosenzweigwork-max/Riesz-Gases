import HRS.Energy.Commutator.RenormStjSelf

/-!
# Route S, packet STJ: the energy bound of one slice
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

variable {d : ℕ}

/-- the mass defect `∫ f_{l,η}` -/
def Fint (d : ℕ) (l η : ℝ) : ℝ := ∫ z : Torus d, fTrunc d l η z

theorem Fint_nonneg (d : ℕ) (l η : ℝ) : 0 ≤ Fint d l η := integral_nonneg fun z => le_max_right _ _

theorem integrable_fTrunc_vol (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) :
    Integrable (fTrunc d l η) (volume : Measure (Torus d)) := by
  refine Integrable.mono' (integrable_sliceGfull_vol hl.le) (EnergyAux.measurable_fTrunc l η).aestronglyMeasurable ?_
  filter_upwards [KernelAux.torus_ae_ne (by omega : 0 < d)] with z hz
  have h := EnergyAux.g_sub_f_pos hd hl hη hz
  have h0 : 0 ≤ fTrunc d l η z := le_max_right _ _
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  linarith

theorem int_f_le_Fint (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (a : Torus d)
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d))) :
    ∫ y, fTrunc d l η (a - y) ∂μ ≤ Λ * Fint d l η := by
  have hc : ENNReal.ofReal Λ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hnn : ∀ y, 0 ≤ fTrunc d l η (a - y) := fun y => le_max_right _ _
  have hi : Integrable (fun y => fTrunc d l η (a - y)) (ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
    ((integrable_fTrunc_vol hd hl hη).comp_sub_left a).smul_measure hc
  calc ∫ y, fTrunc d l η (a - y) ∂μ ≤ ∫ y, fTrunc d l η (a - y) ∂(ENNReal.ofReal Λ • (volume : Measure (Torus d))) :=
        integral_mono_measure hμ (Filter.Eventually.of_forall hnn) hi
    _ = Λ * Fint d l η := by
        rw [integral_smul_measure, ENNReal.toReal_ofReal hΛ0,
          integral_sub_left_eq_self (fun z => fTrunc d l η z) volume a]
        rfl

theorem energy_nonneg (hd : 1 ≤ d) {N : ℕ} (hN : N ≠ 0) {l : ℝ} (hl : 0 < l) {X : Fin N → Torus d}
    {η : Fin N → ℝ} (hS : SliceCharges l X η (fun i => chS d l (η i) (X i)))
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {c : ℝ≥0∞} (hc : c ≠ ⊤)
    (hμ : μ ≤ c • (volume : Measure (Torus d))) (hμ1 : μ Set.univ = 1) :
    0 ≤ quadForm (fun x y => sliceGfull d l (x - y)) (avgM fun i => chS d l (η i) (X i)) μ := by
  haveI : ∀ i, IsFiniteMeasure (chS d l (η i) (X i)) := hS.fin
  haveI := isFiniteMeasure_avgM hN (fun i => chS d l (η i) (X i))
  obtain ⟨hQHi, hQHle⟩ := LE_measures hd hl.le (avgM fun i => chS d l (η i) (X i)) μ
    (fun h0 => absurd h0 hl.ne')
    (fun h2 => ⟨avgM_atomless _ (hS.atom h2), atomless_of_le_vol hd hc hμ⟩) (G_int_sum hN hl.le hS hc hμ)
  refine le_trans ?_ hQHle
  exact integral_nonneg fun x => Finset.sum_nonneg fun j _ => sq_nonneg _

theorem energy_slice_le (hd : 1 ≤ d) {N : ℕ} (hN : N ≠ 0) {l : ℝ} (hl : 0 < l) {X : Fin N → Torus d}
    {η : Fin N → ℝ} (hη : ∀ i, 0 < η i ∧ η i < 1 / 2)
    (hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j))
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d))) (hμ1 : μ Set.univ = 1) :
    quadForm (fun x y => sliceGfull d l (x - y)) (avgM fun i => chS d l (η i) (X i)) μ ≤
      2 * modulatedEnergyKernel (sliceG d l) X μ + (1 / (N : ℝ)) ^ 2 * ∑ i, Self d l (η i) +
        (2 * Λ / N) * ∑ i, Fint d l (η i) := by
  have hc : ENNReal.ofReal Λ ≠ ⊤ := ENNReal.ofReal_ne_top
  have hμ0 : ∀ x, μ {x} = 0 := atomless_of_le_vol hd hc hμ
  haveI : IsProbabilityMeasure μ := ⟨hμ1⟩
  have hGμ : ∀ x, Integrable (fun y => sliceG d l (x - y)) μ := fun x =>
    integrable_sliceG_sub_mu hl.le x hc hμ
  have hμ1' : ∀ x, Integrable (fun y => sliceGfull d l (x - y)) μ := fun x => (hGμ x).add (integrable_const _)
  have hμ2 : Integrable (fun p : Torus d × Torus d => sliceGfull d l (p.1 - p.2)) (μ.prod μ) :=
    integrable_G_mu hl.le μ hc hμ
  have hμ2' : Integrable (fun p : Torus d × Torus d => sliceG d l (p.1 - p.2)) (μ.prod μ) :=
    integrable_sliceG_of_full hμ2
  have hid := energy_identity_slice hd hl μ hμ0 hμ1' hμ2 X η hη hdisj
  have hE : quadForm (fun x y => sliceGfull d l (x - y)) (avgM fun i => chS d l (η i) (X i)) μ =
      quadForm (fun x y => sliceGfull d l (x - y)) (chargeMeasure (smearT d l) η X) μ := rfl
  rw [hE, hid]
  -- the pieces
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hfi : ∀ i, Integrable (fun y => fTrunc d l (η i) (X i - y)) μ := by
    intro i
    have := ((integrable_fTrunc_vol hd hl (hη i).1).comp_sub_left (X i)).smul_measure hc
    exact this.mono_measure hμ
  have hA : ∀ i, ∫ y, (sliceGfull d l (X i - y) - fTrunc d l (η i) (X i - y)) ∂μ =
      (∫ y, sliceG d l (X i - y) ∂μ) + 1 / l - ∫ y, fTrunc d l (η i) (X i - y) ∂μ := by
    intro i
    rw [integral_sub (hμ1' (X i)) (hfi i)]
    have e : ∀ y, sliceGfull d l (X i - y) = sliceG d l (X i - y) + 1 / l := fun y => rfl
    simp_rw [e]
    rw [integral_add (hGμ (X i)) (integrable_const _), integral_const]
    simp [hμ1]
  have hB : ∫ x, ∫ y, sliceGfull d l (x - y) ∂μ ∂μ = (∫ x, ∫ y, sliceG d l (x - y) ∂μ ∂μ) + 1 / l := by
    have e : ∀ x y : Torus d, sliceGfull d l (x - y) = sliceG d l (x - y) + 1 / l := fun x y => rfl
    simp_rw [e]
    have h1 : ∀ x, ∫ y, (sliceG d l (x - y) + 1 / l) ∂μ = (∫ y, sliceG d l (x - y) ∂μ) + 1 / l := by
      intro x
      rw [integral_add (hGμ x) (integrable_const _), integral_const]
      simp [hμ1]
    simp_rw [h1]
    have hint : Integrable (fun x => ∫ y, sliceG d l (x - y) ∂μ) μ := hμ2'.integral_prod_left
    rw [integral_add hint (integrable_const _), integral_const]
    simp [hμ1]
  have hC : ∀ i, ∑ j ∈ Finset.univ.erase i, sliceGfull d l (X i - X j) =
      (∑ j ∈ Finset.univ.erase i, sliceG d l (X i - X j)) + ((N : ℝ) - 1) / l := by
    intro i
    have e : ∀ j, sliceGfull d l (X i - X j) = sliceG d l (X i - X j) + 1 / l := fun j => rfl
    simp_rw [e]
    rw [Finset.sum_add_distrib, Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
    simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : ((N - 1 : ℕ) : ℝ) = (N : ℝ) - 1 := by
      rw [Nat.cast_sub (Nat.one_le_iff_ne_zero.mpr hN)]; simp
    rw [this]; ring
  have hD : ∀ i, ∫ x, ∫ y, sliceGfull d l (x - y) ∂(smearT d l (η i)) ∂(smearT d l (η i)) =
      Self d l (η i) + (mass d l (η i)) ^ 2 / l := by
    intro i; unfold Self; ring
  simp_rw [hA, hB, hC, hD]
  have hm1 : ∀ i, mass d l (η i) ≤ 1 := fun i => mass_le_one hd hl (hη i).1 (hη i).2
  have hm0 : ∀ i, 0 ≤ mass d l (η i) := fun i => mass_nonneg d l (η i)
  have hM2 : ∑ i, (mass d l (η i)) ^ 2 ≤ N := by
    calc ∑ i, (mass d l (η i)) ^ 2 ≤ ∑ _i : Fin N, (1 : ℝ) :=
          Finset.sum_le_sum fun i _ => by nlinarith [hm1 i, hm0 i]
      _ = N := by simp
  have hFf : ∑ i, ∫ y, fTrunc d l (η i) (X i - y) ∂μ ≤ Λ * ∑ i, Fint d l (η i) := by
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun i _ => int_f_le_Fint hd hl (hη i).1 (X i) hΛ0 hμ
  unfold modulatedEnergyKernel modulatedEnergy
  simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ,
    Fintype.card_fin, nsmul_eq_mul, add_div, div_pow, one_pow] at *
  have hsd : ∑ x, mass d l (η x) ^ 2 / l = (∑ x, mass d l (η x) ^ 2) / l := (Finset.sum_div _ _ _).symm
  rw [hsd]
  generalize (∑ x, ∑ j ∈ Finset.univ.erase x, sliceG d l (X x - X j)) = A
  generalize (∑ x, ∫ (y : Torus d), sliceG d l (X x - y) ∂μ) = B
  generalize (∫ (x : Torus d), ∫ (y : Torus d), sliceG d l (x - y) ∂μ ∂μ) = C
  generalize (∑ x, Self d l (η x)) = Sf
  generalize (∑ x, mass d l (η x) ^ 2) = M2 at hM2 ⊢
  generalize (∑ x, ∫ (y : Torus d), fTrunc d l (η x) (X x - y) ∂μ) = Ff at hFf ⊢
  generalize (∑ i, Fint d l (η i)) = Fi at hFf ⊢
  have hlpos : 0 < l := hl
  have h1 : M2 / (N : ℝ) ^ 2 ≤ 1 / N := by
    rw [div_le_iff₀ (by positivity)]
    have : 1 / (N : ℝ) * (N : ℝ) ^ 2 = N := by field_simp
    linarith
  have h2 : (1 / l) * (M2 / (N : ℝ) ^ 2 - 1 / N) ≤ 0 :=
    mul_nonpos_of_nonneg_of_nonpos (by positivity) (by linarith)
  have h3 : (2 / (N : ℝ)) * Ff ≤ (2 / (N : ℝ)) * (Λ * Fi) := mul_le_mul_of_nonneg_left hFf (by positivity)
  have hident : (1 / (N : ℝ) ^ 2 * (A + N * ((N - 1) / l)) + 1 / (N : ℝ) ^ 2 * (Sf + M2 / l) -
      2 / N * (B + N * (1 / l) - Ff) + (C + 1 / l)) -
      (2 * (1 / (2 * (N : ℝ) ^ 2) * A - 1 / N * B + 1 / 2 * C) + 1 / (N : ℝ) ^ 2 * Sf) =
      2 / (N : ℝ) * Ff + (1 / l) * (M2 / (N : ℝ) ^ 2 - 1 / N) := by
    field_simp
    ring
  have h4 : 2 * Λ / (N : ℝ) * Fi = (2 / (N : ℝ)) * (Λ * Fi) := by ring
  rw [h4]
  linarith

end HRS.Commutator.Stj
