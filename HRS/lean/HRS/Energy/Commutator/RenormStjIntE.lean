import HRS.Energy.Commutator.RenormStjFubini

/-!
# Route S, packet STJ: the `l`-integrated energy bound
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

variable {d : ℕ}

theorem integrable_of_lintegral_le {f : ℝ → ℝ} (hf0 : ∀ l ∈ Ioi (0 : ℝ), 0 ≤ f l)
    (hfm : AEStronglyMeasurable f (volume.restrict (Ioi (0 : ℝ)))) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (f l) ≤ ENNReal.ofReal B) :
    IntegrableOn f (Ioi 0) ∧ ∫ l in Ioi (0 : ℝ), f l ≤ B := by
  have hnn : 0 ≤ᵐ[volume.restrict (Ioi (0 : ℝ))] f :=
    (ae_restrict_iff' measurableSet_Ioi).mpr (Filter.Eventually.of_forall hf0)
  have hfin : ∫⁻ l in Ioi (0 : ℝ), ENNReal.ofReal (f l) ≠ ⊤ :=
    (lt_of_le_of_lt hB ENNReal.ofReal_lt_top).ne
  have hint : IntegrableOn f (Ioi 0) := (lintegral_ofReal_ne_top_iff_integrable hfm hnn).mp hfin
  refine ⟨hint, ?_⟩
  rw [integral_eq_lintegral_of_nonneg_ae hnn hfm]
  exact (ENNReal.toReal_mono ENNReal.ofReal_ne_top hB).trans (le_of_eq (ENNReal.toReal_ofReal hB0))

/-- the (`l`-dependent) majorant of the self energies and mass defects -/
def Ubar (d : ℕ) {N : ℕ} (η : Fin N → ℝ) (Λ : ℝ) (l : ℝ) : ℝ :=
  (1 / (N : ℝ)) ^ 2 * ∑ i, ((∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d (η i))).toReal + Fint d l (η i)) +
    (2 * Λ / N) * ∑ i, Fint d l (η i)

/-- the majorant of the slice energy -/
def Ebar (d : ℕ) {N : ℕ} (X : Config d N) (η : Fin N → ℝ) (μ : Measure (Torus d)) (Λ : ℝ) (l : ℝ) : ℝ :=
  2 * modulatedEnergyKernel (sliceG d l) X μ + Ubar d η Λ l

theorem energy_le_Ebar (hd : 1 ≤ d) {N : ℕ} (hN : N ≠ 0) {l : ℝ} (hl : 0 < l) {X : Fin N → Torus d}
    {η : Fin N → ℝ} (hη : ∀ i, 0 < η i ∧ η i ≤ 1 / 8)
    (hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j))
    {μ : Measure (Torus d)} [IsFiniteMeasure μ] {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus d))) (hμ1 : μ Set.univ = 1) :
    quadForm (fun x y => sliceGfull d l (x - y)) (avgM fun i => chS d l (η i) (X i)) μ ≤
      Ebar d X η μ Λ l := by
  have hη2 : ∀ i, 0 < η i ∧ η i < 1 / 2 := fun i => ⟨(hη i).1, by linarith [(hη i).2]⟩
  refine (energy_slice_le hd hN hl hη2 hdisj hΛ0 hμ hμ1).trans ?_
  unfold Ebar Ubar
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have h1 : ∑ i, Self d l (η i) ≤
      ∑ i, ((∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d (η i))).toReal + Fint d l (η i)) :=
    Finset.sum_le_sum fun i _ => Self_le_dom hd hl (hη i).1 (hη i).2
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 / (N : ℝ)) ^ 2)
  linarith

theorem measurable_Gdom (d : ℕ) (ν : Measure (Torus d)) [SFinite ν] :
    Measurable fun l : ℝ => ∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂ν := by
  have hK : Measurable fun p : ℝ × Torus d => ENNReal.ofReal |sliceG d p.1 p.2| :=
    ENNReal.measurable_ofReal.comp (measurable_sliceG_uncurry d).abs
  exact hK.lintegral_prod_right' (ν := ν)

theorem Ubar_integral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) {c : ℝ}
    (hc : 0 < c)
    (hker : ∀ x : Torus d, x ≠ 0 →
      periodicRiesz d s x = c * ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * sliceG d l x) :
    ∃ KU : ℝ, 0 ≤ KU ∧ ∀ {N : ℕ}, N ≠ 0 → ∀ (η : Fin N → ℝ), (∀ i, 0 < η i ∧ η i ≤ 1 / 8) →
      ∀ {Λ : ℝ}, 0 ≤ Λ →
      IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * Ubar d η Λ l) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * Ubar d η Λ l ≤
        KU * ((1 / (N : ℝ)) ^ 2 * ∑ i, (η i ^ (-s) + 1) +
          (1 + Λ) * (1 / (N : ℝ)) * ∑ i, η i ^ ((d : ℝ) - s)) := by
  obtain ⟨CU, hCU0, hCU⟩ := Gdom_integral hd hs0 hs hsd hc hker
  obtain ⟨CF, hCF0, hCF⟩ := Fint_stieltjes hd hs0.le hs hsd
  refine ⟨CU + 3 * CF, by positivity, fun {N} hN η hη {Λ} hΛ => ?_⟩
  have hη2 : ∀ i, 0 < η i ∧ η i < 1 / 2 := fun i => ⟨(hη i).1, by linarith [(hη i).2]⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hβ1 : bexp d s < 1 := by unfold bexp; linarith
  -- the two kinds of terms
  have T1 : ∀ i, IntegrableOn (fun l : ℝ => l ^ (-bexp d s) *
        (∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d (η i))).toReal) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * (∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d (η i))).toReal ≤
        CU * ((η i) ^ (-s) + 1) := by
    intro i
    have hpos : 0 ≤ CU * ((η i) ^ (-s) + 1) := by
      have := Real.rpow_nonneg (hη i).1.le (-s); positivity
    refine integrable_of_lintegral_le (fun l hl => mul_nonneg (Real.rpow_nonneg (le_of_lt hl) _) ENNReal.toReal_nonneg)
      ((measurable_id.pow_const _).mul (measurable_Gdom d (domT d (η i))).ennreal_toReal).aestronglyMeasurable
      hpos ?_
    refine le_trans ?_ (hCU (η i) (hη i).1 (hη i).2)
    refine setLIntegral_mono' measurableSet_Ioi fun l hl => ?_
    have hl' : (0 : ℝ) < l := hl
    rw [ENNReal.ofReal_mul (Real.rpow_nonneg hl'.le _)]
    exact mul_le_mul' le_rfl ENNReal.ofReal_toReal_le
  have T2 := fun i => hCF (η i) (hη2 i).1 (hη2 i).2
  have hrw : ∀ l : ℝ, l ^ (-bexp d s) * Ubar d η Λ l =
      (1 / (N : ℝ)) ^ 2 * ∑ i, (l ^ (-bexp d s) * (∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d (η i))).toReal) +
      ((1 / (N : ℝ)) ^ 2 + 2 * Λ / N) * ∑ i, (l ^ (-bexp d s) * ∫ z : Torus d, fTrunc d l (η i) z) := by
    intro l
    unfold Ubar Fint
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [hrw]
  have hI1 : IntegrableOn (fun l : ℝ => ∑ i, (l ^ (-bexp d s) *
      (∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d (η i))).toReal)) (Ioi 0) :=
    integrable_finset_sum _ fun i _ => (T1 i).1
  have hI2 : IntegrableOn (fun l : ℝ => ∑ i, (l ^ (-bexp d s) * ∫ z : Torus d, fTrunc d l (η i) z)) (Ioi 0) :=
    integrable_finset_sum _ fun i _ => (T2 i).1
  refine ⟨(hI1.const_mul _).add (hI2.const_mul _), ?_⟩
  rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul,
    integral_finset_sum _ fun i _ => (T1 i).1, integral_finset_sum _ fun i _ => (T2 i).1]
  have hs1 : ∑ i, ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * (∫⁻ z, ENNReal.ofReal |sliceG d l z| ∂(domT d (η i))).toReal ≤
      ∑ i, CU * ((η i) ^ (-s) + 1) := Finset.sum_le_sum fun i _ => (T1 i).2
  have hs2 : ∑ i, ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * ∫ z : Torus d, fTrunc d l (η i) z ≤
      ∑ i, CF * (η i) ^ ((d : ℝ) - s) := Finset.sum_le_sum fun i _ => (T2 i).2
  have hu : (1 / (N : ℝ)) ≤ 1 := by
    rw [div_le_one hNpos]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hu0 : 0 ≤ 1 / (N : ℝ) := by positivity
  have hq : ((1 / (N : ℝ)) ^ 2 + 2 * Λ / N) ≤ 3 * ((1 + Λ) * (1 / (N : ℝ))) := by
    have : (1 / (N : ℝ)) ^ 2 ≤ 1 / (N : ℝ) := by nlinarith
    have h2 : 2 * Λ / (N : ℝ) = 2 * Λ * (1 / (N : ℝ)) := by ring
    rw [h2]
    nlinarith [mul_nonneg hΛ hu0]
  have hq0 : 0 ≤ ((1 / (N : ℝ)) ^ 2 + 2 * Λ / N) := by positivity
  have hA0 : 0 ≤ ∑ i, CF * (η i) ^ ((d : ℝ) - s) :=
    Finset.sum_nonneg fun i _ => mul_nonneg hCF0 (Real.rpow_nonneg (hη i).1.le _)
  have hP : ∑ i, CU * ((η i) ^ (-s) + 1) = CU * ∑ i, ((η i) ^ (-s) + 1) := (Finset.mul_sum _ _ _).symm
  have hP2 : ∑ i, CF * (η i) ^ ((d : ℝ) - s) = CF * ∑ i, (η i) ^ ((d : ℝ) - s) := (Finset.mul_sum _ _ _).symm
  rw [hP] at hs1
  rw [hP2] at hs2 hA0
  have hB0 : 0 ≤ ∑ i, (η i) ^ ((d : ℝ) - s) := Finset.sum_nonneg fun i _ => Real.rpow_nonneg (hη i).1.le _
  have hC0 : 0 ≤ ∑ i, ((η i) ^ (-s) + 1) :=
    Finset.sum_nonneg fun i _ => by have := Real.rpow_nonneg (hη i).1.le (-s); linarith
  have h5 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ (1 / (N : ℝ)) ^ 2)
  have h6 := mul_le_mul_of_nonneg_left hs2 hq0
  have h7 : ((1 / (N : ℝ)) ^ 2 + 2 * Λ / N) * (CF * ∑ i, (η i) ^ ((d : ℝ) - s)) ≤
      3 * ((1 + Λ) * (1 / (N : ℝ))) * (CF * ∑ i, (η i) ^ ((d : ℝ) - s)) :=
    mul_le_mul_of_nonneg_right hq hA0
  have e1 : 0 ≤ CF * ((1 / (N : ℝ)) ^ 2 * ∑ i, ((η i) ^ (-s) + 1)) :=
    mul_nonneg hCF0 (mul_nonneg (by positivity) hC0)
  have e2 : 0 ≤ CU * ((1 + Λ) * (1 / (N : ℝ)) * ∑ i, (η i) ^ ((d : ℝ) - s)) :=
    mul_nonneg hCU0 (mul_nonneg (mul_nonneg (by positivity) hu0) hB0)
  refine le_trans (b := (1 / (N : ℝ)) ^ 2 * (CU * ∑ i, ((η i) ^ (-s) + 1)) +
        3 * ((1 + Λ) * (1 / (N : ℝ))) * (CF * ∑ i, (η i) ^ ((d : ℝ) - s))) (by linarith [h5, h6, h7]) ?_
  nlinarith [e1, e2]

theorem Ebar_integral (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 < s) (hs : (d : ℝ) - 2 < s) (hsd : s < d) {c : ℝ}
    (hc : 0 < c)
    (hker : ∀ x : Torus d, x ≠ 0 →
      periodicRiesz d s x = c * ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * sliceG d l x) :
    ∃ KE : ℝ, 0 ≤ KE ∧ ∀ {N : ℕ}, N ≠ 0 → ∀ (X : Config d N), (∀ i j, i ≠ j → X i ≠ X j) →
      ∀ (η : Fin N → ℝ), (∀ i, 0 < η i ∧ η i ≤ 1 / 8) → ∀ {Λ : ℝ}, 0 ≤ Λ → ∀ {ρ : Torus d → ℝ},
      (∀ x, ρ x ≤ Λ) →
      IntegrableOn (fun l : ℝ => l ^ (-bexp d s) * Ebar d X η (withDensityReal ρ) Λ l) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * Ebar d X η (withDensityReal ρ) Λ l ≤
        (2 / c) * rieszEnergy d s X (withDensityReal ρ) +
        KE * ((1 / (N : ℝ)) ^ 2 * ∑ i, (η i ^ (-s) + 1) +
          (1 + Λ) * (1 / (N : ℝ)) * ∑ i, η i ^ ((d : ℝ) - s)) := by
  obtain ⟨CT, hCT0, hCT⟩ := Theta_bound hd hs0.le hs hsd hc hker
  obtain ⟨KU, hKU0, hKU⟩ := Ubar_integral hd hs0 hs hsd hc hker
  have hsc : ∀ r : ℝ, selfScale d s r = r ^ (-s) := fun r => by unfold selfScale; rw [if_neg hs0.ne']
  set Θ : Torus d → ℝ := fun z => c⁻¹ * KernelGrad.tdist z 0 ^ (-s) + CT with hΘ
  have hΘm : Measurable Θ :=
    (measurable_const.mul (EnergyAux.measurable_tdist_zero.pow_const _)).add measurable_const
  have hΘi : Integrable Θ :=
    ((SliceAux.integrable_tdist_rpow (by omega : 0 < d) hs0.le hsd).const_mul c⁻¹).add (integrable_const CT)
  have hΘ0 : ∀ z, 0 ≤ Θ z := fun z => by
    simp only [hΘ]; have := Real.rpow_nonneg (KernelGrad.tdist_nonneg z 0) (-s); positivity
  have hΘb : ∀ z : Torus d, z ≠ 0 → ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * |sliceG d l z| ≤ Θ z := by
    intro z hz
    have := (hCT z hz).2
    rw [hsc] at this
    exact this
  refine ⟨KU, hKU0, fun {N} hN X hX η hη {Λ} hΛ {ρ} hρΛ => ?_⟩
  obtain ⟨hEq, hInt⟩ := riesz_energy_fubini hd hs0.le hs hsd hker hΘm hΘi hΘ0 hΘb X hX hρΛ hΛ
  obtain ⟨hUi, hUb⟩ := hKU hN η hη hΛ
  have hrw : ∀ l : ℝ, l ^ (-bexp d s) * Ebar d X η (withDensityReal ρ) Λ l =
      2 * (l ^ (-bexp d s) * modulatedEnergyKernel (sliceG d l) X (withDensityReal ρ)) +
        l ^ (-bexp d s) * Ubar d η Λ l := fun l => by unfold Ebar; ring
  simp_rw [hrw]
  refine ⟨(hInt.const_mul 2).add hUi, ?_⟩
  rw [integral_add (hInt.const_mul 2) hUi, integral_const_mul]
  have h1 : ∫ l in Ioi (0 : ℝ), l ^ (-bexp d s) * modulatedEnergyKernel (sliceG d l) X (withDensityReal ρ) =
      rieszEnergy d s X (withDensityReal ρ) / c := by
    rw [hEq]; field_simp
  rw [h1]
  have : 2 * (rieszEnergy d s X (withDensityReal ρ) / c) = (2 / c) * rieszEnergy d s X (withDensityReal ρ) := by ring
  linarith

end HRS.Commutator.Stj
