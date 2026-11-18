import HRS.Energy.Commutator.RenormStj0Self

/-!
# Route S, packet STJ: the `l`-integrated energy bound for `d = 1`, `s = 0` (sharp)
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS.Commutator.Renorm

namespace HRS.Commutator.Stj

/-- `N⁻² ∑ -log η_i`, the sharp self-energy sum -/
def Sig0 {N : ℕ} (η : Fin N → ℝ) : ℝ := (1 / (N : ℝ)) ^ 2 * ∑ i, -Real.log (η i)

/-- the sharp majorant of the self energies and mass defects (`d = 1`) -/
def Ubar0 {N : ℕ} (η : Fin N → ℝ) (Λ : ℝ) (l : ℝ) : ℝ :=
  (1 / (N : ℝ)) ^ 2 * ∑ i, (|sliceG 1 l (Torus.mk (e1 (η i)))| + 2 * Fint 1 l (η i)) +
    (2 * Λ / N) * ∑ i, Fint 1 l (η i)

/-- the sharp majorant of the slice energy (`d = 1`) -/
def Ebar0 {N : ℕ} (X : Config 1 N) (η : Fin N → ℝ) (μ : Measure (Torus 1)) (Λ : ℝ) (l : ℝ) : ℝ :=
  2 * modulatedEnergyKernel (sliceG 1 l) X μ + Ubar0 η Λ l

theorem energy_le_Ebar0 {N : ℕ} (hN : N ≠ 0) {l : ℝ} (hl : 0 < l) {X : Fin N → Torus 1}
    {η : Fin N → ℝ} (hη : ∀ i, 0 < η i ∧ η i ≤ 1 / 8)
    (hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j))
    {μ : Measure (Torus 1)} [IsFiniteMeasure μ] {Λ : ℝ} (hΛ0 : 0 ≤ Λ)
    (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus 1))) (hμ1 : μ Set.univ = 1) :
    quadForm (fun x y => sliceGfull 1 l (x - y)) (avgM fun i => chS 1 l (η i) (X i)) μ ≤
      Ebar0 X η μ Λ l := by
  have hη2 : ∀ i, 0 < η i ∧ η i < 1 / 2 := fun i => ⟨(hη i).1, by linarith [(hη i).2]⟩
  refine (energy_slice_le le_rfl hN hl hη2 hdisj hΛ0 hμ hμ1).trans ?_
  unfold Ebar0 Ubar0
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have h1 : ∑ i, Self 1 l (η i) ≤ ∑ i, (|sliceG 1 l (Torus.mk (e1 (η i)))| + 2 * Fint 1 l (η i)) :=
    Finset.sum_le_sum fun i _ => by
      refine (Self_le_G_d1 hl (hη i).1 (hη i).2).trans ?_
      exact add_le_add (le_abs_self _) le_rfl
  have h2 := mul_le_mul_of_nonneg_left h1 (by positivity : (0 : ℝ) ≤ (1 / (N : ℝ)) ^ 2)
  linarith

theorem Ubar0_nonneg {N : ℕ} {l : ℝ} (η : Fin N → ℝ) {Λ : ℝ} (hΛ0 : 0 ≤ Λ) : 0 ≤ Ubar0 η Λ l := by
  unfold Ubar0
  refine add_nonneg (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ =>
    add_nonneg (abs_nonneg _) (by have := Fint_nonneg 1 l (η i); linarith)))
    (mul_nonneg (by positivity) (Finset.sum_nonneg fun i _ => Fint_nonneg 1 l (η i)))

theorem Ebar0_nonneg {N : ℕ} (hN : N ≠ 0) {l : ℝ} (hl : 0 < l) {X : Config 1 N}
    {η : Fin N → ℝ} (hη : ∀ i, 0 < η i ∧ η i ≤ 1 / 8)
    (hdisj : ∀ i j, i ≠ j → η i + η j < KernelGrad.tdist (X i) (X j))
    {μ : Measure (Torus 1)} [IsFiniteMeasure μ] {Λ : ℝ}
    (hμ : μ ≤ ENNReal.ofReal Λ • (volume : Measure (Torus 1))) (hμ1 : μ Set.univ = 1) (hΛ0 : 0 ≤ Λ) :
    0 ≤ Ebar0 X η μ Λ l := by
  have hη2 : ∀ i, 0 < η i ∧ η i < 1 / 2 := fun i => ⟨(hη i).1, by linarith [(hη i).2]⟩
  exact (energy_nonneg le_rfl hN hl (sliceCharges_stj le_rfl hl hη2 hdisj) ENNReal.ofReal_ne_top hμ hμ1).trans
    (energy_le_Ebar0 hN hl hη hdisj hΛ0 hμ hμ1)

theorem mk_e1_ne_zero {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) : Torus.mk (e1 η) ≠ (0 : Torus 1) ∧
    KernelGrad.tdist (Torus.mk (e1 η)) 0 = η := by
  have h1 := KernelGrad.tdist_mk (d := 1) (y := e1 η) (fun i => by
    simp [e1, abs_of_pos hη]; linarith)
  have hne : ‖e1 η‖ = η := by
    simp [e1, EuclideanSpace.norm_eq, Fin.sum_univ_one, Real.sqrt_sq_eq_abs, abs_of_pos hη]
  rw [hne] at h1
  refine ⟨fun h => ?_, h1⟩
  rw [h, CoercAux.tdist_self] at h1
  linarith

theorem Ubar0_integral {c : ℝ} (hc : 0 < c)
    (hker : ∀ x : Torus 1, x ≠ 0 →
      periodicRiesz 1 0 x = c * ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * sliceG 1 l x) :
    ∃ KU : ℝ, 0 ≤ KU ∧ ∀ {N : ℕ}, N ≠ 0 → ∀ (η : Fin N → ℝ), (∀ i, 0 < η i ∧ η i ≤ 1 / 8) →
      ∀ {Λ : ℝ}, 0 ≤ Λ →
      IntegrableOn (fun l : ℝ => l ^ (-bexp 1 0) * Ubar0 η Λ l) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * Ubar0 η Λ l ≤
        c⁻¹ * Sig0 η + KU * ((1 / (N : ℝ)) + (1 + Λ) * (1 / (N : ℝ)) * ∑ i, η i) := by
  obtain ⟨CT, hCT0, hCT⟩ := Theta_bound (d := 1) le_rfl (s := 0) le_rfl (by norm_num) (by norm_num) hc hker
  obtain ⟨CF, hCF0, hCF⟩ := Fint_stieltjes (d := 1) le_rfl (s := 0) le_rfl (by norm_num) (by norm_num)
  refine ⟨CT + 2 * CF, by positivity, fun {N} hN η hη {Λ} hΛ => ?_⟩
  have hη2 : ∀ i, 0 < η i ∧ η i < 1 / 2 := fun i => ⟨(hη i).1, by linarith [(hη i).2]⟩
  have hNpos : (0 : ℝ) < N := by exact_mod_cast Nat.pos_of_ne_zero hN
  have hsc : ∀ r : ℝ, selfScale 1 0 r = -Real.log r := fun r => by unfold selfScale; simp
  have T1 : ∀ i, IntegrableOn (fun l : ℝ => l ^ (-bexp 1 0) * |sliceG 1 l (Torus.mk (e1 (η i)))|) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * |sliceG 1 l (Torus.mk (e1 (η i)))| ≤
        c⁻¹ * (-Real.log (η i)) + CT := by
    intro i
    obtain ⟨hne, htd⟩ := mk_e1_ne_zero (hη2 i).1 (hη2 i).2
    obtain ⟨h1, h2⟩ := hCT _ hne
    rw [htd, hsc] at h2
    exact ⟨h1, h2⟩
  have T2 : ∀ i, IntegrableOn (fun l : ℝ => l ^ (-bexp 1 0) * Fint 1 l (η i)) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * Fint 1 l (η i) ≤ CF * η i ^ (((1 : ℕ) : ℝ) - 0) :=
    fun i => hCF (η i) (hη2 i).1 (hη2 i).2
  have hrw : ∀ l : ℝ, l ^ (-bexp 1 0) * Ubar0 η Λ l =
      (1 / (N : ℝ)) ^ 2 * ∑ i, (l ^ (-bexp 1 0) * |sliceG 1 l (Torus.mk (e1 (η i)))|) +
      (2 * (1 / (N : ℝ)) ^ 2 + 2 * Λ / N) * ∑ i, (l ^ (-bexp 1 0) * Fint 1 l (η i)) := by
    intro l
    unfold Ubar0
    simp only [Finset.mul_sum, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    ring
  simp_rw [hrw]
  have hI1 : IntegrableOn (fun l : ℝ => ∑ i, (l ^ (-bexp 1 0) * |sliceG 1 l (Torus.mk (e1 (η i)))|)) (Ioi 0) :=
    integrable_finset_sum _ fun i _ => (T1 i).1
  have hI2 : IntegrableOn (fun l : ℝ => ∑ i, (l ^ (-bexp 1 0) * Fint 1 l (η i))) (Ioi 0) :=
    integrable_finset_sum _ fun i _ => (T2 i).1
  refine ⟨(hI1.const_mul _).add (hI2.const_mul _), ?_⟩
  rw [integral_add (hI1.const_mul _) (hI2.const_mul _), integral_const_mul, integral_const_mul,
    integral_finset_sum _ fun i _ => (T1 i).1, integral_finset_sum _ fun i _ => (T2 i).1]
  have hs1 : ∑ i, ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * |sliceG 1 l (Torus.mk (e1 (η i)))| ≤
      ∑ i, (c⁻¹ * (-Real.log (η i)) + CT) := Finset.sum_le_sum fun i _ => (T1 i).2
  have hs2 : ∑ i, ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * Fint 1 l (η i) ≤ ∑ i, CF * η i := by
    refine (Finset.sum_le_sum fun i _ => (T2 i).2).trans (le_of_eq ?_)
    refine Finset.sum_congr rfl fun i _ => ?_
    norm_num
  have hu0 : 0 ≤ 1 / (N : ℝ) := by positivity
  have hu : 1 / (N : ℝ) ≤ 1 := by
    rw [div_le_one hNpos]; exact_mod_cast Nat.one_le_iff_ne_zero.mpr hN
  have hq0 : 0 ≤ (2 * (1 / (N : ℝ)) ^ 2 + 2 * Λ / N) := by positivity
  have hq : (2 * (1 / (N : ℝ)) ^ 2 + 2 * Λ / N) ≤ 2 * ((1 + Λ) * (1 / (N : ℝ))) := by
    have : (1 / (N : ℝ)) ^ 2 ≤ 1 / (N : ℝ) := by nlinarith
    have h2 : 2 * Λ / (N : ℝ) = 2 * Λ * (1 / (N : ℝ)) := by ring
    rw [h2]; nlinarith
  have hA0 : 0 ≤ ∑ i, CF * η i := Finset.sum_nonneg fun i _ => mul_nonneg hCF0 (hη i).1.le
  have h5 := mul_le_mul_of_nonneg_left hs1 (by positivity : (0 : ℝ) ≤ (1 / (N : ℝ)) ^ 2)
  have h6 := mul_le_mul_of_nonneg_left hs2 hq0
  have h7 : (2 * (1 / (N : ℝ)) ^ 2 + 2 * Λ / N) * ∑ i, CF * η i ≤
      2 * ((1 + Λ) * (1 / (N : ℝ))) * ∑ i, CF * η i := mul_le_mul_of_nonneg_right hq hA0
  have e1' : (1 / (N : ℝ)) ^ 2 * ∑ i, (c⁻¹ * (-Real.log (η i)) + CT) =
      c⁻¹ * Sig0 η + CT * (1 / (N : ℝ)) := by
    unfold Sig0
    rw [Finset.sum_add_distrib, ← Finset.mul_sum]
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    field_simp
  have e2 : ∑ i, CF * η i = CF * ∑ i, η i := (Finset.mul_sum _ _ _).symm
  rw [e2] at h7 h6
  have hB0 : 0 ≤ ∑ i, η i := Finset.sum_nonneg fun i _ => (hη i).1.le
  have hrhs : (CT + 2 * CF) * (1 / (N : ℝ) + (1 + Λ) * (1 / (N : ℝ)) * ∑ i, η i) =
      CT * (1 / (N : ℝ)) + CT * ((1 + Λ) * (1 / (N : ℝ)) * ∑ i, η i) +
        2 * CF * (1 / (N : ℝ)) + 2 * ((1 + Λ) * (1 / (N : ℝ))) * (CF * ∑ i, η i) := by ring
  have hx1 : 0 ≤ CT * ((1 + Λ) * (1 / (N : ℝ)) * ∑ i, η i) :=
    mul_nonneg hCT0 (mul_nonneg (mul_nonneg (by positivity) hu0) hB0)
  have hx2 : 0 ≤ 2 * CF * (1 / (N : ℝ)) := by positivity
  nlinarith [h5, h6, h7, e1', hrhs, hx1, hx2]

theorem neg_log_le_rpow {t : ℝ} (ht : 0 < t) : -Real.log t ≤ 2 * t ^ (-(1 / 2 : ℝ)) := by
  have h := Real.log_le_rpow_div (inv_nonneg.mpr ht.le) (one_half_pos : (0 : ℝ) < 1 / 2)
  rw [Real.log_inv, Real.inv_rpow ht.le] at h
  rw [Real.rpow_neg ht.le]
  have : ((t ^ (1 / 2 : ℝ))⁻¹) / (1 / 2) = 2 * (t ^ (1 / 2 : ℝ))⁻¹ := by ring
  rw [this] at h
  exact h

theorem Ebar0_integral {c : ℝ} (hc : 0 < c)
    (hker : ∀ x : Torus 1, x ≠ 0 →
      periodicRiesz 1 0 x = c * ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * sliceG 1 l x) :
    ∃ KE : ℝ, 0 ≤ KE ∧ ∀ {N : ℕ}, N ≠ 0 → ∀ (X : Config 1 N), (∀ i j, i ≠ j → X i ≠ X j) →
      ∀ (η : Fin N → ℝ), (∀ i, 0 < η i ∧ η i ≤ 1 / 8) → ∀ {Λ : ℝ}, 0 ≤ Λ → ∀ {ρ : Torus 1 → ℝ},
      (∀ x, ρ x ≤ Λ) →
      IntegrableOn (fun l : ℝ => l ^ (-bexp 1 0) * Ebar0 X η (withDensityReal ρ) Λ l) (Ioi 0) ∧
      ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * Ebar0 X η (withDensityReal ρ) Λ l ≤
        (2 / c) * rieszEnergy 1 0 X (withDensityReal ρ) + c⁻¹ * Sig0 η +
        KE * ((1 / (N : ℝ)) + (1 + Λ) * (1 / (N : ℝ)) * ∑ i, η i) := by
  obtain ⟨CT, hCT0, hCT⟩ := Theta_bound (d := 1) le_rfl (s := 0) le_rfl (by norm_num) (by norm_num) hc hker
  obtain ⟨KU, hKU0, hKU⟩ := Ubar0_integral hc hker
  have hsc : ∀ r : ℝ, selfScale 1 0 r = -Real.log r := fun r => by unfold selfScale; simp
  set Θ : Torus 1 → ℝ := fun z => c⁻¹ * (2 * KernelGrad.tdist z 0 ^ (-(1 / 2 : ℝ))) + CT with hΘ
  have hΘm : Measurable Θ :=
    (measurable_const.mul (measurable_const.mul (EnergyAux.measurable_tdist_zero.pow_const _))).add measurable_const
  have hΘi : Integrable Θ := by
    have h1 := SliceAux.integrable_tdist_rpow (d := 1) (α := 1 / 2) (by omega) (by norm_num) (by norm_num)
    exact ((h1.const_mul 2).const_mul c⁻¹).add (integrable_const CT)
  have hΘ0 : ∀ z, 0 ≤ Θ z := fun z => by
    simp only [hΘ]; have := Real.rpow_nonneg (KernelGrad.tdist_nonneg z 0) (-(1 / 2 : ℝ)); positivity
  have hΘb : ∀ z : Torus 1, z ≠ 0 → ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * |sliceG 1 l z| ≤ Θ z := by
    intro z hz
    have h := (hCT z hz).2
    rw [hsc] at h
    have ht : 0 < KernelGrad.tdist z 0 := KernelGrad.tdist_pos hz
    have := neg_log_le_rpow ht
    simp only [hΘ]
    have hc' : 0 ≤ c⁻¹ := inv_nonneg.mpr hc.le
    nlinarith [mul_le_mul_of_nonneg_left this hc']
  refine ⟨KU, hKU0, fun {N} hN X hX η hη {Λ} hΛ {ρ} hρΛ => ?_⟩
  obtain ⟨hEq, hInt⟩ := riesz_energy_fubini (d := 1) le_rfl (s := 0) le_rfl (by norm_num) (by norm_num) hker hΘm hΘi hΘ0 hΘb X hX hρΛ hΛ
  obtain ⟨hUi, hUb⟩ := hKU hN η hη hΛ
  have hrw : ∀ l : ℝ, l ^ (-bexp 1 0) * Ebar0 X η (withDensityReal ρ) Λ l =
      2 * (l ^ (-bexp 1 0) * modulatedEnergyKernel (sliceG 1 l) X (withDensityReal ρ)) +
        l ^ (-bexp 1 0) * Ubar0 η Λ l := fun l => by unfold Ebar0; ring
  simp_rw [hrw]
  refine ⟨(hInt.const_mul 2).add hUi, ?_⟩
  rw [integral_add (hInt.const_mul 2) hUi, integral_const_mul]
  have h1 : ∫ l in Ioi (0 : ℝ), l ^ (-bexp 1 0) * modulatedEnergyKernel (sliceG 1 l) X (withDensityReal ρ) =
      rieszEnergy 1 0 X (withDensityReal ρ) / c := by
    rw [hEq]; field_simp
  rw [h1]
  have : 2 * (rieszEnergy 1 0 X (withDensityReal ρ) / c) = (2 / c) * rieszEnergy 1 0 X (withDensityReal ρ) := by ring
  linarith

end HRS.Commutator.Stj
