import HRS.MH.CommSuperDefs
import HRS.MH.CommSuperCS1
import HRS.MH.CommSuperCS2
import HRS.MH.CommSuperCS3
import HRS.MH.CommSuperCS8

/-!
# CS4: torus energy of the concentrated data (packet `energy_conc`, `CommSuperSpec.lean`)

Route (`HRS/MH/CommSuperPlan.md`, CS4): the torus energy of the concentrated data is the Euclidean
modulated energy with the pulled-back kernel `H u = periodicRiesz (mk (t u))` (push-forward,
`conc_measure_proof`); `H = t^{-s} rieszKernel + κ_t + r(0) + E` with `|E u| ≤ M t ‖u‖`
(`kernel_local_proof`); the constant part contributes `-κ/(2N)` (deleted diagonal, `∫ρ = 1`);
the remainder is bounded by `4 M t R0`.  Bochner bookkeeping: `integral_prod`, `integral_map`.
Helper names carry the prefix `cs4_`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MH.CommSuper

variable {d N : ℕ} {s : ℝ}

/-- The additive constant `κ_t` of the logarithmic dilation: `-log t` for `s = 0`, `0` otherwise. -/
def cs4_kap (t s : ℝ) : ℝ := if s = 0 then -Real.log t else 0

/-! ### Elementary facts on the torus and on the Euclidean kernel -/

theorem cs4_concMap_sub (t : ℝ) (x y : Euc d) :
    concMap t x - concMap t y = concMap t (x - y) := by
  unfold concMap
  rw [← cs2_mk_sub, smul_sub]

theorem cs4_concMap_measurable (t : ℝ) : Measurable (concMap (d := d) t) :=
  (Torus.continuous_mk.comp (continuous_const_smul t)).measurable

theorem cs4_rk_meas : Measurable (Whole.rieszKernel d s) := by
  unfold Whole.rieszKernel
  split_ifs
  · exact (Real.measurable_log.comp measurable_norm).neg
  · exact measurable_norm.pow_const (-s)

theorem cs4_rk_eq_kern (u : Euc d) :
    Whole.rieszKernel d s u = (if s = 0 then 1 else s) * HRS.Commutator.Whole.kern s u := by
  unfold Whole.rieszKernel HRS.Commutator.Whole.kern
  by_cases hs : s = 0
  · simp [hs]
  · simp only [hs, if_false]
    rw [← mul_assoc, mul_inv_cancel₀ hs, one_mul]

theorem cs4_rk_scale {t : ℝ} (ht : 0 < t) {u : Euc d} (hu : u ≠ 0) :
    Whole.rieszKernel d s (t • u) = (t ^ s)⁻¹ * Whole.rieszKernel d s u + cs4_kap t s := by
  have hn : ‖u‖ ≠ 0 := norm_ne_zero_iff.2 hu
  have hnt : ‖t • u‖ = t * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
  unfold Whole.rieszKernel cs4_kap
  by_cases hs : s = 0
  · subst hs
    simp only [if_true, Real.rpow_zero, inv_one, one_mul]
    rw [hnt, Real.log_mul ht.ne' hn]
    ring
  · simp only [if_neg hs, add_zero]
    rw [hnt, Real.mul_rpow ht.le (norm_nonneg u), Real.rpow_neg ht.le s]

/-- Local form of the torus kernel at a point `t u` with `‖t u‖ < δ` (`kernel_local`). -/
theorem cs4_decomp {δ M t : ℝ} {r : Euc d → ℝ}
    (hr : ∀ x : Euc d, ‖x‖ < δ → |r x - r 0| ≤ M * ‖x‖)
    (hpt : ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
      periodicRiesz d s (Torus.mk x) = Whole.rieszKernel d s x + r x)
    (ht : 0 < t) {u : Euc d} (hu : u ≠ 0) (hδu : t * ‖u‖ < δ) :
    |periodicRiesz d s (concMap t u) - ((t ^ s)⁻¹ * Whole.rieszKernel d s u + cs4_kap t s + r 0)| ≤
      M * (t * ‖u‖) := by
  have hnorm : ‖t • u‖ = t * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
  have htu : t • u ≠ 0 := smul_ne_zero ht.ne' hu
  have hlt : ‖t • u‖ < δ := by rw [hnorm]; exact hδu
  have h1 := hpt (t • u) hlt htu
  have h2 := hr (t • u) hlt
  have e : periodicRiesz d s (concMap t u) = periodicRiesz d s (Torus.mk (t • u)) := rfl
  have key : Whole.rieszKernel d s (t • u) + r (t • u) -
      ((t ^ s)⁻¹ * Whole.rieszKernel d s u + cs4_kap t s + r 0) = r (t • u) - r 0 := by
    rw [cs4_rk_scale ht hu]
    ring
  rw [e, h1, key]
  rw [hnorm] at h2
  exact h2

/-! ### The Euclidean measure `ρ dx` -/

theorem cs4_int_withDensity {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) (f : Euc d → ℝ) :
    ∫ x, f x ∂(Whole.withDensityReal ρ) = ∫ x, f x * ρ x := by
  have hm : Measurable (fun x => ENNReal.ofReal (ρ x)) :=
    ENNReal.measurable_ofReal.comp hρ.measurable
  unfold Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul hm (ae_of_all _ fun x => ENNReal.ofReal_lt_top) f]
  congr 1
  ext x
  rw [ENNReal.toReal_ofReal (hρ.nonneg x), smul_eq_mul, mul_comm]

/-- The Euclidean modulated energy in the Lebesgue form `pairGen`. -/
theorem cs4_modEnergy_eq {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {N : ℕ}
    (X : Whole.EucConfig d N) (g : Euc d → ℝ) :
    Whole.modulatedEnergy g X (Whole.withDensityReal ρ) =
      (1 / 2) * HRS.Commutator.Whole.pairGen (fun x y => g (x - y)) X ρ := by
  have h3 : ∫ x, (∫ y, g (x - y) * ρ y) * ρ x = ∫ x, ∫ y, g (x - y) * ρ x * ρ y := by
    congr 1
    ext x
    rw [← integral_mul_const]
    congr 1
    ext y
    ring
  unfold Whole.modulatedEnergy
  simp only [Whole.convMeasure, Whole.energyPairing, cs4_int_withDensity hρ,
    HRS.Commutator.Whole.pairGen]
  rw [h3]
  ring

/-- Push-forward of the torus energy of the concentrated data to the Euclidean energy of `H`. -/
theorem cs4_int_map_sub {ν : Measure (Euc d)} (t : ℝ) {G : Torus d → ℝ} (hG : Measurable G)
    (z0 : Torus d) :
    ∫ z, G (z0 - z) ∂(ν.map (concMap t)) = ∫ y, G (z0 - concMap t y) ∂ν := by
  have hm : Measurable (fun z : Torus d => G (z0 - z)) :=
    hG.comp (continuous_const.sub continuous_id).measurable
  rw [integral_map (cs4_concMap_measurable t).aemeasurable hm.aestronglyMeasurable]

theorem cs4_iter_map {ν : Measure (Euc d)} [SFinite ν] (t : ℝ) {G : Torus d → ℝ}
    (hG : Measurable G) :
    ∫ z, (∫ w, G (z - w) ∂(ν.map (concMap t))) ∂(ν.map (concMap t)) =
      ∫ x, ∫ y, G (concMap t x - concMap t y) ∂ν ∂ν := by
  have hf : Measurable (fun p : Torus d × Torus d => G (p.1 - p.2)) :=
    hG.comp (continuous_fst.sub continuous_snd).measurable
  have hSM : StronglyMeasurable (fun z : Torus d => ∫ w, G (z - w) ∂(ν.map (concMap t))) :=
    hf.stronglyMeasurable.integral_prod_right'
  rw [integral_map (cs4_concMap_measurable t).aemeasurable hSM.aestronglyMeasurable]
  congr 1
  ext x
  exact cs4_int_map_sub t hG (concMap t x)

theorem cs4_energy_transfer (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {t R0 : ℝ} (ht : 0 < t)
    (hR : t * R0 ≤ 1 / 16) {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ)
    (hsupp : ∀ x, R0 < ‖x‖ → ρ x = 0) {N : ℕ} (X : Whole.EucConfig d N) :
    HRS.rieszEnergy d s (fun i => concMap t (X i)) (HRS.withDensityReal (concDens t ρ)) =
      Whole.modulatedEnergy (fun u => periodicRiesz d s (concMap t u)) X
        (Whole.withDensityReal ρ) := by
  haveI : SFinite (Whole.withDensityReal ρ) := by
    unfold Whole.withDensityReal
    infer_instance
  have hmeas : HRS.withDensityReal (concDens t ρ) = (Whole.withDensityReal ρ).map (concMap t) :=
    (conc_measure_proof (N := N) ht hR hρ hsupp).1
  have hGm : Measurable (periodicRiesz d s) := HRS.CoercAux.measurable_periodicRiesz_one hd hs0 hsd
  have hA : ∀ i j : Fin N, periodicRiesz d s (concMap t (X i) - concMap t (X j)) =
      periodicRiesz d s (concMap t (X i - X j)) := fun i j => by rw [cs4_concMap_sub]
  have hB : ∀ i : Fin N, ∫ y, periodicRiesz d s (concMap t (X i) - y)
      ∂(HRS.withDensityReal (concDens t ρ)) =
      ∫ y, periodicRiesz d s (concMap t (X i - y)) ∂(Whole.withDensityReal ρ) := by
    intro i
    rw [hmeas, cs4_int_map_sub t hGm]
    congr 1
    ext y
    rw [cs4_concMap_sub]
  have hC : ∫ x, ∫ y, periodicRiesz d s (x - y) ∂(HRS.withDensityReal (concDens t ρ))
      ∂(HRS.withDensityReal (concDens t ρ)) =
      ∫ x, ∫ y, periodicRiesz d s (concMap t (x - y)) ∂(Whole.withDensityReal ρ)
        ∂(Whole.withDensityReal ρ) := by
    rw [hmeas, cs4_iter_map t hGm]
    congr 1
    ext x
    congr 1
    ext y
    rw [cs4_concMap_sub]
  simp only [HRS.rieszEnergy, HRS.modulatedEnergyKernel, HRS.modulatedEnergy,
    Whole.modulatedEnergy, Whole.convMeasure, Whole.energyPairing]
  simp only [hA, hB, hC]

/-! ### Integrability and bounds for the pieces -/

/-- A.e. `y ≠ a` (the diagonal of one particle is Lebesgue-null). -/
theorem cs4_ae_ne (hd : 1 ≤ d) (a : Euc d) :
    ∀ᵐ y ∂(volume : Measure (Euc d)), y ≠ a := by
  haveI : NeZero d := ⟨by omega⟩
  rw [ae_iff]
  simpa [Set.setOf_eq_eq_singleton] using measure_singleton a

/-- A.e. `p.1 ≠ p.2` on the product (the diagonal is product-null). -/
theorem cs4_ae_offdiag (hd : 1 ≤ d) :
    ∀ᵐ p ∂(volume : Measure (Euc d × Euc d)), p.1 ≠ p.2 := by
  haveI : NeZero d := ⟨by omega⟩
  have hs : {p : Euc d × Euc d | ¬ p.1 ≠ p.2} = Set.diagonal (Euc d) := by
    ext p
    simp [Set.diagonal]
  rw [ae_iff, hs, Measure.volume_eq_prod (Euc d) (Euc d),
    Measure.measure_prod_null measurableSet_diagonal]
  refine Filter.Eventually.of_forall fun x => ?_
  have hx : Prod.mk x ⁻¹' Set.diagonal (Euc d) = {x} := by
    ext y
    simp [Set.diagonal, eq_comm]
  simp only [hx, Pi.zero_apply]
  exact measure_singleton x

theorem cs4_ae_sec {ρ : Euc d → ℝ} (hd : 1 ≤ d) (hρ : Whole.IsProbDensity ρ) {R0 : ℝ}
    (hsupp : ∀ x, R0 < ‖x‖ → ρ x = 0) {E : Euc d → ℝ} {B : ℝ}
    (hB : ∀ x y : Euc d, x ≠ y → ‖x‖ ≤ R0 → ‖y‖ ≤ R0 → |E (x - y)| ≤ B) {a : Euc d}
    (ha : ‖a‖ ≤ R0) :
    ∀ᵐ y ∂(volume : Measure (Euc d)), ‖E (a - y) * ρ y‖ ≤ B * ρ y := by
  filter_upwards [cs4_ae_ne hd a] with y hy
  by_cases hρy : ρ y = 0
  · simp [hρy]
  have hy' : ‖y‖ ≤ R0 := by
    by_contra h
    exact hρy (hsupp y (not_le.1 h))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg y)]
  exact mul_le_mul_of_nonneg_right (hB a y (Ne.symm hy) ha hy') (hρ.nonneg y)

theorem cs4_ae_prod {ρ : Euc d → ℝ} (hd : 1 ≤ d) (hρ : Whole.IsProbDensity ρ) {R0 : ℝ}
    (hsupp : ∀ x, R0 < ‖x‖ → ρ x = 0) {E : Euc d → ℝ} {B : ℝ}
    (hB : ∀ x y : Euc d, x ≠ y → ‖x‖ ≤ R0 → ‖y‖ ≤ R0 → |E (x - y)| ≤ B) :
    ∀ᵐ p ∂(volume : Measure (Euc d × Euc d)),
      ‖E (p.1 - p.2) * ρ p.1 * ρ p.2‖ ≤ B * (ρ p.1 * ρ p.2) := by
  filter_upwards [cs4_ae_offdiag hd] with p hp
  by_cases h1 : ρ p.1 = 0
  · simp [h1]
  by_cases h2 : ρ p.2 = 0
  · simp [h2]
  have hx : ‖p.1‖ ≤ R0 := by
    by_contra h
    exact h1 (hsupp p.1 (not_le.1 h))
  have hy : ‖p.2‖ ≤ R0 := by
    by_contra h
    exact h2 (hsupp p.2 (not_le.1 h))
  have hb := hB p.1 p.2 hp hx hy
  have hn1 := hρ.nonneg p.1
  have hn2 := hρ.nonneg p.2
  calc ‖E (p.1 - p.2) * ρ p.1 * ρ p.2‖ = |E (p.1 - p.2)| * (ρ p.1 * ρ p.2) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hn1, abs_of_nonneg hn2]
        ring
    _ ≤ B * (ρ p.1 * ρ p.2) := mul_le_mul_of_nonneg_right hb (mul_nonneg hn1 hn2)

theorem cs4_PI_of_bound {ρ : Euc d → ℝ} (hd : 1 ≤ d) (hρ : Whole.IsProbDensity ρ) {R0 : ℝ}
    (hsupp : ∀ x, R0 < ‖x‖ → ρ x = 0) {N : ℕ} {X : Fin N → Euc d} (hX : ∀ i, ‖X i‖ ≤ R0)
    {E : Euc d → ℝ} (hE : Measurable E) {B : ℝ}
    (hB : ∀ x y : Euc d, x ≠ y → ‖x‖ ≤ R0 → ‖y‖ ≤ R0 → |E (x - y)| ≤ B) :
    HRS.Commutator.Whole.PairIntegrable (fun x y => E (x - y)) X ρ := by
  have hρint := cs8_integrable hρ
  refine ⟨fun i => ?_, ?_⟩
  · have hm : Measurable (fun y : Euc d => X i - y) := (continuous_const.sub continuous_id).measurable
    refine Integrable.mono' (hρint.const_mul B) ?_ (cs4_ae_sec hd hρ hsupp hB (hX i))
    exact ((hE.comp hm).mul hρ.measurable).aestronglyMeasurable
  · refine Integrable.mono' ((hρint.mul_prod hρint).const_mul B) ?_ (cs4_ae_prod hd hρ hsupp hB)
    exact (((hE.comp (measurable_fst.sub measurable_snd)).mul
      (hρ.measurable.comp measurable_fst)).mul (hρ.measurable.comp measurable_snd)).aestronglyMeasurable

theorem cs4_PI_const {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {N : ℕ} (X : Fin N → Euc d)
    (c : ℝ) : HRS.Commutator.Whole.PairIntegrable (fun _ _ => c) X ρ := by
  have hρint := cs8_integrable hρ
  refine ⟨fun i => ?_, ?_⟩
  · exact hρint.const_mul c
  · exact ((hρint.mul_prod hρint).const_mul c).congr (ae_of_all _ fun p => by simp only [mul_assoc])

theorem cs4_PI_add {ρ : Euc d → ℝ} {N : ℕ} {X : Fin N → Euc d} {f g : Euc d → Euc d → ℝ}
    (hf : HRS.Commutator.Whole.PairIntegrable f X ρ)
    (hg : HRS.Commutator.Whole.PairIntegrable g X ρ) :
    HRS.Commutator.Whole.PairIntegrable (fun x y => f x y + g x y) X ρ := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  refine ⟨fun i => ?_, ?_⟩
  · exact ((hf1 i).add (hg1 i)).congr (ae_of_all _ fun y => by simp only [add_mul, Pi.add_apply])
  · exact (hf2.add hg2).congr (ae_of_all _ fun p => by simp only [add_mul, Pi.add_apply])

theorem cs4_PI_mul_kern {ρ : Euc d → ℝ} {N : ℕ} {X : Fin N → Euc d} (c : ℝ)
    (hk : HRS.Commutator.Whole.PairIntegrable (fun x y => HRS.Commutator.Whole.kern s (x - y)) X ρ) :
    HRS.Commutator.Whole.PairIntegrable (fun x y => c * HRS.Commutator.Whole.kern s (x - y)) X ρ := by
  obtain ⟨h1, h2⟩ := hk
  refine ⟨fun i => ?_, ?_⟩
  · exact ((h1 i).const_mul c).congr (ae_of_all _ fun y => by simp only [mul_assoc])
  · exact (h2.const_mul c).congr (ae_of_all _ fun p => by simp only [mul_assoc])

theorem cs4_logMoment {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {R0 : ℝ}
    (hsupp : ∀ x, R0 < ‖x‖ → ρ x = 0) :
    Whole.HasLogMoment (Whole.withDensityReal ρ) (Real.log (2 + |R0|)) := by
  have hρint := cs8_integrable hρ
  have hpt : ∀ x : Euc d, Real.log (2 + ‖x‖) * ρ x ≤ Real.log (2 + |R0|) * ρ x := by
    intro x
    by_cases hx : ρ x = 0
    · simp [hx]
    have hxR : ‖x‖ ≤ R0 := by
      by_contra h
      exact hx (hsupp x (not_le.1 h))
    have hlog : Real.log (2 + ‖x‖) ≤ Real.log (2 + |R0|) :=
      Real.log_le_log (by positivity) (by linarith [le_abs_self R0])
    exact mul_le_mul_of_nonneg_right hlog (hρ.nonneg x)
  have hnn : ∀ x : Euc d, 0 ≤ Real.log (2 + ‖x‖) := fun x =>
    Real.log_nonneg (by linarith [norm_nonneg x])
  have hint : Integrable (fun x => Real.log (2 + ‖x‖) * ρ x) := by
    refine Integrable.mono' (hρint.const_mul (Real.log (2 + |R0|))) ?_ (ae_of_all _ fun x => ?_)
    · exact ((Real.measurable_log.comp (measurable_const.add measurable_norm)).mul
        hρ.measurable).aestronglyMeasurable
    · rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (hnn x) (hρ.nonneg x))]
      exact hpt x
  unfold Whole.HasLogMoment
  refine ⟨?_, ?_⟩
  · have hm : Measurable (fun x => ENNReal.ofReal (ρ x)) :=
      ENNReal.measurable_ofReal.comp hρ.measurable
    unfold Whole.withDensityReal
    rw [integrable_withDensity_iff_integrable_smul' hm
      (ae_of_all _ fun x => ENNReal.ofReal_lt_top)]
    refine hint.congr (ae_of_all _ fun x => ?_)
    simp [ENNReal.toReal_ofReal (hρ.nonneg x), smul_eq_mul, mul_comm]
  · rw [cs4_int_withDensity hρ]
    calc ∫ x, Real.log (2 + ‖x‖) * ρ x ≤ ∫ x, Real.log (2 + |R0|) * ρ x :=
          integral_mono hint (hρint.const_mul _) hpt
      _ = Real.log (2 + |R0|) := by
          rw [integral_const_mul, hρ.integral_one, mul_one]

/-! ### Algebra of the Lebesgue-form pair functional -/

theorem cs4_pairGen_add {ρ : Euc d → ℝ} {N : ℕ} {X : Fin N → Euc d} {f g : Euc d → Euc d → ℝ}
    (hf : HRS.Commutator.Whole.PairIntegrable f X ρ)
    (hg : HRS.Commutator.Whole.PairIntegrable g X ρ) :
    HRS.Commutator.Whole.pairGen (fun x y => f x y + g x y) X ρ =
      HRS.Commutator.Whole.pairGen f X ρ + HRS.Commutator.Whole.pairGen g X ρ := by
  obtain ⟨hf1, hf2⟩ := hf
  obtain ⟨hg1, hg2⟩ := hg
  have hint : Integrable (fun p : Euc d × Euc d => (f p.1 p.2 + g p.1 p.2) * ρ p.1 * ρ p.2)
      (volume.prod volume) :=
    (hf2.add hg2).congr (ae_of_all _ fun p => by simp only [add_mul, Pi.add_apply])
  have hT1 : ∫ x, ∫ y, (f x y + g x y) * ρ x * ρ y =
      ∫ p : Euc d × Euc d, (f p.1 p.2 + g p.1 p.2) * ρ p.1 * ρ p.2 :=
    (integral_prod _ hint).symm
  have hT2 : ∫ x, ∫ y, f x y * ρ x * ρ y = ∫ p : Euc d × Euc d, f p.1 p.2 * ρ p.1 * ρ p.2 :=
    (integral_prod _ hf2).symm
  have hT3 : ∫ x, ∫ y, g x y * ρ x * ρ y = ∫ p : Euc d × Euc d, g p.1 p.2 * ρ p.1 * ρ p.2 :=
    (integral_prod _ hg2).symm
  have hT : ∫ x, ∫ y, (f x y + g x y) * ρ x * ρ y =
      (∫ x, ∫ y, f x y * ρ x * ρ y) + (∫ x, ∫ y, g x y * ρ x * ρ y) := by
    rw [hT1, hT2, hT3, ← integral_add hf2 hg2]
    congr 1
    ext p
    simp only [add_mul]
  have hS1 : (∑ i, ∑ j ∈ Finset.univ.erase i, (f (X i) (X j) + g (X i) (X j))) =
      (∑ i, ∑ j ∈ Finset.univ.erase i, f (X i) (X j)) +
        (∑ i, ∑ j ∈ Finset.univ.erase i, g (X i) (X j)) := by
    simp only [Finset.sum_add_distrib]
  have hS2 : (∑ i, ∫ y, (f (X i) y + g (X i) y) * ρ y) =
      (∑ i, ∫ y, f (X i) y * ρ y) + (∑ i, ∫ y, g (X i) y * ρ y) := by
    rw [← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [← integral_add (hf1 i) (hg1 i)]
    congr 1
    ext y
    simp only [add_mul]
  simp only [HRS.Commutator.Whole.pairGen]
  rw [hS1, hS2, hT]
  ring

theorem cs4_pairGen_const_mul_sub (c : ℝ) (k : Euc d → ℝ) {ρ : Euc d → ℝ} {N : ℕ}
    {X : Fin N → Euc d} :
    HRS.Commutator.Whole.pairGen (fun x y => c * k (x - y)) X ρ =
      c * HRS.Commutator.Whole.pairGen (fun x y => k (x - y)) X ρ := by
  have e1 : ∀ i : Fin N, ∫ y, c * k (X i - y) * ρ y = c * ∫ y, k (X i - y) * ρ y := fun i => by
    rw [← integral_const_mul]
    congr 1
    ext y
    ring
  have e2 : ∫ x, ∫ y, c * k (x - y) * ρ x * ρ y = c * ∫ x, ∫ y, k (x - y) * ρ x * ρ y := by
    rw [← integral_const_mul]
    congr 1
    ext x
    rw [← integral_const_mul]
    congr 1
    ext y
    ring
  simp only [HRS.Commutator.Whole.pairGen, e1, e2, ← Finset.mul_sum]
  ring

theorem cs4_pairGen_const (κ : ℝ) {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {N : ℕ}
    (hN : 1 ≤ N) (X : Fin N → Euc d) :
    HRS.Commutator.Whole.pairGen (fun _ _ => κ) X ρ = -κ / (N : ℝ) := by
  have hI : ∀ c : ℝ, ∫ y, c * ρ y = c := fun c => by
    rw [integral_const_mul, hρ.integral_one, mul_one]
  have hJ : ∀ x : Euc d, ∫ y, κ * ρ x * ρ y = κ * ρ x := fun x => by
    rw [integral_const_mul, hρ.integral_one, mul_one]
  have hK : ∫ x, ∫ y, κ * ρ x * ρ y = κ := by
    simp only [hJ]
    exact hI κ
  have hsum1 : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, κ = ((N : ℝ) - 1) * κ := by
    intro i
    rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
      Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub hN, Nat.cast_one]
  have hN0 : (N : ℝ) ≠ 0 := Nat.cast_ne_zero.2 (by omega)
  simp only [HRS.Commutator.Whole.pairGen, hsum1, hI, hK]
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  field_simp
  ring

/-- The bound `|pairGen E| ≤ 4 B` for a kernel bounded by `B` off the diagonal (`|E u| ≤ B`). -/
theorem cs4_pairGen_bound {ρ : Euc d → ℝ} (hd : 1 ≤ d) (hρ : Whole.IsProbDensity ρ) {R0 : ℝ}
    (hsupp : ∀ x, R0 < ‖x‖ → ρ x = 0) {N : ℕ} (hN : 2 ≤ N) {X : Fin N → Euc d}
    (hinj : Function.Injective X) (hX : ∀ i, ‖X i‖ ≤ R0)
    {E : Euc d → ℝ} (hE : Measurable E) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x y : Euc d, x ≠ y → ‖x‖ ≤ R0 → ‖y‖ ≤ R0 → |E (x - y)| ≤ B) :
    |HRS.Commutator.Whole.pairGen (fun x y => E (x - y)) X ρ| ≤ 4 * B := by
  have hρint := cs8_integrable hρ
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hS2i : ∀ i : Fin N, |∫ y, E (X i - y) * ρ y| ≤ B := by
    intro i
    have h := norm_integral_le_of_norm_le (hρint.const_mul B)
      (cs4_ae_sec hd hρ hsupp hB (hX i))
    rw [integral_const_mul, hρ.integral_one, mul_one, Real.norm_eq_abs] at h
    exact h
  have hS2 : |∑ i, ∫ y, E (X i - y) * ρ y| ≤ N * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∫ y, E (X i - y) * ρ y| ≤ ∑ _i : Fin N, B :=
          Finset.sum_le_sum fun i _ => hS2i i
      _ = N * B := by simp
  have hpair : ∀ i j : Fin N, j ∈ Finset.univ.erase i → |E (X i - X j)| ≤ B := by
    intro i j hj
    have hne : X i ≠ X j := fun h => (Finset.mem_erase.1 hj).1 (hinj h).symm
    exact hB _ _ hne (hX i) (hX j)
  have hS1i : ∀ i : Fin N, |∑ j ∈ Finset.univ.erase i, E (X i - X j)| ≤ ((N : ℝ) - 1) * B := by
    intro i
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.univ.erase i, |E (X i - X j)| ≤ ∑ _j ∈ Finset.univ.erase i, B :=
          Finset.sum_le_sum fun j hj => hpair i j hj
      _ = ((N : ℝ) - 1) * B := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_one]
  have hS1 : |∑ i, ∑ j ∈ Finset.univ.erase i, E (X i - X j)| ≤ N * (((N : ℝ) - 1) * B) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j ∈ Finset.univ.erase i, E (X i - X j)| ≤ ∑ _i : Fin N, ((N : ℝ) - 1) * B :=
          Finset.sum_le_sum fun i _ => hS1i i
      _ = N * (((N : ℝ) - 1) * B) := by simp
  have hPI := cs4_PI_of_bound hd hρ hsupp hX hE hB
  have hprod := hPI.2
  have hS3 : |∫ x, ∫ y, E (x - y) * ρ x * ρ y| ≤ B := by
    have e : ∫ x, ∫ y, E (x - y) * ρ x * ρ y =
        ∫ p : Euc d × Euc d, E (p.1 - p.2) * ρ p.1 * ρ p.2 :=
      (integral_prod _ hprod).symm
    rw [e]
    have h := norm_integral_le_of_norm_le ((hρint.mul_prod hρint).const_mul B)
      (cs4_ae_prod hd hρ hsupp hB)
    simp only [integral_const_mul, integral_prod_mul, hρ.integral_one, mul_one] at h
    rw [Real.norm_eq_abs] at h
    exact h
  have hfrac : ((N : ℝ) - 1) / N ≤ 1 := by
    rw [div_le_one hNpos]
    linarith
  have hh1 : |(1 / (N : ℝ) ^ 2) * (∑ i, ∑ j ∈ Finset.univ.erase i, E (X i - X j))| ≤ B := by
    rw [abs_mul, abs_of_pos (div_pos one_pos (pow_pos hNpos 2))]
    calc (1 / (N : ℝ) ^ 2) * |∑ i, ∑ j ∈ Finset.univ.erase i, E (X i - X j)|
        ≤ (1 / (N : ℝ) ^ 2) * (N * (((N : ℝ) - 1) * B)) :=
          mul_le_mul_of_nonneg_left hS1 (div_pos one_pos (pow_pos hNpos 2)).le
      _ = (((N : ℝ) - 1) / N) * B := by
          field_simp
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right hfrac hB0
      _ = B := one_mul B
  have hh2 : |(2 / (N : ℝ)) * (∑ i, ∫ y, E (X i - y) * ρ y)| ≤ 2 * B := by
    rw [abs_mul, abs_of_pos (div_pos two_pos hNpos)]
    calc (2 / (N : ℝ)) * |∑ i, ∫ y, E (X i - y) * ρ y|
        ≤ (2 / (N : ℝ)) * (N * B) :=
          mul_le_mul_of_nonneg_left hS2 (div_pos two_pos hNpos).le
      _ = 2 * B := by
          field_simp
  have e2 : HRS.Commutator.Whole.pairGen (fun x y => E (x - y)) X ρ =
      (1 / (N : ℝ) ^ 2) * (∑ i, ∑ j ∈ Finset.univ.erase i, E (X i - X j))
        - (2 / (N : ℝ)) * (∑ i, ∫ y, E (X i - y) * ρ y)
        + ∫ x, ∫ y, E (x - y) * ρ x * ρ y := rfl
  rw [e2]
  have hA := abs_le.1 hh1
  have hB' := abs_le.1 hh2
  have hC := abs_le.1 hS3
  rw [abs_le]
  constructor <;> linarith [hA.1, hA.2, hB'.1, hB'.2, hC.1, hC.2]

/-! ### The main estimate -/

/-- **CS4** (size L).  For `2 t R0 < δ`, the torus energy of the concentrated bounded compactly
supported data equals the dilated Euclidean energy plus the kernel constant `-r(0)/(2N)` up to
`4 M t R0`. -/
theorem energy_conc_proof (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (δ M c0 : ℝ), 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 ≤ M ∧
      ∀ (N : ℕ), 2 ≤ N → ∀ (t R0 Λ : ℝ), 0 < t → 2 * t * R0 < δ →
        ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → (∀ x, R0 < ‖x‖ → ρ x = 0) →
        ∀ X : Whole.EucConfig d N, Function.Injective X → (∀ i, ‖X i‖ ≤ R0) →
          |rieszEnergy d s (fun i => concMap t (X i)) (withDensityReal (concDens t ρ)) -
              ((t ^ s)⁻¹ * Whole.rieszModulatedEnergy d s X (Whole.withDensityReal ρ) +
                (if s = 0 then Real.log t / (2 * N) else 0) - c0 / (2 * N))| ≤
            4 * M * (t * R0) := by
  obtain ⟨δ, M, r, R, hδ0, hδ1, hM0, hr, -, hpt⟩ := kernel_local_proof hd hs0 hsd
  refine ⟨δ, M, r 0, hδ0, hδ1, hM0, ?_⟩
  intro N hN t R0 Λ ht hδt ρ hρ hρΛ hsupp X hinj hXR
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hR0 : 0 ≤ R0 := le_trans (norm_nonneg _) (hXR ⟨0, by omega⟩)
  have htR : t * R0 ≤ 1 / 16 := by linarith
  have hBnn : 0 ≤ M * (t * (2 * R0)) := mul_nonneg hM0 (mul_nonneg ht.le (by linarith))
  have hGm : Measurable (periodicRiesz d s) := HRS.CoercAux.measurable_periodicRiesz_one hd hs0 hsd
  obtain ⟨Ediff, hEd⟩ : ∃ E : Euc d → ℝ, ∀ u, E u = periodicRiesz d s (concMap t u) -
      ((t ^ s)⁻¹ * Whole.rieszKernel d s u + cs4_kap t s + r 0) :=
    ⟨_, fun u => rfl⟩
  have hEmeas : Measurable Ediff := by
    have e : Ediff = fun u => periodicRiesz d s (concMap t u) -
        ((t ^ s)⁻¹ * Whole.rieszKernel d s u + cs4_kap t s + r 0) := funext hEd
    rw [e]
    exact (hGm.comp (cs4_concMap_measurable t)).sub
      (((measurable_const.mul cs4_rk_meas).add measurable_const).add measurable_const)
  have hBound : ∀ x y : Euc d, x ≠ y → ‖x‖ ≤ R0 → ‖y‖ ≤ R0 →
      |Ediff (x - y)| ≤ M * (t * (2 * R0)) := by
    intro x y hxy hx hy
    have hu : x - y ≠ 0 := sub_ne_zero.2 hxy
    have hnorm : ‖x - y‖ ≤ 2 * R0 := by linarith [norm_sub_le x y]
    have hδu : t * ‖x - y‖ < δ := by
      have h1 : t * ‖x - y‖ ≤ t * (2 * R0) := mul_le_mul_of_nonneg_left hnorm ht.le
      have h2 : t * (2 * R0) < δ := by linarith
      linarith
    rw [hEd]
    exact (cs4_decomp (s := s) hr (fun x h1 h2 => (hpt x h1 h2).1) ht hu hδu).trans
      (mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hnorm ht.le) hM0)
  have hlog : s = 0 → Whole.HasLogMoment (Whole.withDensityReal ρ) (Real.log (2 + |R0|)) :=
    fun _ => cs4_logMoment hρ hsupp
  have hv0 : Whole.HasLipBoundW (0 : Euc d → Euc d) 0 := ⟨0, LipschitzWith.const 0, by simp⟩
  obtain ⟨hEI, -, -⟩ := bdd_integrable_proof hd hs0 hsd hρ hρΛ hlog X hinj 0 0 hv0
  have hPIA : HRS.Commutator.Whole.PairIntegrable
      (fun x y => (t ^ s)⁻¹ * Whole.rieszKernel d s (x - y)) X ρ := by
    have e : (fun x y => (t ^ s)⁻¹ * Whole.rieszKernel d s (x - y)) =
        (fun x y => ((t ^ s)⁻¹ * (if s = 0 then 1 else s)) *
          HRS.Commutator.Whole.kern s (x - y)) := by
      funext x y
      rw [cs4_rk_eq_kern]
      ring
    rw [e]
    exact cs4_PI_mul_kern _ hEI
  have hPIC : HRS.Commutator.Whole.PairIntegrable (fun _ _ => cs4_kap t s + r 0) X ρ :=
    cs4_PI_const hρ X _
  have hPIE : HRS.Commutator.Whole.PairIntegrable (fun x y => Ediff (x - y)) X ρ :=
    cs4_PI_of_bound hd hρ hsupp hXR hEmeas hBound
  have hsplit : (fun x y => periodicRiesz d s (concMap t (x - y))) =
      (fun x y => (t ^ s)⁻¹ * Whole.rieszKernel d s (x - y) +
        ((cs4_kap t s + r 0) + Ediff (x - y))) := by
    funext x y
    rw [hEd (x - y)]
    ring
  have hpg : HRS.Commutator.Whole.pairGen (fun x y => periodicRiesz d s (concMap t (x - y))) X ρ =
      (t ^ s)⁻¹ * HRS.Commutator.Whole.pairGen (fun x y => Whole.rieszKernel d s (x - y)) X ρ +
        (-(cs4_kap t s + r 0) / (N : ℝ) + HRS.Commutator.Whole.pairGen (fun x y => Ediff (x - y)) X ρ) := by
    rw [hsplit]
    have h1 := cs4_pairGen_add (f := fun x y => (t ^ s)⁻¹ * Whole.rieszKernel d s (x - y))
      (g := fun x y => (cs4_kap t s + r 0) + Ediff (x - y)) hPIA (cs4_PI_add hPIC hPIE)
    beta_reduce at h1
    rw [h1]
    have h2 := cs4_pairGen_add (f := fun _ _ => cs4_kap t s + r 0)
      (g := fun x y => Ediff (x - y)) hPIC hPIE
    beta_reduce at h2
    rw [h2, cs4_pairGen_const _ hρ (by omega) X, cs4_pairGen_const_mul_sub (t ^ s)⁻¹
      (Whole.rieszKernel d s)]
  have hT := cs4_energy_transfer hd hs0 hsd ht htR hρ hsupp X
  have hRM : Whole.rieszModulatedEnergy d s X (Whole.withDensityReal ρ) =
      (1 / 2) * HRS.Commutator.Whole.pairGen (fun x y => Whole.rieszKernel d s (x - y)) X ρ :=
    cs4_modEnergy_eq hρ X (Whole.rieszKernel d s)
  have hT2 : Whole.modulatedEnergy (fun u => periodicRiesz d s (concMap t u)) X
      (Whole.withDensityReal ρ) =
      (1 / 2) * HRS.Commutator.Whole.pairGen
        (fun x y => periodicRiesz d s (concMap t (x - y))) X ρ :=
    cs4_modEnergy_eq hρ X (fun u => periodicRiesz d s (concMap t u))
  rw [hT, hT2, hRM, hpg]
  have hdiff : ∀ w Q P : ℝ, (1 / 2) * (w * Q + (-(cs4_kap t s + r 0) / (N : ℝ) + P)) -
      (w * ((1 / 2) * Q) + (if s = 0 then Real.log t / (2 * (N : ℝ)) else 0) - r 0 / (2 * (N : ℝ))) =
      (1 / 2) * P := by
    intro w Q P
    unfold cs4_kap
    split_ifs <;> ring
  rw [hdiff]
  have hP := cs4_pairGen_bound hd hρ hsupp hN hinj hXR hEmeas hBnn hBound
  calc |(1 / 2) * HRS.Commutator.Whole.pairGen (fun x y => Ediff (x - y)) X ρ|
      = (1 / 2) * |HRS.Commutator.Whole.pairGen (fun x y => Ediff (x - y)) X ρ| := by
        rw [abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    _ ≤ (1 / 2) * (4 * (M * (t * (2 * R0)))) := mul_le_mul_of_nonneg_left hP (by norm_num)
    _ = 4 * M * (t * R0) := by ring

end HRS.MH.CommSuper
