import HRS.MH.CommSuperDefs
import HRS.MH.CommSuperCS1
import HRS.MH.CommSuperCS2
import HRS.MH.CommSuperCS3
import HRS.MH.CommSuperCS4
import HRS.MH.CommSuperCS8

/-!
# CS5: torus commutator of the concentrated data (packet `comm_conc`, `CommSuperSpec.lean`)

Route (`HRS/MH/CommSuperPlan.md`, CS5): the torus field `w` is replaced by the measurable field
`W z = t • (v (t⁻¹ • centeredRep z) - v 0)`, which agrees with `w` on the support of the torus density
(a.e.); the torus commutator is pushed forward to `ℝ^d` (`conc_measure_proof`); the pointwise identity
`commKernel (mk t·) = (t^s)⁻¹ · commutatorKernel + t · ⟨v x - v y, R(t(x-y))⟩` (local form of
`periodicRieszGrad`, `kernel_local_proof`) splits the Lebesgue-form pair functional into the Euclidean
commutator and a remainder bounded by `2KMtR0`; the deleted-diagonal bound gives `4 · 2KMtR0`.
Helper names carry the prefix `cs5_`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MH.CommSuper

variable {d N : ℕ} {s : ℝ}

/-! ### Scalar and force-scaling facts -/

theorem cs5_t_mul_pow {t : ℝ} (ht : 0 < t) : t * t ^ (-(s + 1)) = (t ^ s)⁻¹ := by
  have hne : t ≠ 0 := ht.ne'
  rw [show -(s + 1) = -s + -1 by ring, Real.rpow_add ht, Real.rpow_neg ht.le, Real.rpow_neg_one]
  field_simp

theorem cs5_kernGrad_scale {t : ℝ} (ht : 0 < t) {u : Euc d} :
    HRS.Commutator.Whole.kernGrad s (t • u) =
      t ^ (-(s + 1)) • HRS.Commutator.Whole.kernGrad s u := by
  have hn : ‖t • u‖ = t * ‖u‖ := by rw [norm_smul, Real.norm_of_nonneg ht.le]
  have h1 : t ^ (-(s + 1)) = t ^ (-(s + 2)) * t := by
    rw [show -(s + 1) = -(s + 2) + 1 by ring, Real.rpow_add ht, Real.rpow_one]
  unfold HRS.Commutator.Whole.kernGrad
  rw [hn, Real.mul_rpow ht.le (norm_nonneg u), h1]
  module

/-! ### Coordinates and the torus embedding -/

theorem cs5_abs_coord (x : Euc d) (i : Fin d) : |x i| ≤ ‖x‖ := by
  rw [← Real.norm_eq_abs]
  exact PiLp.norm_apply_le x i

theorem cs5_small_norm {t R0 : ℝ} (ht : 0 < t) {x : Euc d} (hx : ‖x‖ ≤ R0) (hR : t * R0 ≤ 1 / 16) :
    ‖t • x‖ ≤ 1 / 16 := by
  rw [norm_smul, Real.norm_of_nonneg ht.le]
  calc t * ‖x‖ ≤ t * R0 := mul_le_mul_of_nonneg_left hx ht.le
    _ ≤ 1 / 16 := hR

theorem cs5_cR_conc {t : ℝ} (ht : 0 < t) {x : Euc d} (hx : ‖t • x‖ ≤ 1 / 16) :
    KernelGrad.centeredRep (concMap t x) = t • x := by
  have hc : ∀ i, |(t • x) i| < 1 / 2 := fun i => by
    have := cs5_abs_coord (t • x) i
    linarith
  exact cs3_cR_of_small (t • x) hc

theorem cs5_mk_inj {t : ℝ} (ht : 0 < t) {x y : Euc d} (hx : ‖t • x‖ ≤ 1 / 16)
    (hy : ‖t • y‖ ≤ 1 / 16) (h : concMap t x = concMap t y) : x = y := by
  have h' : Torus.mk (t • x) = Torus.mk (t • y) := h
  have hxy : ∀ i, t * x i = t * y i := by
    intro i
    obtain ⟨n, hn⟩ := cs3_exists_int_of_mk_eq h' i
    have hxi := abs_le.1 (le_trans (cs5_abs_coord (t • x) i) hx)
    have hyi := abs_le.1 (le_trans (cs5_abs_coord (t • y) i) hy)
    have e : (n : ℝ) = (t • x) i - (t • y) i := by linarith
    have hn' : -1 < (n : ℝ) ∧ (n : ℝ) < 1 := by
      rw [e]
      constructor <;> linarith [hxi.1, hxi.2, hyi.1, hyi.2]
    have hz1 : -1 < n := by exact_mod_cast hn'.1
    have hz2 : n < 1 := by exact_mod_cast hn'.2
    have hn0 : n = 0 := by omega
    rw [hn0] at hn
    simpa using hn
  ext i
  exact mul_left_cancel₀ ht.ne' (hxy i)

/-! ### Measurability -/

theorem cs5_meas_kernGrad : Measurable (HRS.Commutator.Whole.kernGrad (d := d) s) := by
  unfold HRS.Commutator.Whole.kernGrad
  exact ((measurable_norm.pow_const _).neg).smul measurable_id

theorem cs5_meas_commKer {F : Euc d → Euc d} (hF : Measurable F) {v : Euc d → Euc d}
    (hv : Measurable v) :
    Measurable (fun p : Euc d × Euc d => HRS.Commutator.Whole.commKer F v p.1 p.2) := by
  unfold HRS.Commutator.Whole.commKer
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  exact Measurable.inner ((hv.comp measurable_fst).sub (hv.comp measurable_snd))
    (hF.comp (measurable_fst.sub measurable_snd))

theorem cs5_meas_ck (G : Torus d → Euc d) (hG : Measurable G) (W : Torus d → Euc d)
    (hW : Measurable W) :
    Measurable (fun p : Torus d × Torus d => HRS.commKernel G W p.1 p.2) := by
  unfold HRS.commKernel
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  exact Measurable.inner ((hW.comp measurable_fst).sub (hW.comp measurable_snd))
    (hG.comp (continuous_fst.sub continuous_snd).measurable)

/-! ### Almost everywhere support of the torus density -/

theorem cs5_ae_S {t R0 : ℝ} (ht : 0 < t) (hR : t * R0 ≤ 1 / 16) {ρ : Euc d → ℝ}
    (hρ : Whole.IsProbDensity ρ) (hsupp : ∀ x, R0 < ‖x‖ → ρ x = 0) :
    ∀ᵐ z ∂(HRS.withDensityReal (concDens t ρ)), ‖KernelGrad.centeredRep z‖ ≤ 1 / 16 := by
  unfold HRS.withDensityReal
  have hm : Measurable (fun z => ENNReal.ofReal (concDens t ρ z)) :=
    ENNReal.measurable_ofReal.comp (cs3_measurable_concDens hρ.measurable)
  rw [ae_withDensity_iff hm]
  refine ae_of_all _ fun z hz => ?_
  have hz' : concDens t ρ z ≠ 0 := fun h0 => hz (by rw [h0, ENNReal.ofReal_zero])
  have hρ0 : ρ (t⁻¹ • KernelGrad.centeredRep z) ≠ 0 := fun h0 => hz' (by
    unfold concDens
    rw [h0, mul_zero])
  have hn : ‖t⁻¹ • KernelGrad.centeredRep z‖ ≤ R0 := by
    by_contra hc
    exact hρ0 (hsupp _ (not_le.1 hc))
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le)] at hn
  have h2 : ‖KernelGrad.centeredRep z‖ ≤ t * R0 := by
    calc ‖KernelGrad.centeredRep z‖ = t * (t⁻¹ * ‖KernelGrad.centeredRep z‖) := by
          field_simp
      _ ≤ t * R0 := mul_le_mul_of_nonneg_left hn ht.le
  linarith

/-! ### Replacing the torus field on the support -/

theorem cs5_offdiag_replace {w W : Torus d → Euc d} (G : Torus d → Euc d)
    (μ : Measure (Torus d)) {N : ℕ} (X : Config d N)
    (hX : ∀ i, ‖KernelGrad.centeredRep (X i)‖ ≤ 1 / 16)
    (hμ : ∀ᵐ z ∂μ, ‖KernelGrad.centeredRep z‖ ≤ 1 / 16)
    (hw : ∀ z : Torus d, ‖KernelGrad.centeredRep z‖ ≤ 1 / 16 → w z = W z) :
    offDiagPairing (HRS.commKernel G w) X μ = offDiagPairing (HRS.commKernel G W) X μ := by
  have hk : ∀ a b : Torus d, ‖KernelGrad.centeredRep a‖ ≤ 1 / 16 →
      ‖KernelGrad.centeredRep b‖ ≤ 1 / 16 → HRS.commKernel G w a b = HRS.commKernel G W a b := by
    intro a b ha hb
    unfold HRS.commKernel
    rw [hw a ha, hw b hb]
  have h1 : ∑ i, ∑ j ∈ Finset.univ.erase i, HRS.commKernel G w (X i) (X j) =
      ∑ i, ∑ j ∈ Finset.univ.erase i, HRS.commKernel G W (X i) (X j) :=
    Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => hk _ _ (hX i) (hX j)
  have h2 : ∀ i, ∫ y, HRS.commKernel G w (X i) y ∂μ = ∫ y, HRS.commKernel G W (X i) y ∂μ := by
    intro i
    refine integral_congr_ae ?_
    filter_upwards [hμ] with y hy
    exact hk _ _ (hX i) hy
  have h3 : ∫ x, ∫ y, HRS.commKernel G w x y ∂μ ∂μ = ∫ x, ∫ y, HRS.commKernel G W x y ∂μ ∂μ := by
    refine integral_congr_ae ?_
    filter_upwards [hμ] with x hx
    refine integral_congr_ae ?_
    filter_upwards [hμ] with y hy
    exact hk x y hx hy
  unfold offDiagPairing
  rw [h1, h3]
  simp only [h2]

/-! ### Push-forward of the torus pair functional -/

theorem cs5_offdiag_transfer {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {N : ℕ}
    (X : Whole.EucConfig d N) (t : ℝ) {F : Torus d → Torus d → ℝ}
    (hF : Measurable (fun p : Torus d × Torus d => F p.1 p.2)) :
    offDiagPairing F (fun i => concMap t (X i)) ((Whole.withDensityReal ρ).map (concMap t)) =
      HRS.Commutator.Whole.pairGen (fun x y => F (concMap t x) (concMap t y)) X ρ := by
  haveI : SFinite (Whole.withDensityReal ρ) := by
    unfold Whole.withDensityReal
    infer_instance
  have hin : ∀ a : Torus d, ∫ y, F a y ∂((Whole.withDensityReal ρ).map (concMap t)) =
      ∫ y, F a (concMap t y) * ρ y := by
    intro a
    have hm : Measurable (fun z => F a z) := hF.comp (measurable_const.prodMk measurable_id)
    rw [integral_map (cs4_concMap_measurable t).aemeasurable hm.aestronglyMeasurable]
    exact cs4_int_withDensity hρ (fun y => F a (concMap t y))
  have hG : StronglyMeasurable
      (fun z : Torus d => ∫ w, F z w ∂((Whole.withDensityReal ρ).map (concMap t))) :=
    hF.stronglyMeasurable.integral_prod_right'
  have hout : ∫ z, (∫ w, F z w ∂((Whole.withDensityReal ρ).map (concMap t)))
        ∂((Whole.withDensityReal ρ).map (concMap t)) =
      ∫ x, (∫ y, F (concMap t x) (concMap t y) * ρ y) * ρ x := by
    rw [integral_map (cs4_concMap_measurable t).aemeasurable hG.aestronglyMeasurable]
    simp only [hin]
    exact cs4_int_withDensity hρ (fun x => ∫ y, F (concMap t x) (concMap t y) * ρ y)
  have hlast : ∫ x, (∫ y, F (concMap t x) (concMap t y) * ρ y) * ρ x =
      ∫ x, ∫ y, F (concMap t x) (concMap t y) * ρ x * ρ y := by
    congr 1
    ext x
    rw [← integral_mul_const]
    congr 1
    ext y
    ring
  unfold offDiagPairing HRS.Commutator.Whole.pairGen
  rw [hout, hlast]
  simp only [hin]

/-! ### Algebra of the centred pair functional and of the commutator kernel -/

theorem cs5_centered_eq {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {N : ℕ}
    (X : Fin N → Euc d) (h : Euc d → Euc d → ℝ) :
    Whole.centeredPairFunctional h X (Whole.withDensityReal ρ) =
      HRS.Commutator.Whole.pairGen h X ρ := by
  have e1 : ∀ i, ∫ y, h (X i) y ∂(Whole.withDensityReal ρ) = ∫ y, h (X i) y * ρ y := fun i =>
    cs4_int_withDensity hρ (fun y => h (X i) y)
  have e2a : ∀ x, ∫ y, h x y ∂(Whole.withDensityReal ρ) = ∫ y, h x y * ρ y := fun x =>
    cs4_int_withDensity hρ (fun y => h x y)
  have e2 : ∫ x, ∫ y, h x y ∂(Whole.withDensityReal ρ) ∂(Whole.withDensityReal ρ) =
      ∫ x, ∫ y, h x y * ρ x * ρ y := by
    simp only [e2a]
    rw [cs4_int_withDensity hρ]
    congr 1
    ext x
    rw [← integral_mul_const]
    congr 1
    ext y
    ring
  unfold Whole.centeredPairFunctional HRS.Commutator.Whole.pairGen
  simp only [e1, e2]
  ring

theorem cs5_commN {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {N : ℕ} (X : Fin N → Euc d)
    (v : Euc d → Euc d) :
    Whole.commN d s v X (Whole.withDensityReal ρ) =
      HRS.Commutator.Whole.pairGen (Whole.commutatorKernel d s v) X ρ := by
  unfold Whole.commN
  exact cs5_centered_eq hρ X _

theorem cs5_cK_eq (v : Euc d → Euc d) (x y : Euc d) :
    Whole.commutatorKernel d s v x y =
      (if s = 0 then 1 else s) * HRS.Commutator.Whole.commKer (HRS.Commutator.Whole.kernGrad s) v x y := by
  by_cases hxy : x = y
  · subst hxy
    simp [Whole.commutatorKernel, HRS.Commutator.Whole.commKer]
  · unfold Whole.commutatorKernel HRS.Commutator.Whole.commKer
    rw [if_neg hxy, HRS.Commutator.Whole.cmxFB_rk_grad (x - y) (sub_ne_zero.2 hxy), real_inner_smul_right]

/-! ### General pair functionals (kernel bounded on the ball, no difference form) -/

theorem cs5_pt_bound {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {R0 : ℝ}
    (hsupp : ∀ x, R0 < ‖x‖ → ρ x = 0) {k : Euc d → Euc d → ℝ} {B : ℝ}
    (hB : ∀ x y : Euc d, ‖x‖ ≤ R0 → ‖y‖ ≤ R0 → |k x y| ≤ B) {a : Euc d} (ha : ‖a‖ ≤ R0)
    (y : Euc d) : ‖k a y * ρ y‖ ≤ B * ρ y := by
  by_cases h : ρ y = 0
  · simp [h]
  have hy : ‖y‖ ≤ R0 := by
    by_contra hc
    exact h (hsupp y (not_le.1 hc))
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ.nonneg y)]
  exact mul_le_mul_of_nonneg_right (hB a y ha hy) (hρ.nonneg y)

theorem cs5_prod_bound {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {R0 : ℝ}
    (hsupp : ∀ x, R0 < ‖x‖ → ρ x = 0) {k : Euc d → Euc d → ℝ} {B : ℝ}
    (hB : ∀ x y : Euc d, ‖x‖ ≤ R0 → ‖y‖ ≤ R0 → |k x y| ≤ B) (p : Euc d × Euc d) :
    ‖k p.1 p.2 * ρ p.1 * ρ p.2‖ ≤ B * (ρ p.1 * ρ p.2) := by
  by_cases h1 : ρ p.1 = 0
  · simp [h1]
  by_cases h2 : ρ p.2 = 0
  · simp [h2]
  have hx : ‖p.1‖ ≤ R0 := by
    by_contra hc
    exact h1 (hsupp p.1 (not_le.1 hc))
  have hy : ‖p.2‖ ≤ R0 := by
    by_contra hc
    exact h2 (hsupp p.2 (not_le.1 hc))
  have hn1 := hρ.nonneg p.1
  have hn2 := hρ.nonneg p.2
  calc ‖k p.1 p.2 * ρ p.1 * ρ p.2‖ = |k p.1 p.2| * (ρ p.1 * ρ p.2) := by
        rw [Real.norm_eq_abs, abs_mul, abs_mul, abs_of_nonneg hn1, abs_of_nonneg hn2]
        ring
    _ ≤ B * (ρ p.1 * ρ p.2) := mul_le_mul_of_nonneg_right (hB p.1 p.2 hx hy) (mul_nonneg hn1 hn2)

theorem cs5_PI_bd {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {R0 : ℝ}
    (hsupp : ∀ x, R0 < ‖x‖ → ρ x = 0) {N : ℕ} {X : Fin N → Euc d} (hX : ∀ i, ‖X i‖ ≤ R0)
    {k : Euc d → Euc d → ℝ} (hk : Measurable (fun p : Euc d × Euc d => k p.1 p.2)) {B : ℝ}
    (hB : ∀ x y : Euc d, ‖x‖ ≤ R0 → ‖y‖ ≤ R0 → |k x y| ≤ B) :
    HRS.Commutator.Whole.PairIntegrable k X ρ := by
  have hρint := cs8_integrable hρ
  refine ⟨fun i => ?_, ?_⟩
  · refine Integrable.mono' (hρint.const_mul B) ?_
      (ae_of_all _ fun y => cs5_pt_bound hρ hsupp hB (hX i) y)
    exact ((hk.comp (measurable_const.prodMk measurable_id)).mul hρ.measurable).aestronglyMeasurable
  · refine Integrable.mono' ((hρint.mul_prod hρint).const_mul B) ?_
      (ae_of_all _ fun p => cs5_prod_bound hρ hsupp hB p)
    exact ((hk.mul (hρ.measurable.comp measurable_fst)).mul
      (hρ.measurable.comp measurable_snd)).aestronglyMeasurable

theorem cs5_PI_mul {ρ : Euc d → ℝ} {N : ℕ} {X : Fin N → Euc d} (c : ℝ)
    {k : Euc d → Euc d → ℝ} (hk : HRS.Commutator.Whole.PairIntegrable k X ρ) :
    HRS.Commutator.Whole.PairIntegrable (fun x y => c * k x y) X ρ := by
  obtain ⟨h1, h2⟩ := hk
  refine ⟨fun i => ?_, ?_⟩
  · exact ((h1 i).const_mul c).congr (ae_of_all _ fun y => by simp only [mul_assoc])
  · exact (h2.const_mul c).congr (ae_of_all _ fun p => by simp only [mul_assoc])

theorem cs5_pairGen_mul (c : ℝ) (k : Euc d → Euc d → ℝ) {ρ : Euc d → ℝ} {N : ℕ}
    {X : Fin N → Euc d} :
    HRS.Commutator.Whole.pairGen (fun x y => c * k x y) X ρ =
      c * HRS.Commutator.Whole.pairGen k X ρ := by
  have e1 : ∀ i : Fin N, ∫ y, c * k (X i) y * ρ y = c * ∫ y, k (X i) y * ρ y := fun i => by
    rw [← integral_const_mul]
    congr 1
    ext y
    ring
  have e2 : ∫ x, ∫ y, c * k x y * ρ x * ρ y = c * ∫ x, ∫ y, k x y * ρ x * ρ y := by
    rw [← integral_const_mul]
    congr 1
    ext x
    rw [← integral_const_mul]
    congr 1
    ext y
    ring
  simp only [HRS.Commutator.Whole.pairGen, e1, e2, ← Finset.mul_sum]
  ring

/-- The bound `|pairGen k| ≤ 4 B` for a kernel bounded by `B` on the ball of radius `R0`. -/
theorem cs5_pairGen_bd {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) {R0 : ℝ}
    (hsupp : ∀ x, R0 < ‖x‖ → ρ x = 0) {N : ℕ} (hN : 2 ≤ N) {X : Fin N → Euc d}
    (hX : ∀ i, ‖X i‖ ≤ R0) {k : Euc d → Euc d → ℝ}
    (hk : Measurable (fun p : Euc d × Euc d => k p.1 p.2)) {B : ℝ} (hB0 : 0 ≤ B)
    (hB : ∀ x y : Euc d, ‖x‖ ≤ R0 → ‖y‖ ≤ R0 → |k x y| ≤ B) :
    |HRS.Commutator.Whole.pairGen k X ρ| ≤ 4 * B := by
  have hρint := cs8_integrable hρ
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  have hS2i : ∀ i : Fin N, |∫ y, k (X i) y * ρ y| ≤ B := by
    intro i
    have h := norm_integral_le_of_norm_le (hρint.const_mul B)
      (ae_of_all _ fun y => cs5_pt_bound hρ hsupp hB (hX i) y)
    rw [integral_const_mul, hρ.integral_one, mul_one, Real.norm_eq_abs] at h
    exact h
  have hS2 : |∑ i, ∫ y, k (X i) y * ρ y| ≤ N * B := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∫ y, k (X i) y * ρ y| ≤ ∑ _i : Fin N, B :=
          Finset.sum_le_sum fun i _ => hS2i i
      _ = N * B := by simp
  have hS1i : ∀ i : Fin N, |∑ j ∈ Finset.univ.erase i, k (X i) (X j)| ≤ ((N : ℝ) - 1) * B := by
    intro i
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ j ∈ Finset.univ.erase i, |k (X i) (X j)| ≤ ∑ _j ∈ Finset.univ.erase i, B :=
          Finset.sum_le_sum fun j _ => hB _ _ (hX i) (hX j)
      _ = ((N : ℝ) - 1) * B := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i), Finset.card_univ,
            Fintype.card_fin, nsmul_eq_mul, Nat.cast_sub (by omega), Nat.cast_one]
  have hS1 : |∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)| ≤ N * (((N : ℝ) - 1) * B) := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    calc ∑ i, |∑ j ∈ Finset.univ.erase i, k (X i) (X j)| ≤ ∑ _i : Fin N, ((N : ℝ) - 1) * B :=
          Finset.sum_le_sum fun i _ => hS1i i
      _ = N * (((N : ℝ) - 1) * B) := by simp
  have hPI := cs5_PI_bd hρ hsupp hX hk hB
  have hprod := hPI.2
  have hS3 : |∫ x, ∫ y, k x y * ρ x * ρ y| ≤ B := by
    have e : ∫ x, ∫ y, k x y * ρ x * ρ y = ∫ p : Euc d × Euc d, k p.1 p.2 * ρ p.1 * ρ p.2 :=
      (integral_prod _ hprod).symm
    rw [e]
    have h := norm_integral_le_of_norm_le ((hρint.mul_prod hρint).const_mul B)
      (ae_of_all _ fun p => cs5_prod_bound hρ hsupp hB p)
    simp only [integral_const_mul, integral_prod_mul, hρ.integral_one, mul_one] at h
    rw [Real.norm_eq_abs] at h
    exact h
  have hfrac : ((N : ℝ) - 1) / N ≤ 1 := by
    rw [div_le_one hNpos]
    linarith
  have hh1 : |(1 / (N : ℝ) ^ 2) * (∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j))| ≤ B := by
    rw [abs_mul, abs_of_pos (div_pos one_pos (pow_pos hNpos 2))]
    calc (1 / (N : ℝ) ^ 2) * |∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j)|
        ≤ (1 / (N : ℝ) ^ 2) * (N * (((N : ℝ) - 1) * B)) :=
          mul_le_mul_of_nonneg_left hS1 (div_pos one_pos (pow_pos hNpos 2)).le
      _ = (((N : ℝ) - 1) / N) * B := by
          field_simp
      _ ≤ 1 * B := mul_le_mul_of_nonneg_right hfrac hB0
      _ = B := one_mul B
  have hh2 : |(2 / (N : ℝ)) * (∑ i, ∫ y, k (X i) y * ρ y)| ≤ 2 * B := by
    rw [abs_mul, abs_of_pos (div_pos two_pos hNpos)]
    calc (2 / (N : ℝ)) * |∑ i, ∫ y, k (X i) y * ρ y|
        ≤ (2 / (N : ℝ)) * (N * B) :=
          mul_le_mul_of_nonneg_left hS2 (div_pos two_pos hNpos).le
      _ = 2 * B := by
          field_simp
  have e2 : HRS.Commutator.Whole.pairGen k X ρ =
      (1 / (N : ℝ) ^ 2) * (∑ i, ∑ j ∈ Finset.univ.erase i, k (X i) (X j))
        - (2 / (N : ℝ)) * (∑ i, ∫ y, k (X i) y * ρ y)
        + ∫ x, ∫ y, k x y * ρ x * ρ y := rfl
  rw [e2]
  have hA := abs_le.1 hh1
  have hB' := abs_le.1 hh2
  have hC := abs_le.1 hS3
  rw [abs_le]
  constructor <;> linarith [hA.1, hA.2, hB'.1, hB'.2, hC.1, hC.2]

/-! ### Local form of the torus commutator kernel -/

/-- The pointwise identity: for `‖x‖, ‖y‖ ≤ R0` the torus commutator kernel at `(t x, t y)` is the
Euclidean commutator kernel scaled by `(t^s)⁻¹` plus `t ⟨v x - v y, R(t(x-y))⟩`. -/
theorem cs5_pt {δ M R0 t : ℝ} {R : Euc d → Euc d} (hR : ∀ x : Euc d, ‖x‖ < δ → ‖R x‖ ≤ M)
    (hpt : ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 →
      periodicRieszGrad d s (Torus.mk x) = Whole.rieszKernelGrad d s x + R x)
    (ht : 0 < t) (hδ : 2 * t * R0 < δ) (hR0 : t * R0 ≤ 1 / 16) {v : Euc d → Euc d}
    {W : Torus d → Euc d}
    (hW : ∀ x : Euc d, ‖t • x‖ ≤ 1 / 16 → W (concMap t x) = t • (v x - v 0))
    {x y : Euc d} (hx : ‖x‖ ≤ R0) (hy : ‖y‖ ≤ R0) :
    HRS.commKernel (periodicRieszGrad d s) W (concMap t x) (concMap t y) =
      ((t ^ s)⁻¹ * (if s = 0 then 1 else s)) *
          HRS.Commutator.Whole.commKer (HRS.Commutator.Whole.kernGrad s) v x y +
        t * inner ℝ (v x - v y) (R (t • (x - y))) := by
  by_cases hxy : x = y
  · subst hxy
    simp [HRS.commKernel, HRS.Commutator.Whole.commKer]
  · have hd2 : ‖x - y‖ ≤ 2 * R0 := by linarith [norm_sub_le x y]
    have hu : t • (x - y) ≠ 0 := smul_ne_zero ht.ne' (sub_ne_zero.2 hxy)
    have hlt : ‖t • (x - y)‖ < δ := by
      rw [norm_smul, Real.norm_of_nonneg ht.le]
      have h1 : t * ‖x - y‖ ≤ t * (2 * R0) := mul_le_mul_of_nonneg_left hd2 ht.le
      have h2 : t * (2 * R0) = 2 * t * R0 := by ring
      linarith
    have hxs : ‖t • x‖ ≤ 1 / 16 := cs5_small_norm ht hx hR0
    have hys : ‖t • y‖ ≤ 1 / 16 := cs5_small_norm ht hy hR0
    have hne : concMap t x ≠ concMap t y := fun h => hxy (cs5_mk_inj ht hxs hys h)
    have hsub : concMap t x - concMap t y = Torus.mk (t • (x - y)) := by
      rw [cs4_concMap_sub]
      rfl
    have ea : t • (v x - v 0) - t • (v y - v 0) = t • (v x - v y) := by
      rw [← smul_sub]
      congr 1
      abel
    unfold HRS.commKernel HRS.Commutator.Whole.commKer
    rw [if_neg hne, if_neg hxy, hW x hxs, hW y hys, hsub, hpt (t • (x - y)) hlt hu,
      HRS.Commutator.Whole.cmxFB_rk_grad (t • (x - y)) hu, cs5_kernGrad_scale ht, ea]
    simp only [inner_add_right, real_inner_smul_left, real_inner_smul_right]
    rw [← cs5_t_mul_pow ht]
    ring

/-! ### The main estimate -/

/-- **CS5** (size M).  For `2 t R0 < δ`, the torus commutator of the concentrated data equals
`(t^s)⁻¹` times the Euclidean commutator up to `8 K M t R0`. -/
theorem comm_conc_proof (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ (δ M : ℝ), 0 < δ ∧ δ ≤ 1 / 8 ∧ 0 ≤ M ∧
      ∀ (N : ℕ), 2 ≤ N → ∀ (t R0 Λ : ℝ), 0 < t → 2 * t * R0 < δ →
        ∀ ρ : Euc d → ℝ, Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) → (∀ x, R0 < ‖x‖ → ρ x = 0) →
        ∀ X : Whole.EucConfig d N, Function.Injective X → (∀ i, ‖X i‖ ≤ R0) →
        ∀ (v : Euc d → Euc d) (K : ℝ≥0), LipschitzWith K v →
        ∀ w : Torus d → Euc d, (∀ x : Euc d, ‖x‖ ≤ 1 / 16 → w (Torus.mk x) = t • (v (t⁻¹ • x) - v 0)) →
          |commQuantity d s w (fun i => concMap t (X i)) (withDensityReal (concDens t ρ)) -
              (t ^ s)⁻¹ * Whole.commN d s v X (Whole.withDensityReal ρ)| ≤ 8 * K * M * (t * R0) := by
  obtain ⟨δ, M, r, R, hδ0, hδ1, hM0, -, hR, hpt⟩ := kernel_local_proof hd hs0 hsd
  refine ⟨δ, M, hδ0, hδ1, hM0, ?_⟩
  intro N hN t R0 Λ ht hδt ρ hρ hρΛ hsupp X hinj hXR v K hv w hw
  have hN' : (2 : ℝ) ≤ N := by exact_mod_cast hN
  have hR0 : 0 ≤ R0 := le_trans (norm_nonneg _) (hXR ⟨0, by omega⟩)
  have htR : t * R0 ≤ 1 / 16 := by
    have h2 : 2 * t * R0 = 2 * (t * R0) := by ring
    linarith
  have hKnn : (0 : ℝ) ≤ (K : ℝ) := K.2
  have hvm : Measurable v := hv.continuous.measurable
  have hvl : Whole.HasLipBoundW v (K : ℝ) := ⟨K, hv, le_rfl⟩
  -- the measurable replacement of the torus field
  obtain ⟨W, hWdef⟩ : ∃ W : Torus d → Euc d,
      ∀ z, W z = t • (v (t⁻¹ • KernelGrad.centeredRep z) - v 0) := ⟨_, fun _ => rfl⟩
  have hWm : Measurable W := by
    have e : W = fun z => t • (v (t⁻¹ • KernelGrad.centeredRep z) - v 0) := funext hWdef
    rw [e]
    have h1 : Measurable (fun z => v (t⁻¹ • KernelGrad.centeredRep z)) :=
      hvm.comp (cs3_measurable_cR.const_smul t⁻¹)
    exact (h1.sub measurable_const).const_smul t
  have hWc : ∀ x : Euc d, ‖t • x‖ ≤ 1 / 16 → W (concMap t x) = t • (v x - v 0) := by
    intro x hx
    rw [hWdef, cs5_cR_conc ht hx, inv_smul_smul₀ ht.ne']
  have hwW : ∀ z : Torus d, ‖KernelGrad.centeredRep z‖ ≤ 1 / 16 → w z = W z := by
    intro z hz
    have h1 := hw (KernelGrad.centeredRep z) hz
    rw [KernelGrad.mk_centeredRep] at h1
    rw [hWdef]
    exact h1
  have hμS := cs5_ae_S ht htR hρ hsupp
  have hXS : ∀ i, ‖KernelGrad.centeredRep (concMap t (X i))‖ ≤ 1 / 16 := fun i => by
    rw [cs5_cR_conc ht (cs5_small_norm ht (hXR i) htR)]
    exact cs5_small_norm ht (hXR i) htR
  have hrep := cs5_offdiag_replace (w := w) (W := W) (periodicRieszGrad d s)
    (HRS.withDensityReal (concDens t ρ)) (fun i => concMap t (X i)) hXS hμS hwW
  have hmeas := (conc_measure_proof (N := N) ht htR hρ hsupp).1
  have hFm : Measurable (fun p : Torus d × Torus d =>
      HRS.commKernel (periodicRieszGrad d s) W p.1 p.2) :=
    cs5_meas_ck _ (HRS.KernelGrad.measurable_periodicRieszGrad hsd) W hWm
  have htr := cs5_offdiag_transfer hρ X t hFm
  have hQ : commQuantity d s w (fun i => concMap t (X i)) (withDensityReal (concDens t ρ)) =
      HRS.Commutator.Whole.pairGen
        (fun x y => HRS.commKernel (periodicRieszGrad d s) W (concMap t x) (concMap t y)) X ρ := by
    unfold commQuantity commQuantityWith
    rw [hrep, hmeas, htr]
  have hcomm : Whole.commN d s v X (Whole.withDensityReal ρ) =
      HRS.Commutator.Whole.pairGen (Whole.commutatorKernel d s v) X ρ := cs5_commN hρ X v
  -- the Euclidean pieces
  obtain ⟨A, hA⟩ : ∃ A : Euc d → Euc d → ℝ,
      ∀ x y, A x y = (t ^ s)⁻¹ * Whole.commutatorKernel d s v x y := ⟨_, fun _ _ => rfl⟩
  have hAeq : A = fun x y => ((t ^ s)⁻¹ * (if s = 0 then 1 else s)) *
      HRS.Commutator.Whole.commKer (HRS.Commutator.Whole.kernGrad s) v x y := by
    funext x y
    rw [hA, cs5_cK_eq]
    ring
  have hlog : s = 0 → Whole.HasLogMoment (Whole.withDensityReal ρ) (Real.log (2 + |R0|)) :=
    fun _ => cs4_logMoment hρ hsupp
  have hCI := (bdd_integrable_proof hd hs0 hsd hρ hρΛ hlog X hinj v (K : ℝ) hvl).2.1
  have hPIA : HRS.Commutator.Whole.PairIntegrable A X ρ := by
    rw [hAeq]
    exact cs5_PI_mul _ (k := HRS.Commutator.Whole.commKer (HRS.Commutator.Whole.kernGrad s) v) hCI
  obtain ⟨b, hb⟩ : ∃ b : Euc d → Euc d → ℝ, ∀ x y,
      b x y = HRS.commKernel (periodicRieszGrad d s) W (concMap t x) (concMap t y) - A x y :=
    ⟨_, fun _ _ => rfl⟩
  have hid : ∀ x y : Euc d, ‖x‖ ≤ R0 → ‖y‖ ≤ R0 →
      b x y = t * inner ℝ (v x - v y) (R (t • (x - y))) := by
    intro x y hx hy
    have hpt' := cs5_pt (W := W) (v := v) hR (fun x h1 h2 => (hpt x h1 h2).2) ht hδt htR hWc hx hy
    rw [hb, hA, hpt', cs5_cK_eq]
    ring
  have hbnd : ∀ x y : Euc d, ‖x‖ ≤ R0 → ‖y‖ ≤ R0 →
      |b x y| ≤ 2 * K * M * (t * R0) := by
    intro x y hx hy
    have hd2 : ‖x - y‖ ≤ 2 * R0 := by linarith [norm_sub_le x y]
    have hu : ‖t • (x - y)‖ < δ := by
      rw [norm_smul, Real.norm_of_nonneg ht.le]
      have h1 : t * ‖x - y‖ ≤ t * (2 * R0) := mul_le_mul_of_nonneg_left hd2 ht.le
      have h2 : t * (2 * R0) = 2 * t * R0 := by ring
      linarith
    have hr : ‖R (t • (x - y))‖ ≤ M := hR _ hu
    have hv2 : ‖v x - v y‖ ≤ (K : ℝ) * (2 * R0) := by
      rw [← dist_eq_norm]
      calc dist (v x) (v y) ≤ (K : ℝ) * dist x y := hv.dist_le_mul x y
        _ = (K : ℝ) * ‖x - y‖ := by rw [dist_eq_norm]
        _ ≤ (K : ℝ) * (2 * R0) := mul_le_mul_of_nonneg_left hd2 hKnn
    have hin : |inner ℝ (v x - v y) (R (t • (x - y)))| ≤ (K : ℝ) * (2 * R0) * M := by
      calc |inner ℝ (v x - v y) (R (t • (x - y)))| ≤ ‖v x - v y‖ * ‖R (t • (x - y))‖ :=
            abs_real_inner_le_norm _ _
        _ ≤ ((K : ℝ) * (2 * R0)) * M :=
            mul_le_mul hv2 hr (norm_nonneg _) (mul_nonneg hKnn (by linarith))
    rw [hid x y hx hy, abs_mul, abs_of_pos ht]
    calc t * |inner ℝ (v x - v y) (R (t • (x - y)))| ≤ t * ((K : ℝ) * (2 * R0) * M) :=
          mul_le_mul_of_nonneg_left hin ht.le
      _ = 2 * K * M * (t * R0) := by ring
  have hbm : Measurable (fun p : Euc d × Euc d => b p.1 p.2) := by
    have e : (fun p : Euc d × Euc d => b p.1 p.2) = fun p =>
        HRS.commKernel (periodicRieszGrad d s) W (concMap t p.1) (concMap t p.2) - A p.1 p.2 :=
      funext fun p => hb p.1 p.2
    rw [e]
    refine Measurable.sub ?_ ?_
    · exact hFm.comp (((cs4_concMap_measurable t).comp measurable_fst).prodMk
        ((cs4_concMap_measurable t).comp measurable_snd))
    · have e2 : (fun p : Euc d × Euc d => A p.1 p.2) = fun p =>
          ((t ^ s)⁻¹ * (if s = 0 then 1 else s)) *
            HRS.Commutator.Whole.commKer (HRS.Commutator.Whole.kernGrad s) v p.1 p.2 := by
        funext p
        rw [hAeq]
      rw [e2]
      exact measurable_const.mul (cs5_meas_commKer cs5_meas_kernGrad hvm)
  have hPIb : HRS.Commutator.Whole.PairIntegrable b X ρ :=
    cs5_PI_bd hρ hsupp hXR hbm hbnd
  have hsplit : (fun x y => HRS.commKernel (periodicRieszGrad d s) W (concMap t x) (concMap t y)) =
      fun x y => A x y + b x y := by
    funext x y
    rw [hb]
    ring
  have hpg : HRS.Commutator.Whole.pairGen
      (fun x y => HRS.commKernel (periodicRieszGrad d s) W (concMap t x) (concMap t y)) X ρ =
      HRS.Commutator.Whole.pairGen A X ρ + HRS.Commutator.Whole.pairGen b X ρ := by
    rw [hsplit]
    exact cs4_pairGen_add hPIA hPIb
  have hA_pg : HRS.Commutator.Whole.pairGen A X ρ =
      (t ^ s)⁻¹ * HRS.Commutator.Whole.pairGen (Whole.commutatorKernel d s v) X ρ := by
    have e : A = fun x y => (t ^ s)⁻¹ * Whole.commutatorKernel d s v x y :=
      funext fun x => funext fun y => hA x y
    rw [e]
    exact cs5_pairGen_mul _ (Whole.commutatorKernel d s v)
  have hB0 : 0 ≤ 2 * (K : ℝ) * M * (t * R0) :=
    mul_nonneg (mul_nonneg (mul_nonneg two_pos.le hKnn) hM0) (mul_nonneg ht.le hR0)
  have hbd := cs5_pairGen_bd hρ hsupp hN hXR hbm hB0 hbnd
  rw [hcomm, hQ, hpg, ← hA_pg]
  have hdiff : HRS.Commutator.Whole.pairGen A X ρ + HRS.Commutator.Whole.pairGen b X ρ -
      HRS.Commutator.Whole.pairGen A X ρ = HRS.Commutator.Whole.pairGen b X ρ := by
    ring
  rw [hdiff]
  calc |HRS.Commutator.Whole.pairGen b X ρ| ≤ 4 * (2 * (K : ℝ) * M * (t * R0)) := hbd
    _ = 8 * K * M * (t * R0) := by ring

end HRS.MH.CommSuper
