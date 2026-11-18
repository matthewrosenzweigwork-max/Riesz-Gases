import HRS.PDE.Toolbox.CoeffL2
import HRS.PDE.Toolbox.Kernel

/-!
# Appendix C helper lemmas: Friedrichs commutators (Lemma C.7)

Auxiliary results for `HRS/PDE/Toolbox.lean`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate ContDiff

namespace HRS.PDE
namespace Fried

open Kern

variable {d : ℕ}

theorem mode_add_arg (l : Lattice d) (x y : Torus d) :
    Torus.mode l (x + y) = Torus.mode l x * Torus.mode l y := by
  simp only [Torus.mode, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.add_apply,
    ← Finset.prod_mul_distrib]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [fourier_apply, fourier_apply, fourier_apply, smul_add, AddCircle.toCircle_add]
  simp

theorem mode_neg_arg (l : Lattice d) (y : Torus d) :
    Torus.mode l (-y) = starRingEnd ℂ (Torus.mode l y) := by
  simp only [Torus.mode, UnitAddTorus.mFourier, ContinuousMap.coe_mk, Pi.neg_apply, map_prod]
  refine Finset.prod_congr rfl fun i _ => ?_
  rw [fourier_apply, fourier_apply, smul_neg, fourier_neg']
  rfl

/-! ### Convolution with a trigonometric polynomial and coefficients -/

theorem exists_bound_continuous {f : Torus d → ℂ} (hf : Continuous f) : ∃ c : ℝ, ∀ x, ‖f x‖ ≤ c := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus d)).exists_bound_of_continuousOn hf.continuousOn
  exact ⟨C, fun z => hC z (Set.mem_univ z)⟩

theorem integrable_cont_mul {f G : Torus d → ℂ} (hf : Continuous f) (hG : Integrable G) :
    Integrable (fun y => f y * G y) := by
  obtain ⟨c, hc⟩ := exists_bound_continuous hf
  exact hG.bdd_mul hf.aestronglyMeasurable (Filter.Eventually.of_forall hc)

theorem coeffOfC_trig {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) (k : Lattice d) :
    coeffOfC (trig c) k = c k := by
  rw [coeffOfC_eq_integral']
  have h1 : ∀ x, conj (Torus.mode k x) * trig c x =
      ∑ l ∈ boxF d n, c l * Torus.mode (-k + l) x := by
    intro x
    rw [trig_eq_sum hc, Finset.mul_sum, ← Torus.mode_neg k x]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [Torus.mode_add]; ring
  simp_rw [h1]
  rw [integral_finsetSum _ fun l _ => (Torus.integrable_mode _).const_mul _]
  simp_rw [integral_const_mul, Torus.integral_mode]
  have : ∀ l : Lattice d, (-k + l = 0 ↔ k = l) := fun l => by
    constructor <;> intro h
    · exact (neg_add_eq_zero.1 h)
    · simp [h]
  simp_rw [this]
  simp only [mul_ite, mul_one, mul_zero]
  rw [Finset.sum_ite_eq]
  by_cases hk : k ∈ boxF d n
  · simp [hk]
  · have : c k = 0 := by
      by_contra h; exact hk (mem_boxF.2 (hc k h))
    simp [hk, this]

theorem kconv {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) {G : Torus d → ℂ}
    (hG : Integrable G) (x : Torus d) :
    ∫ y, trig c (x - y) * G y = trig (fun l => c l * coeffOfC G l) x := by
  have hsupp : IsTrigPoly n (fun l => c l * coeffOfC G l) := fun l hl => by
    apply hc
    intro h; apply hl; simp [h]
  have h1 : ∀ y, trig c (x - y) * G y =
      ∑ l ∈ boxF d n, c l * Torus.mode l x * (conj (Torus.mode l y) * G y) := by
    intro y
    rw [trig_eq_sum hc, Finset.sum_mul]
    refine Finset.sum_congr rfl fun l _ => ?_
    rw [sub_eq_add_neg, mode_add_arg, mode_neg_arg]; ring
  simp_rw [h1]
  have hint : ∀ l : Lattice d, Integrable fun y => c l * Torus.mode l x * (conj (Torus.mode l y) * G y) := by
    intro l
    refine Integrable.const_mul ?_ _
    have : Continuous fun y => conj (Torus.mode l y) :=
      Complex.continuous_conj.comp (Torus.continuous_mode l)
    exact integrable_cont_mul this hG
  rw [integral_finsetSum _ fun l _ => hint l, trig_eq_sum hsupp]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [integral_const_mul, coeffOfC_eq_integral']
  ring


theorem isTrigPoly_mul_left {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) (v : Lattice d → ℂ) :
    IsTrigPoly n (fun l => c l * v l) := fun l hl => by
  apply hc
  intro h; apply hl; simp [h]

theorem coeffOfC_sub {F G : Torus d → ℂ} (hF : Continuous F) (hG : Continuous G) (k : Lattice d) :
    coeffOfC (fun x => F x - G x) k = coeffOfC F k - coeffOfC G k := by
  simp only [coeffOfC_eq_integral']
  have hk : Continuous fun x => conj (Torus.mode k x) :=
    Complex.continuous_conj.comp (Torus.continuous_mode k)
  have hI : ∀ {H : Torus d → ℂ}, Continuous H → Integrable H := fun hH =>
    hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [mul_sub]
  exact integral_sub (integrable_cont_mul hk (hI hF)) (integrable_cont_mul hk (hI hG))

theorem integrable_of_continuous_torusC {H : Torus d → ℂ} (hH : Continuous H) : Integrable H :=
  hH.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- `∫ K(x-y) (a(y) - a(x)) U(y) dy`, the commutator kernel operator -/
def commF (c : Lattice d → ℂ) (a : Torus d → ℝ) (U : Torus d → ℂ) (x : Torus d) : ℂ :=
  ∫ y, trig c (x - y) * (((a y : ℝ) : ℂ) - ((a x : ℝ) : ℂ)) * U y

theorem continuous_trig_sub {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) (x : Torus d) :
    Continuous fun y => trig c (x - y) :=
  (continuous_trig hc).comp (continuous_const.sub continuous_id)

theorem commF_eq {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) {a : Torus d → ℝ}
    (ha : Continuous a) {U : Torus d → ℂ} (hU : Integrable U) (x : Torus d) :
    commF c a U x = trig (fun l => c l * coeffOfC (fun y => ((a y : ℝ) : ℂ) * U y) l) x -
      ((a x : ℝ) : ℂ) * trig (fun l => c l * coeffOfC U l) x := by
  have hac : Continuous fun y => ((a y : ℝ) : ℂ) := Complex.continuous_ofReal.comp ha
  have haU : Integrable fun y => ((a y : ℝ) : ℂ) * U y := integrable_cont_mul hac hU
  have h1 : Integrable fun y => trig c (x - y) * (((a y : ℝ) : ℂ) * U y) :=
    integrable_cont_mul (continuous_trig_sub hc x) haU
  have h2 : Integrable fun y => trig c (x - y) * U y := integrable_cont_mul (continuous_trig_sub hc x) hU
  unfold commF
  have : ∀ y, trig c (x - y) * (((a y : ℝ) : ℂ) - ((a x : ℝ) : ℂ)) * U y =
      trig c (x - y) * (((a y : ℝ) : ℂ) * U y) - ((a x : ℝ) : ℂ) * (trig c (x - y) * U y) := by
    intro y; ring
  simp_rw [this]
  rw [integral_sub h1 (h2.const_mul _), integral_const_mul, kconv hc haU, kconv hc hU]

theorem continuous_commF {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) {a : Torus d → ℝ}
    (ha : Continuous a) {U : Torus d → ℂ} (hU : Integrable U) : Continuous (commF c a U) := by
  have : commF c a U = fun x => trig (fun l => c l * coeffOfC (fun y => ((a y : ℝ) : ℂ) * U y) l) x -
      ((a x : ℝ) : ℂ) * trig (fun l => c l * coeffOfC U l) x := funext (commF_eq hc ha hU)
  rw [this]
  exact (continuous_trig (isTrigPoly_mul_left hc _)).sub
    ((Complex.continuous_ofReal.comp ha).mul (continuous_trig (isTrigPoly_mul_left hc _)))

/-- Fourier coefficients of the commutator kernel operator. -/
theorem coeffOfC_commF {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) {a : Torus d → ℝ}
    (ha : Continuous a) {U : Torus d → ℂ} (hU : MemLp U 2 volume) :
    coeffOfC (commF c a U) = fun k => c k * mulCoeff (coeffOf a) (coeffOfC U) k -
      mulCoeff (coeffOf a) (fun l => c l * coeffOfC U l) k := by
  have hU1 : Integrable U := hU.integrable one_le_two
  have hac : Continuous fun y => ((a y : ℝ) : ℂ) := Complex.continuous_ofReal.comp ha
  have hT1 := continuous_trig (isTrigPoly_mul_left hc (coeffOfC (fun y => ((a y : ℝ) : ℂ) * U y)))
  have hT2 := continuous_trig (isTrigPoly_mul_left hc (coeffOfC U))
  have e : commF c a U = fun x => trig (fun l => c l * coeffOfC (fun y => ((a y : ℝ) : ℂ) * U y) l) x -
      ((a x : ℝ) : ℂ) * trig (fun l => c l * coeffOfC U l) x := funext (commF_eq hc ha hU1)
  funext k
  have hT3 : Continuous fun x => ((a x : ℝ) : ℂ) * trig (fun l => c l * coeffOfC U l) x := hac.mul hT2
  rw [e]
  rw [coeffOfC_sub (F := fun x => trig (fun l => c l * coeffOfC (fun y => ((a y : ℝ) : ℂ) * U y) l) x)
    (G := fun x => ((a x : ℝ) : ℂ) * trig (fun l => c l * coeffOfC U l) x) hT1 hT3 k,
    coeffOfC_trig (isTrigPoly_mul_left hc _)]
  have hm := mulCoeff_coeffOfC_mul ha hU
  have hm2 := mulCoeff_coeffOfC_mul ha (memLp_two_of_continuous hT2)
  have : coeffOfC (fun y => ((a y : ℝ) : ℂ) * U y) = mulCoeff (coeffOf a) (coeffOfC U) := hm.2.symm
  have h3 : coeffOfC (trig fun l => c l * coeffOfC U l) = fun l => c l * coeffOfC U l :=
    funext (coeffOfC_trig (isTrigPoly_mul_left hc _))
  rw [this, ← hm2.2, h3]


/-! ### `L²` bounds for kernel operators -/

/-- `∫ K(x-y) G(y) dy` -/
def kop (c : Lattice d → ℂ) (G : Torus d → ℂ) (x : Torus d) : ℂ := ∫ y, trig c (x - y) * G y

theorem integrable_conv_bdd {ρ : Torus d → ℝ} (hρ : AEStronglyMeasurable ρ volume)
    (hρ0 : ∀ z, 0 ≤ ρ z) {M : ℝ} (hM : ∀ z, ρ z ≤ M) {G : Torus d → ℝ} (hG : Integrable G)
    (x : Torus d) : Integrable fun y => ρ (x - y) * G y := by
  have hρ_sub : AEStronglyMeasurable (fun y => ρ (x - y)) volume :=
    hρ.comp_quasiMeasurePreserving (quasiMeasurePreserving_sub_left_of_right_invariant volume x)
  refine Integrable.mono' (hG.norm.const_mul M) (hρ_sub.mul hG.aestronglyMeasurable) ?_
  refine Filter.Eventually.of_forall fun y => ?_
  rw [norm_mul, Real.norm_of_nonneg (hρ0 _)]
  exact mul_le_mul_of_nonneg_right (hM _) (norm_nonneg _)

theorem rho0_data {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) :
    AEStronglyMeasurable (fun z => ‖trig c z‖) volume ∧ (∀ z, 0 ≤ ‖trig c z‖) ∧
      ∃ M : ℝ, ∀ z, ‖trig c z‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_continuous (continuous_trig hc)
  exact ⟨(continuous_trig hc).norm.aestronglyMeasurable, fun z => norm_nonneg _, M, hM⟩

theorem rho1_data {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) :
    AEStronglyMeasurable (fun z => Torus.tdist z 0 * ‖trig c z‖) volume ∧
      (∀ z, 0 ≤ Torus.tdist z 0 * ‖trig c z‖) ∧
      ∃ M : ℝ, ∀ z, Torus.tdist z 0 * ‖trig c z‖ ≤ M := by
  obtain ⟨M, hM⟩ := exists_bound_continuous (continuous_trig hc)
  refine ⟨(measurable_tdist_zero.mul (continuous_trig hc).norm.measurable).aestronglyMeasurable,
    fun z => mul_nonneg (by unfold Torus.tdist; positivity) (norm_nonneg _), d * M, fun z => ?_⟩
  exact mul_le_mul (tdist_zero_le z) (hM z) (norm_nonneg _) (Nat.cast_nonneg d)

/-- Young's inequality for `ρ * ‖U‖`. -/
theorem young_conv {ρ : Torus d → ℝ} (hρ : AEStronglyMeasurable ρ volume) (hρ0 : ∀ z, 0 ≤ ρ z)
    {M : ℝ} (hM : ∀ z, ρ z ≤ M) {U : Torus d → ℂ} (hU : MemLp U 2 volume) :
    MemLp (fun x => ∫ y, ρ (x - y) * ‖U y‖) 2 volume ∧
      ∫ x, (∫ y, ρ (x - y) * ‖U y‖) ^ 2 ≤ (∫ z, ρ z) ^ 2 * ∫ y, ‖U y‖ ^ 2 :=
  young_l2 hρ hρ0 hM hU.aestronglyMeasurable.norm (fun _ => norm_nonneg _) hU.norm

theorem norm_kop_le {c : Lattice d → ℂ} {U : Torus d → ℂ} (x : Torus d) :
    ‖kop c U x‖ ≤ ∫ y, ‖trig c (x - y)‖ * ‖U y‖ := by
  refine (norm_integral_le_integral_norm _).trans (le_of_eq ?_)
  simp only [norm_mul]

/-- `L²` bound for kernel operators: `‖K * U‖² ≤ ‖K‖_{L¹}² ‖U‖²`. -/
theorem l2_kop_le {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) {U : Torus d → ℂ}
    (hU : MemLp U 2 volume) :
    ∫ x, ‖kop c U x‖ ^ 2 ≤ (∫ z, ‖trig c z‖) ^ 2 * ∫ y, ‖U y‖ ^ 2 := by
  obtain ⟨hm, h0, M, hM⟩ := rho0_data hc
  obtain ⟨hA, hY⟩ := young_conv hm h0 hM hU
  refine le_trans (integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => sq_nonneg _)
    hA.integrable_sq (Filter.Eventually.of_forall fun x => ?_)) hY
  exact pow_le_pow_left₀ (norm_nonneg _) (norm_kop_le x) 2


theorem norm_commF_le {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) {a : Torus d → ℝ}
    {M : ℝ} (hM : ∀ x y, |a x - a y| ≤ M * Torus.tdist x y) {U : Torus d → ℂ}
    (hU : Integrable U) (x : Torus d) :
    ‖commF c a U x‖ ≤ M * ∫ y, (Torus.tdist (x - y) 0 * ‖trig c (x - y)‖) * ‖U y‖ := by
  obtain ⟨hm, h0, B, hB⟩ := rho1_data hc
  have hint := integrable_conv_bdd hm h0 hB hU.norm x
  unfold commF
  rw [← integral_const_mul]
  refine (norm_integral_le_integral_norm _).trans ?_
  refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun y => norm_nonneg _)
    (hint.const_mul M) (Filter.Eventually.of_forall fun y => ?_)
  simp only [norm_mul]
  have h1 : ‖(((a y : ℝ) : ℂ) - ((a x : ℝ) : ℂ))‖ ≤ M * Torus.tdist (x - y) 0 := by
    rw [← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs, abs_sub_comm]
    have := hM x y
    simpa [Torus.tdist] using this
  have := mul_le_mul_of_nonneg_left h1 (norm_nonneg (trig c (x - y)))
  calc ‖trig c (x - y)‖ * ‖(((a y : ℝ) : ℂ) - ((a x : ℝ) : ℂ))‖ * ‖U y‖
      ≤ ‖trig c (x - y)‖ * (M * Torus.tdist (x - y) 0) * ‖U y‖ :=
        mul_le_mul_of_nonneg_right this (norm_nonneg _)
    _ = M * (Torus.tdist (x - y) 0 * ‖trig c (x - y)‖ * ‖U y‖) := by ring

/-- `L²` bound for the commutator kernel operator. -/
theorem l2_commF_le {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) {a : Torus d → ℝ}
    (ha : Continuous a) {M : ℝ} (hM : ∀ x y, |a x - a y| ≤ M * Torus.tdist x y)
    {U : Torus d → ℂ} (hU : MemLp U 2 volume) :
    ∫ x, ‖commF c a U x‖ ^ 2 ≤ M ^ 2 * ((∫ z, Torus.tdist z 0 * ‖trig c z‖) ^ 2 * ∫ y, ‖U y‖ ^ 2) := by
  obtain ⟨hm, h0, B, hB⟩ := rho1_data hc
  obtain ⟨hA, hY⟩ := young_conv hm h0 hB hU
  have hU1 : Integrable U := hU.integrable one_le_two
  have hcont := continuous_commF hc ha hU1
  calc ∫ x, ‖commF c a U x‖ ^ 2
      ≤ ∫ x, M ^ 2 * (∫ y, (Torus.tdist (x - y) 0 * ‖trig c (x - y)‖) * ‖U y‖) ^ 2 := by
        refine integral_mono (integrable_of_continuous_torus (hcont.norm.pow 2))
          (hA.integrable_sq.const_mul _) fun x => ?_
        calc ‖commF c a U x‖ ^ 2 ≤ (M * ∫ y, (Torus.tdist (x - y) 0 * ‖trig c (x - y)‖) * ‖U y‖) ^ 2 :=
              pow_le_pow_left₀ (norm_nonneg _) (norm_commF_le hc hM hU1 x) 2
          _ = _ := by ring
    _ = M ^ 2 * ∫ x, (∫ y, (Torus.tdist (x - y) 0 * ‖trig c (x - y)‖) * ‖U y‖) ^ 2 := by
        rw [integral_const_mul]
    _ ≤ _ := by gcongr


theorem kop_eq {n : ℕ} {c : Lattice d → ℂ} (hc : IsTrigPoly n c) {U : Torus d → ℂ}
    (hU : Integrable U) : kop c U = trig (fun l => c l * coeffOfC U l) :=
  funext fun x => kconv hc hU x

/-- `∫ K'(x-y)(a(y)-a(x))U(y) dy - a'(x) ∫ K(x-y) U(y) dy` -/
def commD (c' c : Lattice d → ℂ) (a a' : Torus d → ℝ) (U : Torus d → ℂ) (x : Torus d) : ℂ :=
  commF c' a U x - ((a' x : ℝ) : ℂ) * kop c U x

theorem continuous_commD {n : ℕ} {c' c : Lattice d → ℂ} (hc' : IsTrigPoly n c')
    (hc : IsTrigPoly n c) {a a' : Torus d → ℝ} (ha : Continuous a) (ha' : Continuous a')
    {U : Torus d → ℂ} (hU : Integrable U) : Continuous (commD c' c a a' U) := by
  unfold commD
  rw [kop_eq hc hU]
  exact (continuous_commF hc' ha hU).sub
    ((Complex.continuous_ofReal.comp ha').mul (continuous_trig (isTrigPoly_mul_left hc _)))

theorem coeffOfC_commD {n : ℕ} {c' c : Lattice d → ℂ} (hc' : IsTrigPoly n c')
    (hc : IsTrigPoly n c) {a a' : Torus d → ℝ} (ha : Continuous a) (ha' : Continuous a')
    {U : Torus d → ℂ} (hU : MemLp U 2 volume) :
    coeffOfC (commD c' c a a' U) = fun k => c' k * mulCoeff (coeffOf a) (coeffOfC U) k -
      mulCoeff (coeffOf a) (fun l => c' l * coeffOfC U l) k -
      mulCoeff (coeffOf a') (fun l => c l * coeffOfC U l) k := by
  have hU1 : Integrable U := hU.integrable one_le_two
  have hT2 := continuous_trig (isTrigPoly_mul_left hc (coeffOfC U))
  have hT3 : Continuous fun x => ((a' x : ℝ) : ℂ) * trig (fun l => c l * coeffOfC U l) x :=
    (Complex.continuous_ofReal.comp ha').mul hT2
  have e : commD c' c a a' U = fun x => commF c' a U x -
      ((a' x : ℝ) : ℂ) * trig (fun l => c l * coeffOfC U l) x := by
    funext x; unfold commD; rw [kop_eq hc hU1]
  funext k
  rw [e, coeffOfC_sub (F := commF c' a U) (G := fun x => ((a' x : ℝ) : ℂ) * trig (fun l => c l * coeffOfC U l) x)
    (continuous_commF hc' ha hU1) hT3 k, coeffOfC_commF hc' ha hU]
  have hm2 := mulCoeff_coeffOfC_mul ha' (memLp_two_of_continuous hT2)
  have h3 : coeffOfC (trig fun l => c l * coeffOfC U l) = fun l => c l * coeffOfC U l :=
    funext (coeffOfC_trig (isTrigPoly_mul_left hc _))
  rw [← hm2.2, h3]

theorem l2_commD_le {n : ℕ} {c' c : Lattice d → ℂ} (hc' : IsTrigPoly n c')
    (hc : IsTrigPoly n c) {a a' : Torus d → ℝ} (ha : Continuous a) (ha' : Continuous a')
    {M M' : ℝ} (hM : ∀ x y, |a x - a y| ≤ M * Torus.tdist x y) (hM' : ∀ x, |a' x| ≤ M')
    {U : Torus d → ℂ} (hU : MemLp U 2 volume) :
    ∫ x, ‖commD c' c a a' U x‖ ^ 2 ≤
      2 * (M ^ 2 * ((∫ z, Torus.tdist z 0 * ‖trig c' z‖) ^ 2 * ∫ y, ‖U y‖ ^ 2)) +
      2 * (M' ^ 2 * ((∫ z, ‖trig c z‖) ^ 2 * ∫ y, ‖U y‖ ^ 2)) := by
  have hU1 : Integrable U := hU.integrable one_le_two
  have hF := l2_commF_le hc' ha hM hU
  have hK := l2_kop_le hc hU
  have hcF : Continuous (commF c' a U) := continuous_commF hc' ha hU1
  have hkc : Continuous (kop c U) := by rw [kop_eq hc hU1]; exact continuous_trig (isTrigPoly_mul_left hc _)
  have hcD := continuous_commD hc' hc ha ha' hU1
  have hpt : ∀ x, ‖commD c' c a a' U x‖ ^ 2 ≤
      2 * ‖commF c' a U x‖ ^ 2 + 2 * (M' ^ 2 * ‖kop c U x‖ ^ 2) := by
    intro x
    unfold commD
    have h1 : ‖((a' x : ℝ) : ℂ) * kop c U x‖ ≤ M' * ‖kop c U x‖ := by
      rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_right (hM' x) (norm_nonneg _)
    have h2 := norm_sub_le (commF c' a U x) (((a' x : ℝ) : ℂ) * kop c U x)
    have h3 : ‖commF c' a U x - ((a' x : ℝ) : ℂ) * kop c U x‖ ≤
        ‖commF c' a U x‖ + M' * ‖kop c U x‖ := h2.trans (by linarith)
    have h4 := norm_nonneg (commF c' a U x - ((a' x : ℝ) : ℂ) * kop c U x)
    nlinarith [sq_nonneg (‖commF c' a U x‖ - M' * ‖kop c U x‖), norm_nonneg (commF c' a U x),
      mul_nonneg (norm_nonneg (kop c U x)) (norm_nonneg (kop c U x))]
  have hi1 : Integrable fun x => ‖commF c' a U x‖ ^ 2 := integrable_of_continuous_torus (hcF.norm.pow 2)
  have hi2 : Integrable fun x => M' ^ 2 * ‖kop c U x‖ ^ 2 :=
    (integrable_of_continuous_torus (hkc.norm.pow 2)).const_mul _
  calc ∫ x, ‖commD c' c a a' U x‖ ^ 2
      ≤ ∫ x, (2 * ‖commF c' a U x‖ ^ 2 + 2 * (M' ^ 2 * ‖kop c U x‖ ^ 2)) :=
        integral_mono (integrable_of_continuous_torus (hcD.norm.pow 2))
          ((hi1.const_mul 2).add (hi2.const_mul 2)) hpt
    _ = 2 * (∫ x, ‖commF c' a U x‖ ^ 2) + 2 * (M' ^ 2 * ∫ x, ‖kop c U x‖ ^ 2) := by
        rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul, integral_const_mul,
          integral_const_mul]
    _ ≤ _ := by gcongr


/-! ### The mollifier and the commutator on coefficients -/

/-- The mollifier `J_ε = χ(εD)²` on coefficient sequences (same as `mollify` of `Toolbox.lean`). -/
def mol (χ : Euc d → ℝ) (ε : ℝ) (c : Coeff d) : Coeff d :=
  fun k => ((χ (ε • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) * c k

/-- `[J_ε, a]u` on coefficients (same as `mollifyCommutator`). -/
def molComm (χ : Euc d → ℝ) (ε : ℝ) (a : Torus d → ℝ) (u : Coeff d) : Coeff d :=
  mol χ ε (mulCoeff (coeffOf a) u) - mulCoeff (coeffOf a) (mol χ ε u)

/-- symbol `ψ = χ²` as a complex function -/
def psiC (χ : Euc d → ℝ) : Euc d → ℂ := fun ξ => ((χ ξ ^ 2 : ℝ) : ℂ)

/-- the coefficients `ψ(εk)` -/
def cpsi (χ : Euc d → ℝ) (ε : ℝ) : Lattice d → ℂ := kcoef (psiC χ) ε

/-- the coefficients of `∂_j K_ε`: `2πi k_j ψ(εk)` -/
def cder (χ : Euc d → ℝ) (ε : ℝ) (j : Fin d) : Lattice d → ℂ :=
  fun k => cpsi χ ε k * (2 * Real.pi * Complex.I * (k j : ℂ))

theorem mol_eq (χ : Euc d → ℝ) (ε : ℝ) (u : Coeff d) : mol χ ε u = fun l => cpsi χ ε l * u l := rfl

theorem molComm_eq {n : ℕ} (χ : Euc d → ℝ) {ε : ℝ} (hc : IsTrigPoly n (cpsi χ ε))
    {a : Torus d → ℝ} (ha : Continuous a) {u : Coeff d} (hu : MemHs 0 u) :
    molComm χ ε a u = coeffOfC (commF (cpsi χ ε) a (ofCoeff u)) := by
  have hU : MemLp (ofCoeff u) 2 volume := memLp_ofCoeff hu
  rw [coeffOfC_commF hc ha hU, coeffOfC_ofCoeff hu]
  rfl

theorem memHs_one_of_finite {n : ℕ} {v : Coeff d} (hv : IsTrigPoly n v) : MemHs 1 v :=
  summable_of_ne_finset_zero (s := boxF d n) fun k hk => by
    have : v k = 0 := by
      by_contra h; exact hk (mem_boxF.2 (hv k h))
    simp [this]

theorem deriv_molComm {n : ℕ} (χ : Euc d → ℝ) {ε : ℝ} (hc : IsTrigPoly n (cpsi χ ε))
    {a : Torus d → ℝ} (ha : Torus.IsCk 1 a) {u : Coeff d} (hu : MemHs 0 u) (j : Fin d) :
    derivCoeff j (molComm χ ε a u) =
      coeffOfC (commD (cder χ ε j) (cpsi χ ε) a (Torus.partialDeriv j a) (ofCoeff u)) := by
  have hac := continuous_of_isCk ha
  have hU : MemLp (ofCoeff u) 2 volume := memLp_ofCoeff hu
  have hc' : IsTrigPoly n (cder χ ε j) := isTrigPoly_mul_left hc _
  rw [coeffOfC_commD hc' hc hac (continuous_partialDeriv' ha j) hU, coeffOfC_ofCoeff hu]
  have hv : MemHs 1 (fun l => cpsi χ ε l * u l) := memHs_one_of_finite (isTrigPoly_mul_left hc u)
  have hL := derivCoeff_mulCoeffC ha hv j
  funext k
  have hk : 2 * Real.pi * Complex.I * (k j : ℂ) * mulCoeff (coeffOf a) (fun l => cpsi χ ε l * u l) k =
      mulCoeff (coeffOf (Torus.partialDeriv j a)) (fun l => cpsi χ ε l * u l) k +
      mulCoeff (coeffOf a) (fun l => 2 * Real.pi * Complex.I * (l j : ℂ) * (cpsi χ ε l * u l)) k :=
    congrFun hL k
  have e1 : (fun l => cder χ ε j l * u l) =
      fun l => 2 * Real.pi * Complex.I * (l j : ℂ) * (cpsi χ ε l * u l) := by
    funext l; simp only [cder]; ring
  rw [e1]
  show 2 * Real.pi * Complex.I * (k j : ℂ) * (cpsi χ ε k * mulCoeff (coeffOf a) u k -
      mulCoeff (coeffOf a) (fun l => cpsi χ ε l * u l) k) = _
  rw [mul_sub, hk]
  simp only [cder]
  ring


/-! ### Kernel constants for a Friedrichs cutoff -/

/-- the hypotheses of `IsFriedrichsCutoff`, unpacked -/
structure CutoffHyp (χ : Euc d → ℝ) : Prop where
  smooth : ContDiff ℝ ∞ χ
  range : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1
  one : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1
  supp : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → χ ξ = 0

/-- `ξ ↦ 2πi ξ_j ψ(ξ)` -/
def Phi (χ : Euc d → ℝ) (j : Fin d) : Euc d → ℂ :=
  fun ξ => (2 * Real.pi * Complex.I * ((ξ j : ℝ) : ℂ)) * psiC χ ξ

theorem contDiff_psiC {χ : Euc d → ℝ} (h : CutoffHyp χ) : ContDiff ℝ ∞ (psiC χ) :=
  Complex.ofRealCLM.contDiff.comp (h.smooth.pow 2)

theorem psiC_supp {χ : Euc d → ℝ} (h : CutoffHyp χ) : ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → psiC χ ξ = 0 := by
  intro ξ hξ
  simp [psiC, h.supp ξ hξ]

theorem contDiff_Phi {χ : Euc d → ℝ} (h : CutoffHyp χ) (j : Fin d) : ContDiff ℝ ∞ (Phi χ j) := by
  have h1 : ContDiff ℝ ∞ fun ξ : Euc d => ((ξ j : ℝ) : ℂ) :=
    Complex.ofRealCLM.contDiff.comp (EuclideanSpace.proj (𝕜 := ℝ) j).contDiff
  exact (contDiff_const.mul h1).mul (contDiff_psiC h)

theorem Phi_supp {χ : Euc d → ℝ} (h : CutoffHyp χ) (j : Fin d) :
    ∀ ξ : Euc d, 2 ≤ ‖ξ‖ → Phi χ j ξ = 0 := by
  intro ξ hξ
  simp [Phi, psiC_supp h ξ hξ]

theorem cder_eq {χ : Euc d → ℝ} {ε : ℝ} (hε : 0 < ε) (j : Fin d) :
    cder χ ε j = fun l => (ε⁻¹ : ℂ) * kcoef (Phi χ j) ε l := by
  funext l
  have hε' : (ε : ℂ) ≠ 0 := by exact_mod_cast hε.ne'
  simp only [cder, cpsi, kcoef, Phi, psiC, Lattice.toEuc, PiLp.smul_apply, smul_eq_mul]
  push_cast
  field_simp

theorem trig_cder {χ : Euc d → ℝ} {ε : ℝ} (hε : 0 < ε) (j : Fin d) (z : Torus d) :
    trig (cder χ ε j) z = (ε⁻¹ : ℂ) * kern (Phi χ j) ε z := by
  simp only [kern, trig]
  rw [cder_eq hε, ← tsum_mul_left]
  refine tsum_congr fun l => ?_
  ring

theorem kernel_consts {χ : Euc d → ℝ} (h : CutoffHyp χ) :
    ∃ C0 C1 Cd : ℝ, 0 ≤ C0 ∧ 0 ≤ C1 ∧ 0 ≤ Cd ∧ ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
      IsTrigPoly ⌈2 / ε⌉₊ (cpsi χ ε) ∧ (∀ j, IsTrigPoly ⌈2 / ε⌉₊ (cder χ ε j)) ∧
      (∫ z, ‖trig (cpsi χ ε) z‖ ≤ C0) ∧
      (∫ z, Torus.tdist z 0 * ‖trig (cpsi χ ε) z‖ ≤ C1 * ε) ∧
      ∀ j, ∫ z, Torus.tdist z 0 * ‖trig (cder χ ε j) z‖ ≤ Cd := by
  obtain ⟨C0, hC0, h0⟩ := kern_L1_bound (contDiff_psiC h) (psiC_supp h)
  obtain ⟨C1, hC1, h1⟩ := kern_L1_moment_bound (contDiff_psiC h) (psiC_supp h)
  choose Cj hCj hCjb using fun j : Fin d => kern_L1_moment_bound (contDiff_Phi h j) (Phi_supp h j)
  refine ⟨C0, C1, ∑ j, Cj j, hC0, hC1, Finset.sum_nonneg fun j _ => hCj j, fun ε hε hε1 => ?_⟩
  have hc : IsTrigPoly ⌈2 / ε⌉₊ (cpsi χ ε) := isTrigPoly_kcoef (psiC_supp h) hε
  refine ⟨hc, fun j => isTrigPoly_mul_left hc _, (h0 ε hε hε1).2, (h1 ε hε hε1).2, fun j => ?_⟩
  obtain ⟨hint, hb⟩ := hCjb j ε hε hε1
  have : ∀ z, Torus.tdist z 0 * ‖trig (cder χ ε j) z‖ =
      ε⁻¹ * (Torus.tdist z 0 * ‖kern (Phi χ j) ε z‖) := by
    intro z
    rw [trig_cder hε, norm_mul]
    simp [abs_of_pos hε]
    ring
  simp_rw [this]
  rw [integral_const_mul]
  calc ε⁻¹ * ∫ z, Torus.tdist z 0 * ‖kern (Phi χ j) ε z‖ ≤ ε⁻¹ * (Cj j * ε) := by gcongr
    _ = Cj j := by field_simp
    _ ≤ ∑ j, Cj j := Finset.single_le_sum (f := Cj) (fun j _ => hCj j) (Finset.mem_univ j)


theorem tdist_nonneg' (x y : Torus d) : 0 ≤ Torus.tdist x y := by unfold Torus.tdist; positivity

theorem iSup_fderiv_le_cbNorm {a : Torus d → ℝ} (ha : Torus.IsCk 1 a) :
    (⨆ x : Euc d, ‖fderiv ℝ (Torus.lift a) x‖) ≤ Torus.cbNorm 1 a := by
  have hbdd : BddAbove (Set.range fun x : Euc d => ‖iteratedFDeriv ℝ 1 (Torus.lift a) x‖) :=
    Torus.bddAbove_norm_iteratedFDeriv_lift 1 a (by exact_mod_cast ha)
  have h1 : (⨆ x : Euc d, ‖fderiv ℝ (Torus.lift a) x‖) ≤
      ⨆ y : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift a) y‖ := by
    refine ciSup_le fun x => ?_
    rw [← norm_iteratedFDeriv_one]
    exact le_ciSup hbdd x
  refine h1.trans ?_
  unfold Torus.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ y : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift a) y‖)
    (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by norm_num))

theorem iSup_fderiv_nonneg (a : Torus d → ℝ) : 0 ≤ ⨆ x : Euc d, ‖fderiv ℝ (Torus.lift a) x‖ :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem hsNorm_le_of_sq {m : ℝ} {c : Coeff d} {y : ℝ} (hy : 0 ≤ y) (h : hsNormSq m c ≤ y ^ 2) :
    hsNorm m c ≤ y := Real.sqrt_le_iff.2 ⟨hy, h⟩

/-- Lemma C.7, first part, in the unpacked form. -/
theorem friedrichs_main {χ : Euc d → ℝ} (h : CutoffHyp χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (a : Torus d → ℝ), Torus.IsCk 1 a → ∀ u : Coeff d, MemHs 0 u →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        MemHs 1 (molComm χ ε a u) ∧
        hsNorm 0 (molComm χ ε a u) ≤
          C * ε * (⨆ x : Euc d, ‖fderiv ℝ (Torus.lift a) x‖) * hsNorm 0 u ∧
        ∀ σ : ℝ, 0 ≤ σ → σ ≤ 1 →
          hsNorm σ (molComm χ ε a u) ≤ C * ε ^ (1 - σ) * Torus.cbNorm 1 a * hsNorm 0 u := by
  obtain ⟨C0, C1, Cd, hC0, hC1, hCd, hK⟩ := kernel_consts h
  set Cb : ℝ := C1 ^ 2 + 2 * (d * (Cd ^ 2 + C0 ^ 2)) with hCb
  have hCb0 : 0 ≤ Cb := by positivity
  set C : ℝ := max C1 (Real.sqrt Cb) with hCdef
  have hCC1 : C1 ≤ C := le_max_left _ _
  have hC0' : 0 ≤ C := hC1.trans hCC1
  have hCCb : Cb ≤ C ^ 2 := by
    have : Real.sqrt Cb ≤ C := le_max_right _ _
    calc Cb = Real.sqrt Cb ^ 2 := (Real.sq_sqrt hCb0).symm
      _ ≤ C ^ 2 := pow_le_pow_left₀ (Real.sqrt_nonneg _) this 2
  refine ⟨C, hC0', fun a ha u hu ε hε hε1 => ?_⟩
  obtain ⟨hc, hc', hI0, hI1, hId⟩ := hK ε hε hε1
  have hac : Continuous a := continuous_of_isCk ha
  have hU : MemLp (ofCoeff u) 2 volume := memLp_ofCoeff hu
  have hU1 : Integrable (ofCoeff u) := hU.integrable one_le_two
  have hN : hsNormSq 0 u = ∫ y, ‖ofCoeff u y‖ ^ 2 := by
    have := (hsNormSq_zero_coeffOfC (ofCoeff u) hU).2
    rwa [coeffOfC_ofCoeff hu] at this
  have hN0 : 0 ≤ hsNormSq 0 u := hsNormSq_zero_nonneg u
  set M := ⨆ x : Euc d, ‖fderiv ℝ (Torus.lift a) x‖ with hMdef
  set S := Torus.cbNorm 1 a with hSdef
  have hM0 : 0 ≤ M := iSup_fderiv_nonneg a
  have hMS : M ≤ S := iSup_fderiv_le_cbNorm ha
  have hS0 : 0 ≤ S := hM0.trans hMS
  have hM : ∀ x y, |a x - a y| ≤ M * Torus.tdist x y := abs_sub_le_iSup_mul_tdist ha
  set T := molComm χ ε a u with hT
  have hTeq : T = coeffOfC (commF (cpsi χ ε) a (ofCoeff u)) := molComm_eq χ hc hac hu
  have hcF := continuous_commF hc hac hU1
  obtain ⟨hT0, hTN⟩ := hsNormSq_zero_coeffOfC _ (memLp_two_of_continuous hcF)
  rw [← hTeq] at hT0 hTN
  have hρ1 : 0 ≤ ∫ z, Torus.tdist z 0 * ‖trig (cpsi χ ε) z‖ :=
    integral_nonneg fun z => mul_nonneg (tdist_nonneg' _ _) (norm_nonneg _)
  have hρ0 : 0 ≤ ∫ z, ‖trig (cpsi χ ε) z‖ := integral_nonneg fun z => norm_nonneg _
  -- the L² bound
  have hX1 : hsNormSq 0 T ≤ (C1 * ε * M) ^ 2 * hsNormSq 0 u := by
    rw [hTN]
    refine (l2_commF_le hc hac hM hU).trans ?_
    rw [← hN]
    have h2 := pow_le_pow_left₀ hρ1 hI1 2
    calc M ^ 2 * ((∫ z, Torus.tdist z 0 * ‖trig (cpsi χ ε) z‖) ^ 2 * hsNormSq 0 u)
        ≤ M ^ 2 * ((C1 * ε) ^ 2 * hsNormSq 0 u) := by gcongr
      _ = _ := by ring
  have hX : hsNormSq 0 T ≤ (C * ε * M) ^ 2 * hsNormSq 0 u := by
    refine hX1.trans ?_
    have : C1 * ε * M ≤ C * ε * M := by gcongr
    have := pow_le_pow_left₀ (by positivity) this 2
    gcongr
  -- the derivatives
  have hD : ∀ j : Fin d, MemHs 0 (derivCoeff j T) ∧
      hsNormSq 0 (derivCoeff j T) ≤ 2 * (S ^ 2 * Cd ^ 2 * hsNormSq 0 u) + 2 * (S ^ 2 * C0 ^ 2 * hsNormSq 0 u) := by
    intro j
    have hDe : derivCoeff j T = coeffOfC (commD (cder χ ε j) (cpsi χ ε) a (Torus.partialDeriv j a) (ofCoeff u)) :=
      deriv_molComm χ hc ha hu j
    have hcD := continuous_commD (hc' j) hc hac (continuous_partialDeriv' ha j) hU1
    obtain ⟨hm0, hmN⟩ := hsNormSq_zero_coeffOfC _ (memLp_two_of_continuous hcD)
    rw [← hDe] at hm0 hmN
    refine ⟨hm0, ?_⟩
    rw [hmN]
    have hb := l2_commD_le (hc' j) hc hac (continuous_partialDeriv' ha j) hM
      (fun x => (abs_partialDeriv_le ha j x)) hU
    rw [← hN] at hb
    have e1 : (∫ z, Torus.tdist z 0 * ‖trig (cder χ ε j) z‖) ^ 2 ≤ Cd ^ 2 :=
      pow_le_pow_left₀ (integral_nonneg fun z => mul_nonneg (tdist_nonneg' _ _) (norm_nonneg _)) (hId j) 2
    have e2 : (∫ z, ‖trig (cpsi χ ε) z‖) ^ 2 ≤ C0 ^ 2 := pow_le_pow_left₀ hρ0 hI0 2
    have e3 : M ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hM0 hMS 2
    refine hb.trans ?_
    have := mul_le_mul e3 e1 (sq_nonneg _) (sq_nonneg _)
    have := mul_le_mul e2 le_rfl hN0 (sq_nonneg _)
    nlinarith [mul_le_mul_of_nonneg_right (mul_le_mul e3 e1 (sq_nonneg _) (sq_nonneg _)) hN0,
      mul_le_mul_of_nonneg_left (mul_le_mul e2 le_rfl hN0 (sq_nonneg _)) (sq_nonneg S)]
  have hT1 : MemHs 1 T := (memHs_one_iff T).2 ⟨hT0, fun j => (hD j).1⟩
  have hY : hsNormSq 1 T ≤ C ^ 2 * S ^ 2 * hsNormSq 0 u := by
    rw [hsNormSq_one_eq T hT1]
    have h1 : ∑ j, hsNormSq 0 (derivCoeff j T) ≤
        ∑ _j : Fin d, (2 * (S ^ 2 * Cd ^ 2 * hsNormSq 0 u) + 2 * (S ^ 2 * C0 ^ 2 * hsNormSq 0 u)) :=
      Finset.sum_le_sum fun j _ => (hD j).2
    simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at h1
    have hX' : hsNormSq 0 T ≤ C1 ^ 2 * S ^ 2 * hsNormSq 0 u := by
      refine hX1.trans ?_
      have h3 : C1 * ε * M ≤ C1 * S := by
        have : ε * M ≤ 1 * S := mul_le_mul hε1 hMS hM0 zero_le_one
        calc C1 * ε * M = C1 * (ε * M) := by ring
          _ ≤ C1 * S := by nlinarith
      have := pow_le_pow_left₀ (by positivity) h3 2
      calc (C1 * ε * M) ^ 2 * hsNormSq 0 u ≤ (C1 * S) ^ 2 * hsNormSq 0 u := by gcongr
        _ = _ := by ring
    calc hsNormSq 0 T + ∑ j, hsNormSq 0 (derivCoeff j T)
        ≤ C1 ^ 2 * S ^ 2 * hsNormSq 0 u + d * (2 * (S ^ 2 * Cd ^ 2 * hsNormSq 0 u) + 2 * (S ^ 2 * C0 ^ 2 * hsNormSq 0 u)) :=
          add_le_add hX' h1
      _ = Cb * S ^ 2 * hsNormSq 0 u := by rw [hCb]; ring
      _ ≤ C ^ 2 * S ^ 2 * hsNormSq 0 u := by gcongr
  have hsN : 0 ≤ Real.sqrt (hsNormSq 0 u) := Real.sqrt_nonneg _
  have hsN2 : Real.sqrt (hsNormSq 0 u) ^ 2 = hsNormSq 0 u := Real.sq_sqrt hN0
  refine ⟨hT1, ?_, fun σ hσ0 hσ1 => ?_⟩
  · refine hsNorm_le_of_sq (by positivity) ?_
    calc hsNormSq 0 T ≤ (C * ε * M) ^ 2 * hsNormSq 0 u := hX
      _ = (C * ε * M * Real.sqrt (hsNormSq 0 u)) ^ 2 := by
          rw [mul_pow (C * ε * M) (Real.sqrt (hsNormSq 0 u)) 2, hsN2]
  · obtain ⟨hmem, hint⟩ := hsNormSq_interpolation 0 1 σ hσ0 hσ1 T hT0
      (by simpa using hT1)
    simp only [mul_zero, zero_add, mul_one] at hint
    have hQ : 0 ≤ C ^ 2 * S ^ 2 * hsNormSq 0 u := by positivity
    have hP : hsNormSq 0 T ≤ ε ^ 2 * (C ^ 2 * S ^ 2 * hsNormSq 0 u) := by
      refine hX.trans ?_
      have : M ^ 2 ≤ S ^ 2 := pow_le_pow_left₀ hM0 hMS 2
      calc (C * ε * M) ^ 2 * hsNormSq 0 u = ε ^ 2 * (C ^ 2 * M ^ 2 * hsNormSq 0 u) := by ring
        _ ≤ _ := by gcongr
    have hY0 : 0 ≤ hsNormSq 1 T :=
      tsum_nonneg fun k => mul_nonneg (sobWeight_posC 1 k).le (sq_nonneg _)
    refine hsNorm_le_of_sq (by positivity) ?_
    calc hsNormSq σ T ≤ hsNormSq 0 T ^ (1 - σ) * hsNormSq 1 T ^ σ := hint
      _ ≤ (ε ^ 2 * (C ^ 2 * S ^ 2 * hsNormSq 0 u)) ^ (1 - σ) * (C ^ 2 * S ^ 2 * hsNormSq 0 u) ^ σ := by
          exact mul_le_mul (Real.rpow_le_rpow (hsNormSq_zero_nonneg T) hP (by linarith))
            (Real.rpow_le_rpow (hY0) hY hσ0)
            (Real.rpow_nonneg (hY0) _) (Real.rpow_nonneg (by positivity) _)
      _ = (ε ^ (1 - σ)) ^ 2 * (C ^ 2 * S ^ 2 * hsNormSq 0 u) := by
          rw [Real.mul_rpow (by positivity) hQ, mul_assoc, ← Real.rpow_add' hQ (by linarith)]
          have : (ε ^ 2) ^ (1 - σ) = (ε ^ (1 - σ)) ^ 2 := by
            rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul hε.le, ← Real.rpow_mul hε.le]
            ring_nf
          rw [this]; simp
      _ = (C * ε ^ (1 - σ) * S * Real.sqrt (hsNormSq 0 u)) ^ 2 := by
          rw [mul_pow (C * ε ^ (1 - σ) * S) (Real.sqrt (hsNormSq 0 u)) 2, hsN2]; ring

/-! ### The transport commutator -/

theorem memHs_neg_one_deriv {u : Coeff d} (hu : MemHs 0 u) (j : Fin d) :
    MemHs (-1) (derivCoeff j u) := by
  unfold MemHs at *
  simp only [sobWeight_zeroC, one_mul] at hu
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (sobWeight_posC _ k).le (sq_nonneg _))
    (fun k => ?_) hu
  rw [norm_derivCoeff_sq]
  have h1 : sobWeight (-1) k = (sobWeight 1 k)⁻¹ := by
    unfold sobWeight; rw [Real.rpow_neg_one, Real.rpow_one]
  have h2 : (2 * Real.pi * (k j : ℝ)) ^ 2 ≤ sobWeight 1 k := by
    rw [sobWeight_one_eq]
    have := Finset.single_le_sum (f := fun i => (2 * Real.pi * (k i : ℝ)) ^ 2)
      (fun i _ => sq_nonneg _) (Finset.mem_univ j)
    linarith
  have hp := sobWeight_posC (d := d) 1 k
  rw [h1]
  calc (sobWeight 1 k)⁻¹ * ((2 * Real.pi * (k j : ℝ)) ^ 2 * ‖u k‖ ^ 2)
      = ((2 * Real.pi * (k j : ℝ)) ^ 2 / sobWeight 1 k) * ‖u k‖ ^ 2 := by field_simp
    _ ≤ 1 * ‖u k‖ ^ 2 := by
        gcongr
        rw [div_le_one hp]; exact h2
    _ = ‖u k‖ ^ 2 := one_mul _

theorem dual_summable {b : Torus d → ℝ} (hb : Torus.IsCk 1 b) {u : Coeff d} (hu : MemHs 0 u)
    (j : Fin d) (k : Lattice d) :
    Summable fun l => coeffOf b (k - l) * derivCoeff j u l :=
  summable_mulCoeff_dual hb (memHs_neg_one_deriv hu j) k

theorem leibniz0 {b : Torus d → ℝ} (hb : Torus.IsCk 1 b) {u : Coeff d} (hu : MemHs 0 u) (j : Fin d) :
    derivCoeff j (mulCoeff (coeffOf b) u) =
      mulCoeff (coeffOf (Torus.partialDeriv j b)) u + mulCoeff (coeffOf b) (derivCoeff j u) := by
  rw [coeffOf_partialDeriv_eq j b hb]
  refine derivCoeff_mulCoeff_of_summable _ _ j (fun k => ?_) (fun k => ?_)
  · have := summable_coeffOf_mul_of_memHs (continuous_partialDeriv' hb j) hu k
    rwa [coeffOf_partialDeriv_eq j b hb] at this
  · exact dual_summable hb hu j k

/-- `∫ K'(x-y)(b(y)-b(x))U(y) dy - ∫ K(x-y) b'(y) U(y) dy` -/
def transD (c' c : Lattice d → ℂ) (b b' : Torus d → ℝ) (U : Torus d → ℂ) (x : Torus d) : ℂ :=
  commF c' b U x - kop c (fun y => ((b' y : ℝ) : ℂ) * U y) x

theorem integrable_mul_real {b' : Torus d → ℝ} (hb' : Continuous b') {U : Torus d → ℂ}
    (hU : Integrable U) : Integrable fun y => ((b' y : ℝ) : ℂ) * U y :=
  integrable_cont_mul (Complex.continuous_ofReal.comp hb') hU

theorem continuous_transD {n : ℕ} {c' c : Lattice d → ℂ} (hc' : IsTrigPoly n c')
    (hc : IsTrigPoly n c) {b b' : Torus d → ℝ} (hb : Continuous b) (hb' : Continuous b')
    {U : Torus d → ℂ} (hU : Integrable U) : Continuous (transD c' c b b' U) := by
  unfold transD
  rw [kop_eq hc (integrable_mul_real hb' hU)]
  exact (continuous_commF hc' hb hU).sub (continuous_trig (isTrigPoly_mul_left hc _))

theorem coeffOfC_transD {n : ℕ} {c' c : Lattice d → ℂ} (hc' : IsTrigPoly n c')
    (hc : IsTrigPoly n c) {b b' : Torus d → ℝ} (hb : Continuous b) (hb' : Continuous b')
    {U : Torus d → ℂ} (hU : MemLp U 2 volume) :
    coeffOfC (transD c' c b b' U) = fun k => c' k * mulCoeff (coeffOf b) (coeffOfC U) k -
      mulCoeff (coeffOf b) (fun l => c' l * coeffOfC U l) k -
      c k * mulCoeff (coeffOf b') (coeffOfC U) k := by
  have hU1 : Integrable U := hU.integrable one_le_two
  have hbU := integrable_mul_real hb' hU1
  have hT : Continuous fun x => trig (fun l => c l * coeffOfC (fun y => ((b' y : ℝ) : ℂ) * U y) l) x :=
    continuous_trig (isTrigPoly_mul_left hc _)
  have e : transD c' c b b' U = fun x => commF c' b U x -
      trig (fun l => c l * coeffOfC (fun y => ((b' y : ℝ) : ℂ) * U y) l) x := by
    funext x; unfold transD; rw [kop_eq hc hbU]
  funext k
  rw [e, coeffOfC_sub (F := commF c' b U) (G := fun x =>
    trig (fun l => c l * coeffOfC (fun y => ((b' y : ℝ) : ℂ) * U y) l) x)
    (continuous_commF hc' hb hU1) hT k, coeffOfC_commF hc' hb hU,
    coeffOfC_trig (isTrigPoly_mul_left hc _)]
  have := (mulCoeff_coeffOfC_mul hb' hU).2
  rw [← this]

theorem norm_sub_sq_le' (x y : ℂ) : ‖x - y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖y‖ ^ 2 := by
  have h2 := norm_sub_le x y
  nlinarith [sq_nonneg (‖x‖ - ‖y‖), norm_nonneg x, norm_nonneg y, norm_nonneg (x - y)]

theorem l2_transD_le {n : ℕ} {c' c : Lattice d → ℂ} (hc' : IsTrigPoly n c')
    (hc : IsTrigPoly n c) {b b' : Torus d → ℝ} (hb : Continuous b) (hb' : Continuous b')
    {M M' : ℝ} (hM : ∀ x y, |b x - b y| ≤ M * Torus.tdist x y) (hM' : ∀ x, |b' x| ≤ M')
    {U : Torus d → ℂ} (hU : MemLp U 2 volume) :
    ∫ x, ‖transD c' c b b' U x‖ ^ 2 ≤
      2 * (M ^ 2 * ((∫ z, Torus.tdist z 0 * ‖trig c' z‖) ^ 2 * ∫ y, ‖U y‖ ^ 2)) +
      2 * ((∫ z, ‖trig c z‖) ^ 2 * (M' ^ 2 * ∫ y, ‖U y‖ ^ 2)) := by
  have hU1 : Integrable U := hU.integrable one_le_two
  have hbU1 := integrable_mul_real hb' hU1
  have hbUm : MemLp (fun y => ((b' y : ℝ) : ℂ) * U y) 2 volume := by
    refine MemLp.of_le_mul (c := M') hU
      ((Complex.continuous_ofReal.comp hb').aestronglyMeasurable.mul hU.aestronglyMeasurable)
      (Filter.Eventually.of_forall fun y => ?_)
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs]
    exact mul_le_mul_of_nonneg_right (hM' y) (norm_nonneg _)
  have hF := l2_commF_le hc' hb hM hU
  have hK := l2_kop_le hc hbUm
  have hcF : Continuous (commF c' b U) := continuous_commF hc' hb hU1
  have hkc : Continuous (kop c fun y => ((b' y : ℝ) : ℂ) * U y) := by
    rw [kop_eq hc hbU1]; exact continuous_trig (isTrigPoly_mul_left hc _)
  have hcD := continuous_transD hc' hc hb hb' hU1
  have hbN : ∫ y, ‖((b' y : ℝ) : ℂ) * U y‖ ^ 2 ≤ M' ^ 2 * ∫ y, ‖U y‖ ^ 2 := by
    rw [← integral_const_mul]
    refine integral_mono hbUm.norm.integrable_sq (hU.norm.integrable_sq.const_mul _) fun y => ?_
    simp only
    rw [norm_mul, Complex.norm_real, Real.norm_eq_abs, mul_pow]
    exact mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (abs_nonneg _) (hM' y) 2) (sq_nonneg _)
  have hi1 : Integrable fun x => ‖commF c' b U x‖ ^ 2 := integrable_of_continuous_torus (hcF.norm.pow 2)
  have hi2 : Integrable fun x => ‖kop c (fun y => ((b' y : ℝ) : ℂ) * U y) x‖ ^ 2 :=
    integrable_of_continuous_torus (hkc.norm.pow 2)
  calc ∫ x, ‖transD c' c b b' U x‖ ^ 2
      ≤ ∫ x, (2 * ‖commF c' b U x‖ ^ 2 + 2 * ‖kop c (fun y => ((b' y : ℝ) : ℂ) * U y) x‖ ^ 2) :=
        integral_mono (integrable_of_continuous_torus (hcD.norm.pow 2))
          ((hi1.const_mul 2).add (hi2.const_mul 2)) fun x => norm_sub_sq_le' _ _
    _ = 2 * (∫ x, ‖commF c' b U x‖ ^ 2) +
          2 * (∫ x, ‖kop c (fun y => ((b' y : ℝ) : ℂ) * U y) x‖ ^ 2) := by
        rw [integral_add (hi1.const_mul 2) (hi2.const_mul 2), integral_const_mul, integral_const_mul]
    _ ≤ _ := by
        have : (∫ z, ‖trig c z‖) ^ 2 * ∫ y, ‖((b' y : ℝ) : ℂ) * U y‖ ^ 2 ≤
            (∫ z, ‖trig c z‖) ^ 2 * (M' ^ 2 * ∫ y, ‖U y‖ ^ 2) := by gcongr
        linarith


theorem coeffOfC_sum {ι : Type*} (s : Finset ι) {F : ι → Torus d → ℂ} (hF : ∀ i, Continuous (F i))
    (k : Lattice d) :
    coeffOfC (fun x => ∑ i ∈ s, F i x) k = ∑ i ∈ s, coeffOfC (F i) k := by
  simp only [coeffOfC_eq_integral']
  have hk : Continuous fun x => conj (Torus.mode k x) :=
    Complex.continuous_conj.comp (Torus.continuous_mode k)
  simp_rw [Finset.mul_sum]
  exact integral_finsetSum _ fun i _ => integrable_cont_mul hk (integrable_of_continuous_torusC (hF i))

/-- `[J_ε, b·∇]u` on coefficients (same as `mollifyTransportCommutator`). -/
def mtc (χ : Euc d → ℝ) (ε : ℝ) (b : Fin d → Torus d → ℝ) (u : Coeff d) : Coeff d :=
  mol χ ε (fun k => ∑ j, mulCoeff (coeffOf (b j)) (derivCoeff j u) k) -
    fun k => ∑ j, mulCoeff (coeffOf (b j)) (derivCoeff j (mol χ ε u)) k

theorem deriv_mol (χ : Euc d → ℝ) (ε : ℝ) (j : Fin d) (u : Coeff d) :
    derivCoeff j (mol χ ε u) = fun l => cder χ ε j l * u l := by
  funext l
  simp only [derivCoeff, mol_eq, cder]
  ring

theorem mtc_eq {n : ℕ} (χ : Euc d → ℝ) {ε : ℝ} (hc : IsTrigPoly n (cpsi χ ε))
    (hc' : ∀ j, IsTrigPoly n (cder χ ε j)) {b : Fin d → Torus d → ℝ}
    (hb : ∀ j, Torus.IsCk 1 (b j)) {u : Coeff d} (hu : MemHs 0 u) :
    mtc χ ε b u = coeffOfC (fun x => ∑ j, transD (cder χ ε j) (cpsi χ ε) (b j)
      (Torus.partialDeriv j (b j)) (ofCoeff u) x) := by
  have hU : MemLp (ofCoeff u) 2 volume := memLp_ofCoeff hu
  have hU1 : Integrable (ofCoeff u) := hU.integrable one_le_two
  funext k
  rw [coeffOfC_sum _ (fun j => continuous_transD (hc' j) hc (continuous_of_isCk (hb j))
    (continuous_partialDeriv' (hb j) j) hU1)]
  have hj : ∀ j, coeffOfC (transD (cder χ ε j) (cpsi χ ε) (b j) (Torus.partialDeriv j (b j)) (ofCoeff u)) k =
      cpsi χ ε k * mulCoeff (coeffOf (b j)) (derivCoeff j u) k -
        mulCoeff (coeffOf (b j)) (derivCoeff j (mol χ ε u)) k := by
    intro j
    rw [coeffOfC_transD (hc' j) hc (continuous_of_isCk (hb j)) (continuous_partialDeriv' (hb j) j) hU,
      coeffOfC_ofCoeff hu, deriv_mol]
    have hL := congrFun (leibniz0 (hb j) hu j) k
    simp only [derivCoeff, Pi.add_apply] at hL
    simp only [cder]
    linear_combination (cpsi χ ε k) * hL
  rw [Finset.sum_congr rfl fun j _ => hj j, Finset.sum_sub_distrib, ← Finset.mul_sum]
  rfl


theorem abs_partialDeriv_le_iSup {b : Torus d → ℝ} (hb : Torus.IsCk 1 b) (j : Fin d) (x : Torus d) :
    |Torus.partialDeriv j b x| ≤ ⨆ z : Euc d, ‖fderiv ℝ (Torus.lift b) z‖ := by
  refine le_trans ?_ (norm_fderiv_lift_le_iSup hb (Torus.rep x))
  have := (fderiv ℝ (Torus.lift b) (Torus.rep x)).le_opNorm (EuclideanSpace.single j (1 : ℝ))
  rw [PiLp.norm_single] at this
  simpa [Torus.partialDeriv] using this

theorem norm_sum_sq_le (s : Finset (Fin d)) (v : Fin d → ℂ) :
    ‖∑ j ∈ s, v j‖ ^ 2 ≤ d * ∑ j ∈ s, ‖v j‖ ^ 2 := by
  have h1 : ‖∑ j ∈ s, v j‖ ≤ ∑ j ∈ s, ‖v j‖ := norm_sum_le _ _
  have h2 := sq_sum_le_card_mul_sum_sq (s := s) (f := fun j => ‖v j‖)
  have h3 : (s.card : ℝ) ≤ d := by
    exact_mod_cast (Finset.card_le_univ s).trans (by simp)
  calc ‖∑ j ∈ s, v j‖ ^ 2 ≤ (∑ j ∈ s, ‖v j‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ s.card * ∑ j ∈ s, ‖v j‖ ^ 2 := h2
    _ ≤ d * ∑ j ∈ s, ‖v j‖ ^ 2 := by
        gcongr

theorem transport_main {χ : Euc d → ℝ} (h : CutoffHyp χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ b : Fin d → Torus d → ℝ, (∀ j, Torus.IsCk 1 (b j)) → ∀ u : Coeff d, MemHs 0 u →
      ∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        MemHs 0 (mtc χ ε b u) ∧
        hsNormSq 0 (mtc χ ε b u) ≤
          (C * ∑ j, ⨆ x : Euc d, ‖fderiv ℝ (Torus.lift (b j)) x‖) ^ 2 * hsNormSq 0 u := by
  obtain ⟨C0, C1, Cd, hC0, hC1, hCd, hK⟩ := kernel_consts h
  set C : ℝ := Real.sqrt (2 * d * (Cd ^ 2 + C0 ^ 2)) with hCdef
  have hC2 : C ^ 2 = 2 * d * (Cd ^ 2 + C0 ^ 2) := Real.sq_sqrt (by positivity)
  refine ⟨C, Real.sqrt_nonneg _, fun b hb u hu ε hε hε1 => ?_⟩
  obtain ⟨hc, hc', hI0, hI1, hId⟩ := hK ε hε hε1
  have hU : MemLp (ofCoeff u) 2 volume := memLp_ofCoeff hu
  have hU1 : Integrable (ofCoeff u) := hU.integrable one_le_two
  have hN : hsNormSq 0 u = ∫ y, ‖ofCoeff u y‖ ^ 2 := by
    have := (hsNormSq_zero_coeffOfC (ofCoeff u) hU).2
    rwa [coeffOfC_ofCoeff hu] at this
  have hN0 : 0 ≤ hsNormSq 0 u := hsNormSq_zero_nonneg u
  set M : Fin d → ℝ := fun j => ⨆ x : Euc d, ‖fderiv ℝ (Torus.lift (b j)) x‖ with hMdef
  have hM0 : ∀ j, 0 ≤ M j := fun j => iSup_fderiv_nonneg (b j)
  set F : Torus d → ℂ := fun x => ∑ j, transD (cder χ ε j) (cpsi χ ε) (b j)
    (Torus.partialDeriv j (b j)) (ofCoeff u) x with hFdef
  have hFc : Continuous F := continuous_finsetSum _ fun j _ =>
    continuous_transD (hc' j) hc (continuous_of_isCk (hb j)) (continuous_partialDeriv' (hb j) j) hU1
  have hEq : mtc χ ε b u = coeffOfC F := mtc_eq χ hc hc' hb hu
  obtain ⟨hT0, hTN⟩ := hsNormSq_zero_coeffOfC F (memLp_two_of_continuous hFc)
  rw [← hEq] at hT0 hTN
  refine ⟨hT0, ?_⟩
  rw [hTN]
  have hj : ∀ j, ∫ x, ‖transD (cder χ ε j) (cpsi χ ε) (b j) (Torus.partialDeriv j (b j)) (ofCoeff u) x‖ ^ 2 ≤
      2 * (M j ^ 2 * (Cd ^ 2 * hsNormSq 0 u)) + 2 * (C0 ^ 2 * (M j ^ 2 * hsNormSq 0 u)) := by
    intro j
    have hb1 := l2_transD_le (hc' j) hc (continuous_of_isCk (hb j))
      (continuous_partialDeriv' (hb j) j) (abs_sub_le_iSup_mul_tdist (hb j))
      (fun x => abs_partialDeriv_le_iSup (hb j) j x) hU
    rw [← hN] at hb1
    have e1 : (∫ z, Torus.tdist z 0 * ‖trig (cder χ ε j) z‖) ^ 2 ≤ Cd ^ 2 :=
      pow_le_pow_left₀ (integral_nonneg fun z => mul_nonneg (tdist_nonneg' _ _) (norm_nonneg _)) (hId j) 2
    have e2 : (∫ z, ‖trig (cpsi χ ε) z‖) ^ 2 ≤ C0 ^ 2 :=
      pow_le_pow_left₀ (integral_nonneg fun z => norm_nonneg _) hI0 2
    refine hb1.trans ?_
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e1 hN0) (sq_nonneg (M j))
    have := mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e2 (mul_nonneg (sq_nonneg (M j)) hN0))
      (sq_nonneg (M j))
    nlinarith [mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_right e1 hN0) (sq_nonneg (M j)),
      mul_le_mul_of_nonneg_right e2 (mul_nonneg (sq_nonneg (M j)) hN0)]
  have hcj : ∀ j, Continuous fun x => transD (cder χ ε j) (cpsi χ ε) (b j)
      (Torus.partialDeriv j (b j)) (ofCoeff u) x := fun j =>
    continuous_transD (hc' j) hc (continuous_of_isCk (hb j)) (continuous_partialDeriv' (hb j) j) hU1
  have hint : ∀ j, Integrable fun x => ‖transD (cder χ ε j) (cpsi χ ε) (b j)
      (Torus.partialDeriv j (b j)) (ofCoeff u) x‖ ^ 2 := fun j =>
    integrable_of_continuous_torus ((hcj j).norm.pow 2)
  calc ∫ x, ‖F x‖ ^ 2
      ≤ ∫ x, (d * ∑ j, ‖transD (cder χ ε j) (cpsi χ ε) (b j)
          (Torus.partialDeriv j (b j)) (ofCoeff u) x‖ ^ 2) :=
        integral_mono (integrable_of_continuous_torus (hFc.norm.pow 2))
          ((integrable_finsetSum _ fun j _ => hint j).const_mul _) fun x => norm_sum_sq_le _ _
    _ = d * ∑ j, ∫ x, ‖transD (cder χ ε j) (cpsi χ ε) (b j)
          (Torus.partialDeriv j (b j)) (ofCoeff u) x‖ ^ 2 := by
        rw [integral_const_mul, integral_finsetSum _ fun j _ => hint j]
    _ ≤ d * ∑ j, (2 * (M j ^ 2 * (Cd ^ 2 * hsNormSq 0 u)) + 2 * (C0 ^ 2 * (M j ^ 2 * hsNormSq 0 u))) := by
        gcongr with j _
        exact hj j
    _ = C ^ 2 * (∑ j, M j ^ 2) * hsNormSq 0 u := by
        rw [hC2, Finset.mul_sum, Finset.mul_sum, Finset.sum_mul]
        refine Finset.sum_congr rfl fun j _ => by ring
    _ ≤ C ^ 2 * (∑ j, M j) ^ 2 * hsNormSq 0 u := by
        have : ∑ j, M j ^ 2 ≤ (∑ j, M j) ^ 2 := by
          rw [sq, Finset.sum_mul]
          refine Finset.sum_le_sum fun j _ => ?_
          rw [sq]
          exact mul_le_mul_of_nonneg_left
            (Finset.single_le_sum (f := M) (fun i _ => hM0 i) (Finset.mem_univ j)) (hM0 j)
        gcongr
    _ = _ := by ring


theorem memHs_of_finite (m : ℝ) {n : ℕ} {v : Coeff d} (hv : IsTrigPoly n v) : MemHs m v :=
  summable_of_ne_finset_zero (s := boxF d n) fun k hk => by
    have : v k = 0 := by
      by_contra h; exact hk (mem_boxF.2 (hv k h))
    simp [this]

theorem isTrigPoly_deriv {n : ℕ} {v : Coeff d} (hv : IsTrigPoly n v) (j : Fin d) :
    IsTrigPoly n (derivCoeff j v) := by
  intro k hk
  apply hv
  intro h
  apply hk
  simp [derivCoeff, h]

theorem norm_psi_le (χ : Euc d → ℝ) (hχ : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1) (ξ : Euc d) :
    ‖((χ ξ ^ 2 : ℝ) : ℂ)‖ ≤ 1 := by
  rw [Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
  exact pow_le_one₀ (hχ ξ).1 (hχ ξ).2

theorem memHs_zero_mol {χ : Euc d → ℝ} (hχ : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1) (ε : ℝ) {x : Coeff d}
    (hx : MemHs 0 x) : MemHs 0 (mol χ ε x) := by
  rw [memHs_zero_iffC] at hx ⊢
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hx
  simp only [mol, norm_mul]
  have := norm_psi_le χ hχ (ε • Lattice.toEuc k)
  have h2 : ‖((χ (ε • Lattice.toEuc k) ^ 2 : ℝ) : ℂ)‖ * ‖x k‖ ≤ ‖x k‖ := by
    calc _ ≤ 1 * ‖x k‖ := mul_le_mul_of_nonneg_right this (norm_nonneg _)
      _ = _ := one_mul _
  exact pow_le_pow_left₀ (by positivity) h2 2

theorem mulCoeff_add_of_summable (a x y : Coeff d)
    (hx : ∀ k, Summable fun l => a (k - l) * x l) (hy : ∀ k, Summable fun l => a (k - l) * y l) :
    mulCoeff a (x + y) = mulCoeff a x + mulCoeff a y := by
  funext k
  simp only [mulCoeff, Pi.add_apply, mul_add]
  exact (hx k).tsum_add (hy k)

theorem mtc_add {χ : Euc d → ℝ} (hχ : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1) (ε : ℝ)
    {b : Fin d → Torus d → ℝ} (hb : ∀ j, Torus.IsCk 1 (b j)) {x y : Coeff d}
    (hx : MemHs 0 x) (hy : MemHs 0 y) :
    mtc χ ε b (x + y) = mtc χ ε b x + mtc χ ε b y := by
  have e1 : ∀ (j : Fin d) (x y : Coeff d), derivCoeff j (x + y) = derivCoeff j x + derivCoeff j y := by
    intro j x y; funext k; simp only [derivCoeff, Pi.add_apply]; ring
  have e2 : mol χ ε (x + y) = mol χ ε x + mol χ ε y := by
    funext k; simp only [mol, Pi.add_apply]; ring
  have hmx := memHs_zero_mol hχ ε hx
  have hmy := memHs_zero_mol hχ ε hy
  have e3 : ∀ j, mulCoeff (coeffOf (b j)) (derivCoeff j (x + y)) =
      mulCoeff (coeffOf (b j)) (derivCoeff j x) + mulCoeff (coeffOf (b j)) (derivCoeff j y) := by
    intro j; rw [e1 j x y]
    exact mulCoeff_add_of_summable _ _ _ (dual_summable (hb j) hx j) (dual_summable (hb j) hy j)
  have e4 : ∀ j, mulCoeff (coeffOf (b j)) (derivCoeff j (mol χ ε (x + y))) =
      mulCoeff (coeffOf (b j)) (derivCoeff j (mol χ ε x)) +
        mulCoeff (coeffOf (b j)) (derivCoeff j (mol χ ε y)) := by
    intro j; rw [e2, e1 j]
    exact mulCoeff_add_of_summable _ _ _ (dual_summable (hb j) hmx j) (dual_summable (hb j) hmy j)
  funext k
  unfold mtc
  simp only [Pi.sub_apply, Pi.add_apply, mol, e3, e4, Finset.sum_add_distrib]
  ring

theorem eventually_mol_eq {χ : Euc d → ℝ} (hone : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1) {n : ℕ}
    {v : Coeff d} (hv : IsTrigPoly n v) :
    ∀ᶠ ε : ℝ in 𝓝[>] 0, mol χ ε v = v := by
  have h1 : ∀ l : Lattice d, ∀ᶠ ε : ℝ in 𝓝 0, ‖ε • Lattice.toEuc l‖ < 1 := fun l => by
    have : Tendsto (fun ε : ℝ => ‖ε • Lattice.toEuc l‖) (𝓝 0) (𝓝 0) := by
      have hc : Continuous (fun ε : ℝ => ‖ε • Lattice.toEuc l‖) := by fun_prop
      simpa using hc.tendsto 0
    exact this.eventually_lt_const one_pos
  have h2 : ∀ᶠ ε : ℝ in 𝓝 0, ∀ l ∈ boxF d n, ‖ε • Lattice.toEuc l‖ < 1 :=
    (Filter.eventually_all_finset _).2 fun l _ => h1 l
  filter_upwards [nhdsWithin_le_nhds h2] with ε hε
  funext l
  by_cases hl : v l = 0
  · simp [mol, hl]
  · have := hone _ (hε l (mem_boxF.2 (hv l hl))).le
    simp [mol, this]

theorem tendsto_psi_sub_one {χ : Euc d → ℝ} (hcont : Continuous χ) (hone : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1)
    (k : Lattice d) :
    Tendsto (fun ε : ℝ => (((χ (ε • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) - 1)) (𝓝[>] 0) (𝓝 0) := by
  have h0 : Tendsto (fun ε : ℝ => χ (ε • Lattice.toEuc k)) (𝓝 0) (𝓝 1) := by
    have hc : Continuous (fun ε : ℝ => χ (ε • Lattice.toEuc k)) := by fun_prop
    simpa [hone 0 (by simp)] using hc.tendsto 0
  have h1 : Tendsto (fun ε : ℝ => (((χ (ε • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) - 1)) (𝓝 0) (𝓝 (((1 ^ 2 : ℝ) : ℂ) - 1)) :=
    ((Complex.continuous_ofReal.tendsto _).comp (h0.pow 2)).sub tendsto_const_nhds
  simpa using h1.mono_left nhdsWithin_le_nhds


theorem memHs_zero_sum (s : Finset (Fin d)) (f : Fin d → Coeff d) (hf : ∀ j, MemHs 0 (f j)) :
    MemHs 0 (fun k => ∑ j ∈ s, f j k) := by
  classical
  induction s using Finset.induction_on with
  | empty =>
    rw [memHs_zero_iffC]
    simp
  | insert a s ha ih =>
    have := (hsNormSq_zero_add_le (hf a) ih).1
    convert this using 1
    funext k
    simp [Finset.sum_insert ha]

theorem mtc_trig_tendsto {χ : Euc d → ℝ} (hcont : Continuous χ) (hχ : ∀ ξ, 0 ≤ χ ξ ∧ χ ξ ≤ 1)
    (hone : ∀ ξ : Euc d, ‖ξ‖ ≤ 1 → χ ξ = 1) {b : Fin d → Torus d → ℝ}
    (hb : ∀ j, Torus.IsCk 1 (b j)) {n : ℕ} {v : Coeff d} (hv : IsTrigPoly n v) :
    Tendsto (fun ε : ℝ => hsNormSq 0 (mtc χ ε b v)) (𝓝[>] 0) (𝓝 0) := by
  set w : Coeff d := fun k => ∑ j, mulCoeff (coeffOf (b j)) (derivCoeff j v) k with hwdef
  have hw : MemHs 0 w := memHs_zero_sum _ _ fun j =>
    (mulCoeff_l2_bound (continuous_of_isCk (hb j)) (memHs_of_finite 0 (isTrigPoly_deriv hv j))).1
  have hw2 : Summable fun k => ‖w k‖ ^ 2 := (memHs_zero_iffC w).1 hw
  have heq : ∀ᶠ ε : ℝ in 𝓝[>] 0, hsNormSq 0 (mtc χ ε b v) =
      ∑' k, ‖(((χ (ε • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) - 1) * w k‖ ^ 2 := by
    filter_upwards [eventually_mol_eq hone hv] with ε hε
    have : mtc χ ε b v = fun k => (((χ (ε • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) - 1) * w k := by
      unfold mtc
      rw [hε]
      funext k
      simp only [Pi.sub_apply, mol]
      ring
    rw [this]
    unfold hsNormSq
    simp only [sobWeight_zeroC, one_mul]
  refine Tendsto.congr' (heq.mono fun ε h => h.symm) ?_
  have := tendsto_tsum_of_dominated_convergence (𝓕 := 𝓝[>] (0 : ℝ))
    (f := fun (ε : ℝ) (k : Lattice d) => ‖(((χ (ε • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) - 1) * w k‖ ^ 2)
    (g := fun _ => (0 : ℝ)) (bound := fun k => ‖w k‖ ^ 2) hw2
    (fun k => by
      have h1 := ((tendsto_psi_sub_one hcont hone k).mul_const (w k)).norm.pow 2
      simpa using h1)
    (Filter.Eventually.of_forall fun ε k => by
      rw [Real.norm_of_nonneg (sq_nonneg _), norm_mul, mul_pow]
      have hp0 : 0 ≤ χ (ε • Lattice.toEuc k) ^ 2 := sq_nonneg _
      have hp1 : χ (ε • Lattice.toEuc k) ^ 2 ≤ 1 :=
        pow_le_one₀ (hχ _).1 (hχ _).2
      have h1 : ‖(((χ (ε • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) - 1)‖ ≤ 1 := by
        rw [← Complex.ofReal_one, ← Complex.ofReal_sub, Complex.norm_real, Real.norm_eq_abs]
        exact abs_le.2 ⟨by linarith, by linarith⟩
      have h2 : ‖(((χ (ε • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) - 1)‖ ^ 2 ≤ 1 := by
        calc _ ≤ 1 ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h1 2
          _ = 1 := one_pow 2
      calc ‖(((χ (ε • Lattice.toEuc k) ^ 2 : ℝ) : ℂ) - 1)‖ ^ 2 * ‖w k‖ ^ 2 ≤ 1 * ‖w k‖ ^ 2 :=
            mul_le_mul_of_nonneg_right h2 (sq_nonneg _)
        _ = ‖w k‖ ^ 2 := one_mul _)
  simpa using this


theorem memHs_zero_sub_trunc (n : ℕ) {u : Coeff d} (hu : MemHs 0 u) :
    MemHs 0 (u - truncCoeff n u) := by
  rw [memHs_zero_iffC] at hu ⊢
  refine Summable.of_nonneg_of_le (fun k => sq_nonneg _) (fun k => ?_) hu
  simp only [Pi.sub_apply, truncCoeff]
  split_ifs <;> simp

theorem isTrigPoly_trunc (n : ℕ) (u : Coeff d) : IsTrigPoly n (truncCoeff n u) := by
  intro k hk
  by_contra h
  apply hk
  simp [truncCoeff, h]

theorem mtc_tendsto {χ : Euc d → ℝ} (h : CutoffHyp χ) {b : Fin d → Torus d → ℝ}
    (hb : ∀ j, Torus.IsCk 1 (b j)) {u : Coeff d} (hu : MemHs 0 u) :
    Tendsto (fun ε : ℝ => hsNormSq 0 (mtc χ ε b u)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := transport_main h
  set K2 : ℝ := (C * ∑ j, ⨆ x : Euc d, ‖fderiv ℝ (Torus.lift (b j)) x‖) ^ 2 with hK2
  have hK20 : 0 ≤ K2 := sq_nonneg _
  rw [Metric.tendsto_nhds]
  intro δ hδ
  obtain ⟨-, htr⟩ := truncCoeff_tendsto 0 u hu
  have h1 : Tendsto (fun n : ℕ => (2 * K2) * hsNorm 0 (u - truncCoeff n u) ^ 2) atTop (𝓝 0) := by
    simpa using (htr.pow 2).const_mul (2 * K2)
  obtain ⟨N, hN⟩ := (h1.eventually_lt_const (half_pos hδ)).exists
  set uN := truncCoeff N u with huN
  set r := u - uN with hr
  have huN0 : MemHs 0 uN := memHs_of_finite 0 (isTrigPoly_trunc N u)
  have hr0 : MemHs 0 r := memHs_zero_sub_trunc N hu
  have hrsq : hsNormSq 0 r = hsNorm 0 r ^ 2 := (Real.sq_sqrt (hsNormSq_zero_nonneg r)).symm
  have h2 := mtc_trig_tendsto h.smooth.continuous h.range h.one hb (isTrigPoly_trunc N u)
  have h3 : ∀ᶠ ε : ℝ in 𝓝[>] 0, hsNormSq 0 (mtc χ ε b uN) < δ / 4 :=
    h2.eventually_lt_const (by positivity)
  have h4 : ∀ᶠ ε : ℝ in 𝓝[>] (0 : ℝ), 0 < ε ∧ ε ≤ 1 := by
    filter_upwards [Ioo_mem_nhdsGT (zero_lt_one : (0 : ℝ) < 1)] with ε hε using ⟨hε.1, hε.2.le⟩
  filter_upwards [h3, h4] with ε hε3 hε4
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (hsNormSq_zero_nonneg _)]
  have hsplit : mtc χ ε b u = mtc χ ε b uN + mtc χ ε b r := by
    have := mtc_add h.range ε hb huN0 hr0
    rwa [hr, add_sub_cancel] at this
  obtain ⟨hmN, -⟩ := hC b hb uN huN0 ε hε4.1 hε4.2
  obtain ⟨hmr, hbr⟩ := hC b hb r hr0 ε hε4.1 hε4.2
  have := (hsNormSq_zero_add_le hmN hmr).2
  rw [hsplit]
  rw [hrsq] at hbr
  nlinarith


/-- Lemma C.7, second part, in the unpacked form. -/
theorem friedrichs_transport_main {χ : Euc d → ℝ} (h : CutoffHyp χ) :
    ∃ C : ℝ, ∀ (b : Fin d → Torus d → ℝ), (∀ j, Torus.IsCk 1 (b j)) → ∀ (u : Coeff d), MemHs 0 u →
      (∀ ε : ℝ, 0 < ε → ε ≤ 1 →
        MemHs 0 (mtc χ ε b u) ∧
        hsNorm 0 (mtc χ ε b u) ≤
          C * (∑ j, ⨆ x : Euc d, ‖fderiv ℝ (Torus.lift (b j)) x‖) * hsNorm 0 u) ∧
      Tendsto (fun ε => hsNorm 0 (mtc χ ε b u)) (𝓝[>] 0) (𝓝 0) := by
  obtain ⟨C, hC0, hC⟩ := transport_main h
  refine ⟨C, fun b hb u hu => ⟨fun ε hε hε1 => ?_, ?_⟩⟩
  · obtain ⟨hm, hbd⟩ := hC b hb u hu ε hε hε1
    refine ⟨hm, hsNorm_le_of_sq ?_ ?_⟩
    · exact mul_nonneg (mul_nonneg hC0 (Finset.sum_nonneg fun j _ => iSup_fderiv_nonneg (b j)))
        (Real.sqrt_nonneg _)
    · rw [mul_pow, hsNorm, Real.sq_sqrt (hsNormSq_zero_nonneg u)]
      exact hbd
  · have := (Real.continuous_sqrt.tendsto 0).comp (mtc_tendsto h hb hu)
    simpa [hsNorm, Function.comp_def] using this

end Fried
end HRS.PDE
