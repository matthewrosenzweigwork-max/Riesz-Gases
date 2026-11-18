import HRS.Whole.AppendixA
import HRS.MH.CoercLowerDefs

/-!
# CoercLower B1: generic plumbing (packets P01a-e, P02a-c)

Proofs of the statements in `HRS/MH/CoercLowerSpec.lean`, copied verbatim.
-/

noncomputable section

open MeasureTheory
open scoped BigOperators

namespace HRS.MH.CoercLower


variable {d N : ℕ}

/-- [P01a] -/
theorem isProbDensity_integrable {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ) : Integrable ρ := by
  by_contra h
  have h1 := hρ.integral_one
  rw [integral_undef h] at h1
  exact zero_ne_one h1

/-- [P01b] -/
theorem eucCollisionSet_iff {X : HRS.Whole.EucConfig d N} :
    X ∉ HRS.Whole.eucCollisionSet d N ↔ Function.Injective X := by
  constructor
  · intro hX a b hab
    by_contra hne
    exact hX ⟨a, b, hne, hab⟩
  · intro hinj hX
    obtain ⟨i, j, hij, hXij⟩ := hX
    exact hij (hinj hXij)

/-- [P01c] -/
theorem measurable_rieszKernel (d : ℕ) (s : ℝ) : Measurable (HRS.Whole.rieszKernel d s) := by
  by_cases hs : s = 0
  · have : HRS.Whole.rieszKernel d s = fun x => -Real.log ‖x‖ := by
      funext x
      simp [HRS.Whole.rieszKernel, hs]
    rw [this]
    fun_prop
  · have : HRS.Whole.rieszKernel d s = fun x => ‖x‖ ^ (-s) := by
      funext x
      simp [HRS.Whole.rieszKernel, hs]
    rw [this]
    fun_prop

/-- [P01d] The junk value at `0` is `0` for `s ≥ 0`. -/
theorem rieszKernel_zero (d : ℕ) {s : ℝ} (hs : 0 ≤ s) : HRS.Whole.rieszKernel d s 0 = 0 := by
  by_cases h0 : s = 0
  · simp [HRS.Whole.rieszKernel, h0]
  · have hpos : s ≠ 0 := h0
    have hneg : -s ≠ 0 := neg_ne_zero.mpr hpos
    simp only [HRS.Whole.rieszKernel, if_neg hpos, norm_zero]
    exact Real.zero_rpow hneg

/-- [P01e] -/
theorem ae_ne_zero (hd : 1 ≤ d) : ∀ᵐ z : Euc d ∂volume, z ≠ 0 := by
  have hnt : Nontrivial (Euc d) := by
    obtain ⟨n, rfl⟩ : ∃ n, d = n + 1 := ⟨d - 1, by omega⟩
    infer_instance
  have h0 : volume ({0} : Set (Euc d)) = 0 := measure_singleton 0
  rw [ae_iff]
  simpa using h0

/-- [P02a] -/
theorem convMeasure_withDensityReal (g : Euc d → ℝ) {ρ : Euc d → ℝ} (hm : Measurable ρ)
    (h0 : ∀ x, 0 ≤ ρ x) (x : Euc d) :
    HRS.Whole.convMeasure g (HRS.Whole.withDensityReal ρ) x = HRS.Whole.convFun g ρ x := by
  unfold HRS.Whole.convMeasure HRS.Whole.withDensityReal HRS.Whole.convFun
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  congr 1
  funext y
  rw [ENNReal.toReal_ofReal (h0 y), smul_eq_mul, mul_comm]

/-- [P02b] -/
theorem energyPairing_withDensityReal (g : Euc d → ℝ) {ρ : Euc d → ℝ} (hm : Measurable ρ)
    (h0 : ∀ x, 0 ≤ ρ x) :
    HRS.Whole.energyPairing g (HRS.Whole.withDensityReal ρ) (HRS.Whole.withDensityReal ρ) = energyDens g ρ := by
  unfold HRS.Whole.energyPairing energyDens
  have hinner : ∀ x, ∫ y, g (x - y) ∂(HRS.Whole.withDensityReal ρ)
      = HRS.Whole.convFun g ρ x := fun x => convMeasure_withDensityReal g hm h0 x
  simp only [hinner]
  unfold HRS.Whole.withDensityReal
  rw [integral_withDensity_eq_integral_toReal_smul hm.ennreal_ofReal
    (Filter.Eventually.of_forall fun y => ENNReal.ofReal_lt_top)]
  congr 1
  funext x
  rw [ENNReal.toReal_ofReal (h0 x), smul_eq_mul, mul_comm]

/-- [P02c] `2 F_N = Qform g - g(0)/N` (pure algebra once P02a, P02b are available). -/
theorem modulatedEnergy_eq_Qform (g : Euc d → ℝ) {ρ : Euc d → ℝ} (hρ : HRS.Whole.IsProbDensity ρ)
    (hN : 1 ≤ N) (X : HRS.Whole.EucConfig d N) :
    HRS.Whole.modulatedEnergy g X (HRS.Whole.withDensityReal ρ) = (Qform g X ρ - g 0 / N) / 2 := by
  have hm := hρ.measurable
  have h0 := hρ.nonneg
  have hC : ∑ i, HRS.Whole.convMeasure g (HRS.Whole.withDensityReal ρ) (X i)
      = ∑ i, HRS.Whole.convFun g ρ (X i) :=
    Finset.sum_congr rfl fun i _ => convMeasure_withDensityReal g hm h0 (X i)
  have hE := energyPairing_withDensityReal g hm h0
  have hS : ∀ i, ∑ j ∈ Finset.univ.erase i, g (X i - X j)
      = ∑ j, g (X i - X j) - g 0 := by
    intro i
    rw [Finset.sum_erase_eq_sub (Finset.mem_univ i), sub_self]
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (1 : ℝ) ≤ N := by exact_mod_cast hN
    linarith
  unfold HRS.Whole.modulatedEnergy Qform
  rw [hC, hE]
  simp only [hS, Finset.sum_sub_distrib, Finset.sum_const, Finset.card_univ, Fintype.card_fin,
    nsmul_eq_mul]
  field_simp
  ring

end HRS.MH.CoercLower
