import HRS.MS.S111K4P5
import HRS.MS.S111K4T3
import HRS.MS.ThCorrSmAux2
import HRS.MS.TransOpAux23
import HRS.MS.S111X2Aux18

/-!
# S11.1 / T03 (S11K4), Pro `R26-T6.E03` and the uniform `C_b²` bounds along a classical orbit
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S111K4

open HRS HRS.Whole

variable {d : ℕ}

/-- Pro `R26-T6.E03` for the thermal reference: smooth representatives of the (unscaled) response of `C_b²` data. -/
theorem k4_resp_rep (hd : 2 ≤ d) (s a β : ℝ) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) (ha : 0 < a) (hβ : 0 < β)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d s a β ρ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ f : Euc d → ℝ, MemCb 2 f → ∃ h : Euc d → ℝ,
      HRS.Whole.IsResponse (HRS.Whole.rieszKernel d s) (HRS.Whole.withDensityReal ρ) β f h ∧
        MemCb 2 h ∧ cbNorm 2 h ≤ C * cbNorm 2 f := by
  have hdr : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hsd : s < d := by linarith
  have hds : 0 < (d : ℝ) - s := by linarith
  set M : ℕ := ⌈(2 + (d : ℝ) / 2) / ((d : ℝ) - s)⌉₊ + 1 with hMdef
  have hM : ((2 : ℕ) : ℝ) + d / 2 < M * ((d : ℝ) - s) := by
    have h1 : (2 + (d : ℝ) / 2) / ((d : ℝ) - s) ≤ ⌈(2 + (d : ℝ) / 2) / ((d : ℝ) - s)⌉₊ := Nat.le_ceil _
    have h2 : (2 + (d : ℝ) / 2) < ((⌈(2 + (d : ℝ) / 2) / ((d : ℝ) - s)⌉₊ : ℝ) + 1) * ((d : ℝ) - s) := by
      have := (div_le_iff₀ hds).1 h1
      nlinarith
    simpa [hMdef] using h2
  set N : ℕ := ⌈(M : ℝ) * ((d : ℝ) - s) + d⌉₊ + 3 with hNdef
  have hN : (M : ℝ) * ((d : ℝ) - s) + d < N := by
    have := Nat.le_ceil ((M : ℝ) * ((d : ℝ) - s) + d)
    rw [hNdef]; push_cast; linarith
  have hmN : 2 ≤ N := by omega
  obtain ⟨c, M₀, m₂, hc, hM₀, hS, -⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd (am := a) (ap := a) (βm := β) (βp := β)
    ha hβ le_rfl le_rfl
  obtain ⟨S, -, hS'⟩ := hS N
  have hρeq : ρ = thermalDensity d s a β := HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρ
  have hTc : HRS.MS.TcDefs.TcRef d ρ M₀ c S N := by
    rw [hρeq]; exact hS' a β le_rfl le_rfl le_rfl le_rfl
  obtain ⟨C, hC0, hC⟩ := HRS.MS.Tc5.tc5_resolvent_rep (d := d) hs0 hsd 2 2 M le_rfl hM β M₀ c S hc N hmN hN
  refine ⟨β⁻¹ * C, by positivity, fun f hf => ?_⟩
  obtain ⟨r₀, r, hr0, hreq, hrc, hrn, hrae⟩ := hC ρ hTc β hβ le_rfl f hf
  haveI := HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  set μ := HRS.Whole.withDensityReal ρ with hμ
  obtain ⟨hsc, hsn⟩ := HRS.MS.Tc5.tc5_cb_smul β⁻¹ hrc
  refine ⟨fun x => β⁻¹ * r x, ⟨?_, ?_⟩, hsc, ?_⟩
  · have hr1 : MemLp r 2 μ := hr0.1.ae_eq hrae.symm
    refine ⟨hr1.const_mul _, ?_⟩
    rw [integral_const_mul, integral_congr_ae hrae, hr0.2, mul_zero]
  · have hkop : ∀ x, HRS.Whole.Kop (rieszKernel d s) μ (fun y => β⁻¹ * r y) x =
        β⁻¹ * HRS.Whole.Kop (rieszKernel d s) μ r₀ x := by
      intro x
      have e1 : HRS.Whole.Kop (rieszKernel d s) μ r = HRS.Whole.Kop (rieszKernel d s) μ r₀ :=
        HRS.MS.S98.s98_kop_congr_ae hrae
      rw [← congrFun e1 x]
      unfold HRS.Whole.Kop HRS.Whole.projMean HRS.Whole.pair
      have e2 : ∀ z : Euc d, (∫ y, rieszKernel d s (z - y) * (β⁻¹ * r y) ∂μ) =
          β⁻¹ * ∫ y, rieszKernel d s (z - y) * r y ∂μ := fun z => by
        rw [← integral_const_mul]
        refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
        simp only
        ring
      simp_rw [e2]
      rw [integral_const_mul]
      ring
    filter_upwards [hreq, hrae] with x h1 h2
    rw [hkop]
    have : r x + β * HRS.Whole.Kop (rieszKernel d s) μ r₀ x = β * HRS.Whole.projMean μ f x := by
      rw [h2]; exact h1
    field_simp
    linarith
  · calc cbNorm 2 (fun x => β⁻¹ * r x) ≤ |β⁻¹| * cbNorm 2 r := hsn
      _ ≤ |β⁻¹| * (C * cbNorm 2 f) := mul_le_mul_of_nonneg_left hrn (abs_nonneg _)
      _ = β⁻¹ * C * cbNorm 2 f := by rw [abs_of_pos (inv_pos.2 hβ)]; ring

end HRS.MS.S111K4
