import HRS.MS.R2SeAux31

/-!
# S9.9 `r2_static_edgeworth`, packet 32: the potentials of the response functions

Worker S99, namespace `S99`.  For the thermal reference `μ = ρ dx`, `a_j = responseRepW φ_j`, `G_j(x) = ∫ g(x-y) a_j(y) dμ(y)`:

* `s99_conv_cont`: `x ↦ ∫ g(x-y) r(y) dμ(y)` is continuous for bounded continuous `r` (copy of `s98_conv_continuous`);
* `s99_resp_all`: the response equation `a_j + γ K_μ a_j = P_μ φ_j` holds at every `x` (not only `μ`-a.e.);
* `s99_Gpot_eq`: `G_j = c_j + γ⁻¹ (φ_j - a_j)`; in particular `G_j` is `C¹`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

/-- The potential `G_j`. -/
def Gpot (d : ℕ) (s a β : ℝ) (ψ : Euc d → ℝ) (x : Euc d) : ℝ :=
  ∫ y, rieszKernel d s (x - y) * ψ y ∂(thermalMeasure d s a β)

section PotA

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β C c BU : ℝ} (hT : ThermalData d s a β C c BU)

include hd hs0 hsd hT

theorem s99_conv_cont {r : Euc d → ℝ} (hr : Continuous r) {B : ℝ} (hB : ∀ x, |r x| ≤ B) :
    Continuous (Gpot d s a β r) := by
  have hρc : Continuous (thermalDensity d s a β) := hT.smooth.continuous
  have hB0 : 0 ≤ B := (abs_nonneg _).trans (hB 0)
  have e : Gpot d s a β r = fun x => ∫ z, rieszKernel d s z * (thermalDensity d s a β (x - z) * r (x - z)) := by
    funext x
    unfold Gpot
    show ∫ y, rieszKernel d s (x - y) * r y ∂(withDensityReal (thermalDensity d s a β)) = _
    rw [HRS.MS.S98.s98_integral_wDR _ hρc.measurable (fun y => (hT.pos y).le)]
    have := integral_sub_left_eq_self (fun z => rieszKernel d s z * (thermalDensity d s a β (x - z) * r (x - z)))
      (volume : Measure (Euc d)) x
    rw [← this]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    simp only [sub_sub_cancel]
    ring
  rw [e]
  obtain ⟨hk, hB', hBint⟩ := HRS.MS.MovForce.mv1_g_data (d := d) (s := s) (by omega) hs0 hsd hT.hc
  refine HRS.MS.MovForce.mv1_continuous_conv (ρ := fun y => thermalDensity d s a β y * r y) hT.hc hk hB' hBint
    (C := C * B) (mul_nonneg hT.C0 hB0) (hρc.mul hr) (fun y => ?_)
  rw [abs_mul, abs_of_pos (hT.pos y)]
  calc thermalDensity d s a β y * |r y| ≤ (C * Real.exp (-c * ‖y‖ ^ 2)) * B :=
        mul_le_mul (by simpa [abs_of_pos (hT.pos y)] using hT.h0 y) (hB y) (abs_nonneg _)
          (mul_nonneg hT.C0 (Real.exp_pos _).le)
    _ = C * B * Real.exp (-c * ‖y‖ ^ 2) := by ring

end PotA

section PotB

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hφ F

/-- The response equation holds everywhere. -/
theorem s99_resp_all (j : ℕ) (x : Euc d) :
    aRep d s a β γ (φ j) x + γ * Kop (rieszKernel d s) (thermalMeasure d s a β) (aRep d s a β γ (φ j)) x =
      projMean (thermalMeasure d s a β) (φ j) x := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  set μ := thermalMeasure d s a β with hμdef
  have ha1 : Continuous (aRep d s a β γ (φ j)) := (F.amem j).1.continuous
  have hab : ∀ x, |aRep d s a β γ (φ j) x| ≤ cbNorm (k0 d) (aRep d s a β γ (φ j)) := fun x => by
    have h1 := s99_norm_iter_le_cb (F.amem j) (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
  have hKc : Continuous (Kop (rieszKernel d s) μ (aRep d s a β γ (φ j))) := by
    have := s99_conv_cont hd hs0 hsd hT ha1 hab
    unfold Kop projMean
    exact this.sub continuous_const
  have hφc : Continuous (φ j) := (hφ.1 j).1.continuous
  have hPc : Continuous (projMean μ (φ j)) := by
    unfold projMean
    exact hφc.sub continuous_const
  have hae := (F.resp j).2
  have hvol : ∀ᵐ x ∂(volume : Measure (Euc d)), aRep d s a β γ (φ j) x +
      γ * Kop (rieszKernel d s) μ (aRep d s a β γ (φ j)) x = projMean μ (φ j) x := by
    have hmeas : Measurable fun x => ENNReal.ofReal (thermalDensity d s a β x) :=
      ENNReal.measurable_ofReal.comp hT.smooth.continuous.measurable
    have := (ae_withDensity_iff hmeas).1 hae
    filter_upwards [this] with x hx
    exact hx (by simpa using hT.pos x)
  have hcont : Continuous fun x => aRep d s a β γ (φ j) x +
      γ * Kop (rieszKernel d s) μ (aRep d s a β γ (φ j)) x := ha1.add (continuous_const.mul hKc)
  exact congrFun ((Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) hcont hPc).1 hvol) x

/-- `G_j = c_j + γ⁻¹ (φ_j - a_j)`. -/
theorem s99_Gpot_eq (j : ℕ) : ∃ c0 : ℝ, ∀ x, Gpot d s a β (aRep d s a β γ (φ j)) x =
    c0 + γ⁻¹ * (φ j x - aRep d s a β γ (φ j) x) := by
  refine ⟨pair (thermalMeasure d s a β) (Gpot d s a β (aRep d s a β γ (φ j))) -
    γ⁻¹ * pair (thermalMeasure d s a β) (φ j), fun x => ?_⟩
  have h := s99_resp_all hd hs0 hs ha hβ hγ hT hφ F j x
  have h' : aRep d s a β γ (φ j) x + γ * (Gpot d s a β (aRep d s a β γ (φ j)) x -
      pair (thermalMeasure d s a β) (Gpot d s a β (aRep d s a β γ (φ j)))) =
      φ j x - pair (thermalMeasure d s a β) (φ j) := h
  have hγ0 : γ ≠ 0 := hγ.ne'
  have : γ⁻¹ * (γ * (Gpot d s a β (aRep d s a β γ (φ j)) x -
      pair (thermalMeasure d s a β) (Gpot d s a β (aRep d s a β γ (φ j))))) =
      γ⁻¹ * (φ j x - pair (thermalMeasure d s a β) (φ j) - aRep d s a β γ (φ j) x) := by
    congr 1; linarith
  rw [← mul_assoc, inv_mul_cancel₀ hγ0, one_mul] at this
  linarith [this]

end PotB

end S99

end
