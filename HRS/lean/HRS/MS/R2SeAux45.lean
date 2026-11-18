import HRS.MS.R2SeAux44

/-!
# S9.9 `r2_static_edgeworth`, packet 45: linearity of the response and the vector `ℓ_x ∈ B_m`

Worker S99, namespace `S99`.

* `s99_resp_smul`: `a_{cψ} = c a_ψ` pointwise (uniqueness of the response, `s98_resp_unique`);
* `s99_ell_eq`: `ℓ_x = r2EllPt x = Ψ⁻¹ (ellv x)` for the isometry `Ψ : B_m ≃ ℓ²` of an enumeration `e` of the multi-indices and
  `φ_j = oscTestFun m (e j)`;
* bounds and continuity of `x ↦ ℓ_x`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section Smul

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) {a β γ : ℝ} (ha : 0 < a) (hβ : 0 < β) (hγ : 0 < γ)

include hd hs0 hsd ha hβ hγ

theorem s99_resp_smul {ψ : Euc d → ℝ} (hψ : MemCb (J1 d) ψ) (c : ℝ) (x : Euc d) :
    responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ (fun y => c * ψ y) x =
      c * responseRepW (rieszKernel d s) (thermalMeasure d s a β) γ ψ x := by
  obtain ⟨c₀, M₀, m₂, hc₀, hM₀, hU, -⟩ := HRS.MS.Tc6.tc6_unif hd hs0 hsd (am := a) (ap := a) (βm := β)
    (βp := β) ha hβ le_rfl le_rfl
  obtain ⟨S, hS0, hSρ⟩ := hU 0
  have hTc := hSρ a β le_rfl le_rfl le_rfl le_rfl
  have hmem : ∀ i : ℕ, MemCb (J1 d) (if i = 0 then ψ else fun y => c * ψ y) := fun i => by
    by_cases hi : i = 0
    · simp only [hi, if_true]; exact hψ
    · simp only [hi, if_false]; exact (HRS.MS.Tc5.tc5_cb_smul c hψ).1
  obtain ⟨F'⟩ := s99_famData hd hs0 hsd ha hβ hγ (φ := fun i : ℕ => if i = 0 then ψ else fun y => c * ψ y) hmem
  have r0 := F'.resp 0
  have r1 := F'.resp 1
  have a0 := F'.amem 0
  have a1 := F'.amem 1
  simp only [if_true, if_false, one_ne_zero] at r0 r1 a0 a1
  have hc : IsResponse (rieszKernel d s) (thermalMeasure d s a β) γ (fun y => c * ψ y)
      (fun y => c * aRep d s a β γ ψ y) := by
    refine ⟨⟨r0.1.1.const_mul c, by rw [integral_const_mul, r0.1.2, mul_zero]⟩, ?_⟩
    filter_upwards [r0.2] with y hy
    have h1 := HRS.MS.S98.s98_kop_smul (rieszKernel d s) (thermalMeasure d s a β) c (aRep d s a β γ ψ) y
    have h2 : projMean (thermalMeasure d s a β) (fun y => c * ψ y) y =
        c * projMean (thermalMeasure d s a β) ψ y := by
      unfold projMean pair
      rw [integral_const_mul]; ring
    rw [h1, h2, ← hy]; ring
  have hae := HRS.MS.S98.s98_resp_unique (by omega : 1 ≤ d) hs0 hsd hc₀ hTc hγ r1 hc
  have hvol : ∀ᵐ y ∂(volume : Measure (Euc d)), aRep d s a β γ (fun y => c * ψ y) y =
      c * aRep d s a β γ ψ y := by
    have hmeas : Measurable fun x => ENNReal.ofReal (thermalDensity d s a β x) :=
      ENNReal.measurable_ofReal.comp hTc.smooth.continuous.measurable
    have := (ae_withDensity_iff hmeas).1 hae
    filter_upwards [this] with y hy
    exact hy (by simpa using hTc.pos y)
  exact congrFun ((Continuous.ae_eq_iff_eq (volume : Measure (Euc d)) a1.1.continuous
    (continuous_const.mul a0.1.continuous)).1 hvol) x

end Smul

end S99

end
