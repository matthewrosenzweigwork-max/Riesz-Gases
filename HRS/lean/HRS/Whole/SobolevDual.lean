import HRS.PDE.ToolboxRd.Defs
import HRS.Prob.Metrics

/-!
# The negative Sobolev space `H^{-Γ}(ℝ^d)` and its pairing with `H^Γ(ℝ^d)`

Source: HRS whole-space supplement (S), Section "Initial fields on the whole space" /
`B:thm:main-rd-field` (S.A.6), `B:lem:iid-init-field-rd` (S.B.2), `B:prop:limit-field` (S.B.7).  The
supplement works in `H = H^{-Γ}(ℝ^d)`, the dual of `H^Γ(ℝ^d)` (`H^Γ,H^{-Γ}` duality pairing, S line
11290 / `B:eq:iid-feature-map`), for an integer `Γ`; the project has no whole-space `H^{-Γ}`.

## Representation decisions

* `HNeg d Γ` is the *Fourier-side model* of `H^{-Γ}(ℝ^d)`, `Γ : ℝ`: the real-linear subspace of
  `L²(ℝ^d, ℂ; (1+4π²|ξ|²)^{-Γ} dξ)` consisting of the classes `F` with the reality condition
  `F(-ξ) = conj F(ξ)`.  An element `F` is the Fourier transform `û` (with Mathlib's convention
  `𝓕u(ξ) = ∫ e^{-2πi⟨x,ξ⟩}u(x) dx`) of a real tempered distribution `u`, and
  `‖F‖² = ∫ |F|² (1+4π²|ξ|²)^{-Γ} dξ = ‖u‖²_{H^{-Γ}}`, with the same weight `(1+4π²|ξ|²)^s` as
  `HRS.PDE.ToolboxRd.sobolevNormSq` (norm of `H^s`).  The subspace is the kernel of the continuous
  real-linear map `F ↦ conj F(-·) - F` (so it is closed and complete, `Hilbert` up to the
  complex-to-real restriction of scalars).
* The duality pairing is `⟨φ, F⟩_{H^Γ,H^{-Γ}} = Re ∫ conj(φ̂(ξ)) F(ξ) dξ` for `φ` a real function
  (`fourierL2 φ` is the Plancherel transform, junk `0` when `φ ∉ L²`; the integral is the genuine
  Parseval pairing for `φ ∈ H^Γ`).  The class of terminal tests is
  `IsSobolevTest Γ φ`: `φ` smooth and in `H^Γ` (a dense subclass of `H^Γ`; smoothness is needed because
  the classical adjoint solution has terminal datum a *function*, never an a.e.-class).
* `H^{-Γ}`-valued random variables are random elements of `HNeg d Γ` (Borel `σ`-algebra).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff ComplexConjugate

namespace HRS.Whole

variable {d : ℕ}

/-- The weight `(1+4π²|ξ|²)^{-Γ}` of the `H^{-Γ}` norm on the Fourier side. -/
def sobolevWeight (d : ℕ) (Γ : ℝ) (ξ : Euc d) : ℝ≥0∞ :=
  ENNReal.ofReal ((1 + 4 * Real.pi ^ 2 * ‖ξ‖ ^ 2) ^ (-Γ))

/-- The measure `(1+4π²|ξ|²)^{-Γ} dξ` on the Fourier side. -/
def sobolevMeasure (d : ℕ) (Γ : ℝ) : Measure (Euc d) :=
  volume.withDensity (sobolevWeight d Γ)

theorem sobolevMeasure_neg (Γ : ℝ) :
    MeasurePreserving (fun ξ : Euc d => -ξ) (sobolevMeasure d Γ) (sobolevMeasure d Γ) := by
  have hm : Measurable (sobolevWeight d Γ) := by
    unfold sobolevWeight
    fun_prop
  refine ⟨measurable_neg, ?_⟩
  unfold sobolevMeasure
  have h1 : (volume : Measure (Euc d)).map (fun ξ => -ξ) = volume := Measure.map_neg_eq_self _
  ext s hs
  rw [Measure.map_apply measurable_neg hs, withDensity_apply _ (measurable_neg hs),
    withDensity_apply _ hs]
  conv_rhs => rw [← h1]
  rw [setLIntegral_map hs hm measurable_neg]
  have h3 : ∀ x : Euc d, sobolevWeight d Γ (-x) = sobolevWeight d Γ x := by
    intro x; simp [sobolevWeight]
  simp_rw [h3]

/-- The real structure `F ↦ conj F(-·)` of the Fourier side. -/
def realStructure (d : ℕ) (Γ : ℝ) :
    Lp ℂ 2 (sobolevMeasure d Γ) →L[ℝ] Lp ℂ 2 (sobolevMeasure d Γ) :=
  ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.compLpL 2 (sobolevMeasure d Γ)) ∘L
    (Lp.compMeasurePreservingₗᵢ (𝕜 := ℝ) (E := ℂ) (p := (2 : ℝ≥0∞))
      (fun ξ : Euc d => -ξ) (sobolevMeasure_neg Γ)).toContinuousLinearMap

/-- The real-linear subspace `{F : conj F(-·) = F}` of `L²(ℂ; (1+4π²|ξ|²)^{-Γ} dξ)`. -/
def HNegSubmodule (d : ℕ) (Γ : ℝ) : Submodule ℝ (Lp ℂ 2 (sobolevMeasure d Γ)) :=
  LinearMap.ker (((realStructure d Γ) -
    ContinuousLinearMap.id ℝ (Lp ℂ 2 (sobolevMeasure d Γ))).toLinearMap)

/-- `H^{-Γ}(ℝ^d)`, `Γ ∈ ℝ`, in its Fourier-side model (see the module docstring). -/
def HNeg (d : ℕ) (Γ : ℝ) : Type := HNegSubmodule d Γ

instance (Γ : ℝ) : NormedAddCommGroup (HNeg d Γ) :=
  inferInstanceAs (NormedAddCommGroup (HNegSubmodule d Γ))

instance (Γ : ℝ) : NormedSpace ℝ (HNeg d Γ) :=
  inferInstanceAs (NormedSpace ℝ (HNegSubmodule d Γ))

instance (Γ : ℝ) : MeasurableSpace (HNeg d Γ) := borel _

instance (Γ : ℝ) : BorelSpace (HNeg d Γ) := ⟨rfl⟩

instance (Γ : ℝ) : CompleteSpace (HNeg d Γ) := by
  have h : IsClosed ((HNegSubmodule d Γ : Set (Lp ℂ 2 (sobolevMeasure d Γ)))) :=
    ContinuousLinearMap.isClosed_ker
      ((realStructure d Γ) - ContinuousLinearMap.id ℝ (Lp ℂ 2 (sobolevMeasure d Γ)))
  exact h.completeSpace_coe

/-- The Fourier transform `û : ℝ^d → ℂ` (an a.e. class) of an element of `H^{-Γ}`. -/
def HNeg.fourier {Γ : ℝ} (F : HNeg d Γ) : Euc d → ℂ :=
  (((F : HNegSubmodule d Γ).1 : Lp ℂ 2 (sobolevMeasure d Γ)) : Euc d → ℂ)

/-- The reality condition `û(-ξ) = conj û(ξ)` of an element of `H^{-Γ}`. -/
theorem HNeg.fourier_conj {Γ : ℝ} (F : HNeg d Γ) :
    ∀ᵐ ξ ∂(sobolevMeasure d Γ), F.fourier (-ξ) = (starRingEnd ℂ) (F.fourier ξ) := by
  set G : Lp ℂ 2 (sobolevMeasure d Γ) := (F : HNegSubmodule d Γ).1 with hG
  have h : realStructure d Γ G = G := by
    have := (F : HNegSubmodule d Γ).2
    simp only [HNegSubmodule, LinearMap.mem_ker] at this
    simpa [sub_eq_zero] using this
  have h1 := Lp.coeFn_compMeasurePreserving G (sobolevMeasure_neg Γ)
  have h2 := ContinuousLinearMap.coeFn_compLpL ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap)
    (Lp.compMeasurePreserving (fun ξ : Euc d => -ξ) (sobolevMeasure_neg Γ) G)
  have h3 : (realStructure d Γ) G =
      ((Complex.conjCLE : ℂ ≃L[ℝ] ℂ).toContinuousLinearMap.compLpL 2 (sobolevMeasure d Γ))
        (Lp.compMeasurePreserving (fun ξ : Euc d => -ξ) (sobolevMeasure_neg Γ) G) := rfl
  have h4 : (G : Euc d → ℂ) =ᵐ[sobolevMeasure d Γ] (realStructure d Γ G : Euc d → ℂ) := by
    rw [h]
  rw [h3] at h4
  filter_upwards [h1, h2, h4] with ξ a b c
  have e : (G : Euc d → ℂ) ξ = (starRingEnd ℂ) ((G : Euc d → ℂ) (-ξ)) := by
    rw [c, b, a]; rfl
  show (G : Euc d → ℂ) (-ξ) = (starRingEnd ℂ) ((G : Euc d → ℂ) ξ)
  rw [e]; simp

/-- The duality pairing `⟨φ, F⟩_{H^Γ,H^{-Γ}} = Re ∫ conj(φ̂(ξ)) F(ξ) dξ` of a real function `φ`
with an element `F ∈ H^{-Γ}` (Parseval; for `φ ∈ H^Γ` the integral converges absolutely by
Cauchy-Schwarz). -/
def HNeg.pairing {Γ : ℝ} (φ : Euc d → ℝ) (F : HNeg d Γ) : ℝ :=
  (∫ ξ, conj (HRS.PDE.ToolboxRd.fourierL2 φ ξ) * F.fourier ξ).re

/-- `‖φ‖_{H^Γ(ℝ^d)} = (∫ (1+4π²|ξ|²)^Γ |φ̂|² dξ)^{1/2}` (junk `0` for `φ ∉ H^Γ`; always used
together with `MemSobolev`). -/
def sobolevNorm (Γ : ℝ) (φ : Euc d → ℝ) : ℝ := Real.sqrt (HRS.PDE.ToolboxRd.sobolevNormSq Γ φ)

/-- A terminal test of the `H^Γ,H^{-Γ}` duality: a smooth function in `H^Γ(ℝ^d)` (a dense class of
`H^Γ`; see the module docstring). -/
def IsSobolevTest (Γ : ℝ) (φ : Euc d → ℝ) : Prop :=
  ContDiff ℝ ∞ φ ∧ HRS.PDE.ToolboxRd.MemSobolev Γ φ

end HRS.Whole
