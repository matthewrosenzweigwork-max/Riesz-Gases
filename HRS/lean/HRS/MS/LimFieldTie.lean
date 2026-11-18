import HRS.MS.LimFieldAux2
import HRS.Whole.AppendixBField

/-!
# SB7: proofs of the statements of S.B.7 (`limit_field_rd_duality`, `limit_field_rd_weak_form`)

The declarations `HRS.Whole.limit_field_rd_duality` and `HRS.Whole.limit_field_rd_weak_form`
(`HRS/Whole/AppendixBField.lean`) carry the S.B.7 repairs approved (2026-10-22): the extra hypotheses
listed below.  The theorems proved here have exactly the types of these (edited) statements; the `example`s
below check this by `type_of%` ties (`limit_field_rd_weak_form` and the uniqueness half are tied as whole
statements, the existence half as the first conjunct).  The proofs are in `HRS/MS/LimFieldAux1.lean` (noise
process, existence) and `HRS/MS/LimFieldAux2.lean` (uniqueness and weak form).

## `limit_field_rd_duality`

* (a) existence: proved exactly as stated (`sb7_limit_field_rd_duality_exists` has the frozen type, checked by
  the `example` below).  Construction: `Y_t = I^t + G_t` on the product extension `Ω × Ω₀`, `I^t` from
  `HasTransportedField`, `G_t = √(2q) ∫_0^t K^{r,t} dW_r` the `H^{-Γ}`-valued version (Hilbert-Schmidt image of
  an isonormal process, `sb7_isonormal_hs`) with the covariance `noiseCovW`.  No measurability of `η₀` is
  needed (the independence is proved for an arbitrary function of the first factor).
* (b) uniqueness in law: the originally frozen statement was false as written, because of a junk value.  `law P η` is
  `Measure.map η P`, and for a map that is not `AEMeasurable` this is an arbitrary fixed Dirac mass (the same
  one for every non-measurable `η`).  `IsAdjointDualityLimitW` only constrains the values
  `η (propagatorW C 0 t φ)`, so two initial functionals with different laws at those values and a
  non-measurable coordinate elsewhere satisfy `law P₁ η₁ = law P₂ η₂` while the laws of `Y` differ.  The
  repair recorded in `docs/ISSUES.md` (AE-measurability of the initial functional, as `Orbits.lean:506`) is
  used: `sb7_limit_field_rd_duality_unique` has the two extra hypotheses `AEMeasurable η₁ P₁` and
  `AEMeasurable η₂ P₂`, and is otherwise the frozen statement.

## `limit_field_rd_weak_form`

`sb7_limit_field_rd_weak_form` is the statement with the following extra hypotheses (now part of the edited
`limit_field_rd_weak_form`).  The
mathematical proof (duality identity, Duhamel identity `hduh` with `s = 0` and `s = w`, linearity and
orbit-continuity of `η₀`, an `L²`-closure argument for the Gaussian family) needs, besides the frozen ones:

* `hT : 0 ≤ T`.  For `T < 0` no time lies in `[0,T]`, the duality identity is empty and the clause `init` of
  `IsWeakLimitSPDEW` (a statement at time `0`) is false in general.
* `hη₀m : Measurable η₀`.  The same junk-value trap as in the uniqueness half: for a non-measurable `η₀` the
  independence and law clauses can fail (and `IndepFun`/`law` of vectors containing `η₀(ϑ)` are junk).
* `hbd`: the bound that was in `hduh` is `∃ B, ∀ r ∈ [s,t], ...` with `B` depending on `s` (it is replaced by `hbd` in the
  edited statement, and the proof re-derives the old conjunct from `hbd`); the `L²` bound
  `E g_r² ≤ 2qTB²` of the noise integrand (hence the integrability of the time integral) needs `B` uniform
  in `s ≤ r ≤ T`.  This is the uniform bound of the TeX Duhamel formula (the proof of S L10763-10768), only
  its quantifier order differs.
* `hΛm`, `hgm`: joint measurability of the Duhamel gradient integrand `(r,w,x) ↦ ∇U^{w,r}(𝓛_rϑ)(x)` (cut off
  to `0 ≤ w ≤ r ≤ T`, `sb7_Lam3`) and of the noise integrand
  `(r,ζ) ↦ ⟨𝓛_rϑ, Y^r⟩ - A η₀(U^{0,r} 𝓛_rϑ)` (cut off to `r ∈ [0,T]`, `sb7_g`).  They are what the docstring of
  the frozen statement calls "joint measurability, so that `r ↦ ⟨𝓛_rϑ,η^r⟩` is measurable": `hYm` alone does
  not give them, since neither `r ↦ 𝓛_rϑ` nor `r ↦ η₀(U^{0,r}𝓛_rϑ)` is assumed measurable.

`hη` and `hYm` of the statement are not needed by the proof (kept so that the argument list agrees).
-/

noncomputable section

open MeasureTheory ProbabilityTheory

namespace HRS.MS.U10

open HRS HRS.Whole

variable {d : ℕ}

/-- Existence half of `limit_field_rd_duality`, with the frozen type. -/
theorem sb7_limit_field_rd_duality_exists (Γ : ℝ) (C : WholeCoeff d) (A q T B : ℝ) (hq : 0 ≤ q)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ))
    (Kern : ℝ → ℝ → Euc d → Fin d → HNeg d Γ) (hK : IsIntrinsicKernel Γ C T B Kern) :
    ∀ {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
      (η₀ : Ω → (Euc d → ℝ) → ℝ), HasTransportedField P C Γ A T η₀ →
      ∃ (Ω' : Type) (_ : MeasurableSpace Ω') (P' : Measure Ω') (_ : IsProbabilityMeasure P')
        (π : Ω' → Ω) (Y : ℝ → Ω' → HNeg d Γ),
        MeasurePreserving π P' P ∧ IsAdjointDualityLimitW P' C Γ A q T (fun ζ' => η₀ (π ζ')) Y :=
  fun {_} _ P _ η₀ hη => sb7_duality_exists hq hρ hρm hK P η₀ hη

/-- Uniqueness half of `limit_field_rd_duality` (S.B.7(iii)(b)), with the extra hypotheses
`AEMeasurable η₁ P₁`, `AEMeasurable η₂ P₂` (see the module docstring). -/
theorem sb7_limit_field_rd_duality_unique (Γ : ℝ) (C : WholeCoeff d) (A q T : ℝ) :
    ∀ {Ω₁ Ω₂ : Type} [MeasurableSpace Ω₁] [MeasurableSpace Ω₂] (P₁ : Measure Ω₁)
      (P₂ : Measure Ω₂) [IsProbabilityMeasure P₁] [IsProbabilityMeasure P₂]
      (η₁ : Ω₁ → (Euc d → ℝ) → ℝ) (η₂ : Ω₂ → (Euc d → ℝ) → ℝ)
      (Y₁ : ℝ → Ω₁ → HNeg d Γ) (Y₂ : ℝ → Ω₂ → HNeg d Γ),
      AEMeasurable η₁ P₁ → AEMeasurable η₂ P₂ →
      law P₁ η₁ = law P₂ η₂ →
      IsAdjointDualityLimitW P₁ C Γ A q T η₁ Y₁ → IsAdjointDualityLimitW P₂ C Γ A q T η₂ Y₂ →
      ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ),
        (∀ a, ts a ∈ Set.Icc (0 : ℝ) T) → (∀ a, IsSobolevTest Γ (φ a)) →
        law P₁ (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (φ a) (Y₁ (ts a) ζ) :
            EuclideanSpace ℝ (Fin p))) =
          law P₂ (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (φ a) (Y₂ (ts a) ζ) :
            EuclideanSpace ℝ (Fin p))) :=
  fun {_ _} _ _ P₁ P₂ _ _ η₁ η₂ Y₁ Y₂ h₁ h₂ hl hY₁ hY₂ =>
    sb7_duality_unique P₁ P₂ η₁ η₂ Y₁ Y₂ h₁ h₂ hl hY₁ hY₂

/-- The existence half has exactly the frozen type (the first conjunct of the frozen statement). -/
example (Γ : ℝ) (C : WholeCoeff d) (A q T B : ℝ) (hq : 0 ≤ q)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ))
    (Kern : ℝ → ℝ → Euc d → Fin d → HNeg d Γ) (hK : IsIntrinsicKernel Γ C T B Kern) :
    type_of% (@sb7_limit_field_rd_duality_exists d Γ C A q T B hq hρ hρm Kern hK) :=
  (HRS.Whole.limit_field_rd_duality Γ C A q T B hq hρ hρm Kern hK).1

/-- Proposition S.B.7(iii), last sentence: the adjoint-duality solution solves the weak equation.  The
frozen statement `HRS.Whole.limit_field_rd_weak_form` with the extra hypotheses `hT`, `hbd`, `hΛm`,
`hη₀m`, `hgm` (see the module docstring). -/
theorem sb7_limit_field_rd_weak_form (Γ : ℝ) (C : WholeCoeff d) (A q T K : ℝ) (hq : 0 ≤ q)
    (hT : 0 ≤ T) (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ))
    (hU : AdjointInputOne Γ C T K)
    (hduh : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → ∀ s t : ℝ, 0 ≤ s → s ≤ t → t ≤ T →
      ∀ x, propagatorW C s t ϑ x - ϑ x = ∫ r in Set.Icc s t, propagatorW C s r (generatorW C r ϑ) x ∧
        gradient (propagatorW C s t ϑ) x - gradient ϑ x =
          ∫ r in Set.Icc s t, gradient (propagatorW C s r (generatorW C r ϑ)) x)
    (hbd : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → ∃ B : ℝ, ∀ s r : ℝ, 0 ≤ s → s ≤ r → r ≤ T →
      ∀ x, ‖gradient (propagatorW C s r (generatorW C r ϑ)) x‖ ≤ B)
    (hΛm : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → Measurable (sb7_Lam3 C T ϑ))
    {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (η₀ : Ω → (Euc d → ℝ) → ℝ) (hη : HasTransportedField P C Γ A T η₀)
    (hη₀m : Measurable η₀) (hlin : IsLinearOnCb1 P η₀)
    (horbit : ∀ᵐ ζ ∂P, ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → ∀ t ∈ Set.Icc (0 : ℝ) T,
      IntegrableOn (fun r => η₀ ζ (propagatorW C 0 r (generatorW C r ϑ))) (Set.Icc (0 : ℝ) t) ∧
      η₀ ζ (fun x => ∫ r in Set.Icc (0 : ℝ) t, propagatorW C 0 r (generatorW C r ϑ) x) =
        ∫ r in Set.Icc (0 : ℝ) t, η₀ ζ (propagatorW C 0 r (generatorW C r ϑ)))
    (Y : ℝ → Ω → HNeg d Γ) (hYm : Measurable (fun p : ℝ × Ω => Y p.1 p.2))
    (hgm : ∀ ϑ : Euc d → ℝ, IsWeakTestFn Γ C T ϑ → Measurable (sb7_g C A T η₀ Y ϑ)) :
    IsAdjointDualityLimitW P C Γ A q T η₀ Y → IsWeakLimitSPDEW P C Γ A q T η₀ Y :=
  fun hdual => sb7_weak_form_main hq hT hρ hρm hU
    (fun ϑ hϑ s t hs hst ht =>
      ⟨(hbd ϑ hϑ).imp fun B hB r hr x => hB s r hs hr.1 (hr.2.trans ht) x, hduh ϑ hϑ s t hs hst ht⟩)
    hbd hΛm hη₀m hlin horbit hgm hdual

/-- The uniqueness half has exactly the type of the edited (S.B.7 repair) second conjunct of
`HRS.Whole.limit_field_rd_duality`. -/
example (Γ : ℝ) (C : WholeCoeff d) (A q T B : ℝ) (hq : 0 ≤ q)
    (hρ : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.Whole.IsProbDensity (C.ρ r))
    (hρm : Measurable (Function.uncurry C.ρ))
    (Kern : ℝ → ℝ → Euc d → Fin d → HNeg d Γ) (hK : IsIntrinsicKernel Γ C T B Kern) :
    type_of% (@sb7_limit_field_rd_duality_unique d Γ C A q T) :=
  (HRS.Whole.limit_field_rd_duality Γ C A q T B hq hρ hρm Kern hK).2

/-- The weak form has exactly the type of the edited `HRS.Whole.limit_field_rd_weak_form`. -/
example : type_of% (@sb7_limit_field_rd_weak_form) := @HRS.Whole.limit_field_rd_weak_form

end HRS.MS.U10
