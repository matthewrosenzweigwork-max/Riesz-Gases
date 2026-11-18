import HRS.MS.R2InterpAux44

/-!
# S10.2 (worker S102), part 45 (packet G6): the projection family `s102_Pj` and the replacement of `γ` outside `[0,T]`
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MC.Sec7.S7PIG6 HRS.MS.CovMeas HRS.Sec7

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

/-- `S102Concl` only sees `γ_u` for `u ∈ [0,T]`. -/
theorem s102_Concl_congr (hT : 0 ≤ T) (s : ℝ) (μ : Measure (Euc d)) {γ γ' : ℝ → Measure (OscPath d m T)}
    (hγ : ∀ u ∈ Icc (0 : ℝ) T, γ u = γ' u) {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω)
    (X : ℝ≥0 → Ω → EucConfig d N) (Φ : OscPath d m T → ℝ) (Pj : OscPath d m T →L[ℝ] OscPath d m T)
    (h : S102Concl C m T s μ γ P X Φ Pj) : S102Concl C m T s μ γ' P X Φ Pj := by
  obtain ⟨A, J, hA, hJ, h1, h2, h3⟩ := h
  have e : ∀ τ ∈ Icc (0 : ℝ) T, ∀ Ψ : OscPath d m T → ℝ, r2HeatFn γ Ψ τ = r2HeatFn γ' Ψ τ := by
    intro τ hτ Ψ
    funext y
    unfold r2HeatFn
    rw [hγ τ hτ]
  refine ⟨A, J, hA, hJ, ?_, ?_, ?_⟩
  · filter_upwards [h1] with ζ h
    refine (s102_isR2RS_iff _ _ _).2 (S7PIG6_IsRS_congr ((s102_isR2RS_iff _ _ _).1 h) fun τ a b hτ _ _ _ => ?_)
    simp only [e τ hτ]
  · filter_upwards [h2] with ζ h
    refine (s102_isR2RS_iff _ _ _).2 (S7PIG6_IsRS_congr ((s102_isR2RS_iff _ _ _).1 h) fun τ a b hτ _ _ _ => ?_)
    simp only [e τ hτ]
  · rw [h3, e 0 ⟨le_rfl, hT⟩]

set_option maxSynthPendingDepth 3 in
/-- **G6**: removal of the projection for the whole-space projection family `s102_Pj`. -/
theorem s102_G6 (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 + 1 < r) (hP : (d : ℝ) < 2 * Pw)
    (hD : S101Data C m T r c) (hlin : S102Lin C m T) (hT : 0 < T) (hν : 0 ≤ C.ν)
    (Mρ : ℝ) (hρint : ∀ u ∈ Icc (0 : ℝ) T, Integrable (C.ρ u))
    (hρnn : ∀ u ∈ Icc (0 : ℝ) T, ∀ x, 0 ≤ C.ρ u x)
    (hρmom : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun x => C.ρ u x * jbracket x ^ (2 * Pw)) ∧
      ∫ x, C.ρ u x * jbracket x ^ (2 * Pw) ≤ Mρ)
    (hG : ∀ L : ℕ, S102GramInt C m hT L)
    (s : ℝ) (μ : Measure (Euc d)) (γ : ℝ → Measure (OscPath d m T))
    (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {N : ℕ} {Ω : Type} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ)
    (Mb : Ω → ℝ → ℝ)
    (hdr : ∀ᵐ ζ ∂P, S102Drift C m T r Pw (fun u => r2QuadField s μ P X u ζ) (Mb ζ))
    (hMint : Integrable (fun ζ => ∫ u in Ioc 0 T, Mb ζ u) P)
    (hY : ∀ᵐ ζ ∂P, ContinuousOn (s102_Y C m T P X ζ) (Icc 0 T))
    (Vf : Ω → ℝ) (hVf : Integrable Vf P)
    (hJc : ∀ᵐ ζ ∂P, ∃ (Jc : ℝ → TensorDual (OscPath d m T) 2), Jc 0 = 0 ∧
      (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IsR2JValue C m T (s102_etaf μ X ζ) (Ioc a b) (Jc b - Jc a)) ∧
      BoundedVariationOn Jc (Icc 0 T) ∧ (eVariationOn Jc (Icc 0 T)).toReal ≤ Vf ζ)
    (hzW : AEMeasurable (fun ζ => zetaPathW m T 0 P X ζ) P)
    (hy : AEMeasurable (fun ζ => s102_y0 C m T P X ζ) P)
    (hF : ∀ L, S102Concl C m T s μ γ P X Φ (s102_Pj T hT L)) :
    S102Concl C m T s μ γ P X Φ (ContinuousLinearMap.id ℝ (OscPath d m T)) := by
  classical
  set γ' : ℝ → Measure (OscPath d m T) := fun u => if u ∈ Icc (0 : ℝ) T then γ u else Measure.dirac 0 with hγ'def
  have hγγ' : ∀ u ∈ Icc (0 : ℝ) T, γ u = γ' u := fun u hu => by
    show γ u = if u ∈ Icc (0 : ℝ) T then γ u else Measure.dirac 0
    rw [if_pos hu]
  have hγ'p : ∀ u, IsProbabilityMeasure (γ' u) := fun u => by
    by_cases hu : u ∈ Icc (0 : ℝ) T
    · have := (hγ u hu).1.1
      rw [← hγγ' u hu]
      exact this.toIsProbabilityMeasure
    · show IsProbabilityMeasure (if u ∈ Icc (0 : ℝ) T then γ u else Measure.dirac 0)
      rw [if_neg hu]
      infer_instance
  have hγ' : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ' u) := fun u hu => by
    rw [← hγγ' u hu]
    exact hγ u hu
  obtain ⟨hP1, hconv, hTconv⟩ := s102_projection_strong (d := d) m T hT
  have hLP : S102LipProj γ' (fun L => s102_Pj T hT L) :=
    s102_lipProj hd hP0 hr hP hD hlin hT hν Mρ hρint hρnn hρmom hG γ' hγ'p hγ'
  have := s102_Concl_congr hT.le s μ (fun u hu => (hγγ' u hu).symm) P X Φ (ContinuousLinearMap.id ℝ (OscPath d m T))
    (s102_G6_core hP hD hlin hT s μ γ' hγ'p P X (fun L => s102_Pj T hT L) hP1 hconv hTconv hLP hΦ Mb hdr hMint hY
      Vf hVf hJc hzW hy (fun L => s102_Concl_congr hT.le s μ hγγ' P X Φ _ (hF L)))
  exact this

end HRS.MS.R2Interp

end
