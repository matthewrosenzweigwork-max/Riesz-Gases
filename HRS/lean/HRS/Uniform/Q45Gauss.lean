import HRS.Uniform.Q07cAux10

/-!
# Q45 (Lemma 3.20): existence of a Gaussian Hilbert martingale with prescribed deterministic covariance density
-/

noncomputable section

open HRS HRS.MRep
open MeasureTheory Filter Topology HRS.HilbertCLTAux ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q45

open HRS.Uniform.Q07c

open Classical

variable {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

/-- A continuous Hilbert martingale, `G_0 = 0`, with deterministic covariance density `Db` on `[0,T]`, on a
probability space in `Type`. -/
theorem exists_gaussian_martingale (T : ℝ) (hT : 0 ≤ T) (Db : ℝ → H →L[ℝ] H →L[ℝ] ℝ)
    (hDb : IsDetCovDensity T Db) :
    ∃ (Ω : Type) (mΩ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (ℱ : Filtration ℝ mΩ) (G : ℝ → Ω → H),
      (∀ ω, Continuous fun τ => G τ ω) ∧ (∀ ω, G 0 ω = 0) ∧
      IsHilbertMartingaleWithCovariation P ℱ T G (fun r _ => if r ≤ T then Db r else 0) := by
  obtain ⟨ιe, hι, e, -⟩ := exists_hilbertBasis_ulift.{_, 0} (H := H)
  haveI := hι
  obtain ⟨Sb, hSbm, hSb0, hSb⟩ := exists_sqrt_density e T Db hDb
  obtain ⟨Tf, hD⟩ := pc_detData e T Db hDb hSbm hSb0 hSb
  have hSbHS := hD.summable_of
  set P : Measure (ιe → WienerSeq) := wMeasure ιe with hPdef
  set ℱ := wFiltration ιe with hℱdef
  have hB : IsCylindricalBrownian P ℱ (fun t (ω : ιe → WienerSeq) (i : ιe) => wienerPath t (ω i)) :=
    fun F => isBrownianFiltration_wFiltration F
  obtain ⟨Gb, hGI, hGJ⟩ := pc_exists_G hD hB
  have hZG : ∀ S, IsHSIntegrand P ℱ S
      (fun r (_ : ιe → WienerSeq) (j : ιe) => if r ≤ T then Sb r (e j) else 0) :=
    fun S => hD.hsInt P ℱ S
  have hNJG : ∀ x : H, ∃ J : ℝ → (ιe → WienerSeq) → ℝ,
      IsItoC P ℱ (fun t ω j => wienerPath t (ω j))
        (fun r (_ : ιe → WienerSeq) (j : ιe) => inner ℝ (if r ≤ T then Sb r (e j) else 0) x) J ∧
      ∀ τ, 0 ≤ τ → (fun ω => inner ℝ (Gb τ ω) x) =ᵐ[P] J τ := by
    intro x
    obtain ⟨J, hJ, hae⟩ := hGJ x
    refine ⟨J, ?_, hae⟩
    have : (fun r (_ : ιe → WienerSeq) (j : ιe) =>
        inner ℝ (if r ≤ T then Sb r (e j) else (0 : H)) x) = fSb e T Sb x := by
      funext r ω j; by_cases h : r ≤ T <;> simp [fSb, h]
    rw [this]; exact hJ
  have hGHM := isHM_of_ito hB hZG hGI.cont hGI.adapted hGI.zero hNJG T
  have hcovG : ∀ r : ℝ, 0 ≤ r → hsCovForm (fun j => if r ≤ T then Sb r (e j) else (0 : H)) =
      if r ≤ T then Db r else 0 := by
    intro r hr0
    by_cases hr : r ≤ T
    · simp only [hr, ite_true]
      exact hsCovForm_sqrt_cols e (hSb r ⟨hr0, hr⟩) (hSbHS r)
    · have h0 : Sb r = 0 := hSb0 r (fun h => hr h.2)
      simp only [hr, ite_false]
      refine ContinuousLinearMap.ext fun x => ContinuousLinearMap.ext fun y => ?_
      rw [hsCovForm_apply (by simpa using (summable_zero : Summable fun _ : ιe => (0 : ℝ)))]
      simp
  have hGfinal : IsHilbertMartingaleWithCovariation P ℱ T Gb
      (fun r _ => if r ≤ T then Db r else 0) := by
    refine hGHM.mono_congr hT le_rfl (fun x y => ?_) (fun σ x y => measurable_const) ?_
    · have : (Function.uncurry fun σ (ω : ιe → WienerSeq) =>
          (fun r (_ : ιe → WienerSeq) => if r ≤ T then Db r else 0) σ ω x y) =
          fun p => if p.1 ≤ T then Db p.1 x y else 0 := by
        funext p; by_cases h : p.1 ≤ T <;> simp [Function.uncurry, h]
      rw [this]
      exact Measurable.ite (measurableSet_le measurable_fst measurable_const)
        ((hDb.meas x y).comp measurable_fst) measurable_const
    · intro r hr ω
      exact (hcovG r hr).symm
  haveI : IsProbabilityMeasure P := inferInstance
  exact ⟨ιe → WienerSeq, inferInstance, P, inferInstance, ℱ, Gb, hGI.cont,
    fun ω => hGI.zero 0 le_rfl ω, hGfinal⟩

end HRS.Uniform.Q45
