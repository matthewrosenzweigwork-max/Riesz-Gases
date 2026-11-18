import HRS.Sections.AdjKDAux2

/-!
# ADJKD, part 3: tight + finite-dimensional convergence ⇒ convergence in law (packet F)
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.AdjK

open HRS.Uniform

variable {d : ℕ}

theorem adjkd_convergence_of_tight_fidi (m T : ℝ) (hT : 0 ≤ T)
    {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)] (P : ∀ n, Measure (Ω n))
    [∀ n, IsProbabilityMeasure (P n)] (Φ : ∀ n, Ω n → PathSpace d m T)
    {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    (Ψ : Ω' → PathSpace d m T) (hΦ : ∀ n, AEMeasurable (Φ n) (P n)) (hΨ : AEMeasurable Ψ P')
    (htight : IsTightMeasureSet (Set.range fun n => (P n).map (Φ n)))
    (hfidi : ∀ (p : ℕ) (ts : Fin p → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) T)
      (φ : Fin p → Torus d → ℝ), (∀ a, Torus.IsSmooth (φ a)) →
      TendstoInDistribution
        (fun n ω => (WithLp.toLp 2 fun a => NegSobolev.eval ((Φ n ω).at' ⟨ts a, hts a⟩) (φ a) :
          EuclideanSpace ℝ (Fin p)))
        atTop
        (fun ω' => (WithLp.toLp 2 fun a => NegSobolev.eval ((Ψ ω').at' ⟨ts a, hts a⟩) (φ a) :
          EuclideanSpace ℝ (Fin p)))
        P P') :
    TendstoInDistribution Φ atTop Ψ P P' := by
  classical
  let ν : ℕ → ProbabilityMeasure (PathSpace d m T) := fun n => ⟨(P n).map (Φ n), inferInstance⟩
  let ν' : ProbabilityMeasure (PathSpace d m T) := ⟨P'.map Ψ, inferInstance⟩
  have hcomp : IsCompact (closure (Set.range ν)) := by
    apply isCompact_closure_of_isTightMeasureSet
    refine htight.subset ?_
    rintro _ ⟨_, ⟨n, rfl⟩, rfl⟩
    exact ⟨n, rfl⟩
  refine ⟨hΦ, hΨ, ?_⟩
  refine hcomp.tendsto_nhds_of_unique_mapClusterPt
    (Eventually.of_forall fun n => subset_closure ⟨n, rfl⟩) ?_
  intro μ _ hμ
  have hext : (μ : Measure (PathSpace d m T)) = P'.map Ψ := by
    refine adjkd_ext_of_fidi _ _ fun p ts φ hφ => ?_
    have hG := adjkdG_continuous (m := m) ts φ hφ
    have h1 := (hfidi p (fun a => (ts a).1) (fun a => (ts a).2) φ hφ).tendsto
    have h2 : MapClusterPt (ProbabilityMeasure.map μ (adjkdG (m := m) ts φ)) atTop
        (fun n => ProbabilityMeasure.map (ν n) (adjkdG (m := m) ts φ)) :=
      hμ.continuousAt_comp (f := fun κ : ProbabilityMeasure (PathSpace d m T) =>
        ProbabilityMeasure.map κ (adjkdG (m := m) ts φ))
        (ProbabilityMeasure.continuous_map hG).continuousAt
    have hseq : (fun n => ProbabilityMeasure.map (ν n) (adjkdG (m := m) ts φ)) =
        fun n => (⟨(P n).map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval
          ((Φ n ω).at' ⟨(ts a).1, (ts a).2⟩) (φ a) : EuclideanSpace ℝ (Fin p))),
          inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin p))) := by
      funext n
      apply Subtype.ext
      show ((P n).map (Φ n)).map (adjkdG ts φ) = _
      exact AEMeasurable.map_map_of_aemeasurable hG.measurable.aemeasurable (hΦ n)
    have hlim : ProbabilityMeasure.map ν' (adjkdG (m := m) ts φ) =
        ⟨P'.map (fun ω' => (WithLp.toLp 2 fun a => NegSobolev.eval
          ((Ψ ω').at' ⟨(ts a).1, (ts a).2⟩) (φ a) : EuclideanSpace ℝ (Fin p))), inferInstance⟩ := by
      apply Subtype.ext
      show (P'.map Ψ).map (adjkdG ts φ) = _
      exact AEMeasurable.map_map_of_aemeasurable hG.measurable.aemeasurable hΨ
    rw [hseq] at h2
    have h3 : MapClusterPt (ProbabilityMeasure.map μ (adjkdG (m := m) ts φ)) atTop
        (fun n => (⟨(P n).map (fun ω => (WithLp.toLp 2 fun a => NegSobolev.eval
          ((Φ n ω).at' ⟨(ts a).1, (ts a).2⟩) (φ a) : EuclideanSpace ℝ (Fin p))),
          inferInstance⟩ : ProbabilityMeasure (EuclideanSpace ℝ (Fin p)))) := h2
    have h4 : ProbabilityMeasure.map μ (adjkdG (m := m) ts φ) = _ :=
      eq_of_nhds_neBot (ClusterPt.mono h3 h1)
    have h5 : ProbabilityMeasure.map μ (adjkdG (m := m) ts φ) =
        ProbabilityMeasure.map ν' (adjkdG (m := m) ts φ) := by
      rw [hlim]; exact h4
    have h6 := congrArg (fun κ : ProbabilityMeasure (EuclideanSpace ℝ (Fin p)) =>
      (κ : Measure (EuclideanSpace ℝ (Fin p)))) h5
    exact h6
  exact Subtype.ext hext

end HRS.AdjK
