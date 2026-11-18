import HRS.MP.SelfSimP4Mol
import HRS.MP.SelfSimP4Kern
import HRS.MP.SelfSimP4Gibbs
import HRS.MP.SelfSimP4Reg
import HRS.MP.SelfSimP4Flow
import HRS.MP.SelfSimP4Jensen
import HRS.MP.SelfSimP4MolLsc
import HRS.MP.SelfSimP4LscM
import HRS.MP.SelfSimP4Level
import HRS.MP.SelfSimP4Limit

/-!
# S.A.28, packet P4: the self-similar entropy inequality for a collision-free solution

The assembly of `HRS.MP.SelfSimP4Spec.ss_P4_entropy_free_proof` with each interface lemma replaced by its proof.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.SelfSim HRS HRS.MP.SelfSimP4
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MP.SelfSimP4Final

variable {d : ℕ}

/-- **P4**, assembled from (1)-(10) (statement verbatim from `HRS.MP.SelfSim.ss_P4_entropy_free`). -/
theorem ss_P4_entropy_free_final (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (N : ℕ)
    (hN : 2 ≤ N) (invβ : ℝ) (hβ : 0 < invβ) (S : ℝ) (hS : 0 < S)
    {Ω : Type*} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ} {W : ℝ≥0 → Ω → (Fin N → Euc d)}
    {Y : ℝ≥0 → Ω → EucConfig d N}
    (hY : SSAddSol P invβ (ssDrift d s N) S ℱ W' W Y) (hnc : SSNoCollision P S Y)
    (hH0 : gibbsEntropyW (selfSimWeight d s invβ N 0) (law P (Y 0)) < ⊤) :
    SSEntropyIneq d s invβ N S P Y := by
  obtain ⟨gM, hgM⟩ := HRS.MP.SelfSimP4Impl.p4_kernel_proof (N := N) hd s hs0
  obtain ⟨YM, hYM, hYM0, htv⟩ := HRS.MP.SelfSimP4Impl.p4_regularised_flow_proof s invβ hβ hS P hY hnc (fun M => (hgM M).1)
  have hYm : ∀ t, Measurable (Y t) := fun t => (hY.filtered.adapted t).mono (ℱ.le t) le_rfl
  have hμp : ∀ r : ℝ, IsProbabilityMeasure (law P (Y (Real.toNNReal r))) := fun r =>
    (Measure.isProbabilityMeasure_map_iff (hYm _).aemeasurable).2 inferInstance
  have hμ0 : IsProbabilityMeasure (law P (Y 0)) := (Measure.isProbabilityMeasure_map_iff (hYm _).aemeasurable).2 inferInstance
  have hlaw0 : ∀ M, law P (YM M (Real.toNNReal 0)) = law P (Y 0) := fun M => by
    rw [Real.toNNReal_zero]
    exact congrArg (law P) (funext (hYM0 M))
  have hG : ∀ M τ, _ := fun M τ => HRS.MP.SelfSimP4Impl.p4_gibbs_proof hd s hs0 N invβ hβ τ (hgM M).1
  have hm0 : ∫⁻ x, ENNReal.ofReal (‖x‖ ^ 2) ∂(law P (Y 0)) < ⊤ := (((hG 0 0).2.2 (law P (Y 0))).2 hH0)
  -- the level-`M` dissipation inequality, with a measurable majorant of the Fisher information
  have hlev : ∀ M, ∃ D : ℝ → ℝ≥0∞, AEMeasurable D (volume.restrict (Set.Icc (0 : ℝ) S)) ∧
      (∀ r ∈ Set.Icc (0 : ℝ) S, fisherInfoW (p4GibbsOf invβ (p4Pot (gM M) s N r))
        (law P (YM M (Real.toNNReal r))) ≤ D r) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) S,
        gibbsEntropyW (p4GibbsOf invβ (p4Pot (gM M) s N t)) (law P (YM M (Real.toNNReal t))) +
          ((ENNReal.ofReal invβ * ∫⁻ r in Set.Icc (0 : ℝ) t, D r : ℝ≥0∞) : EReal) ≤
        gibbsEntropyW (p4GibbsOf invβ (p4Pot (gM M) s N 0)) (law P (YM M (Real.toNNReal 0))) := by
    intro M
    have hV := (hgM M).2 S hS.le
    have hF : P4FlowHyp invβ (p4Drift (gM M) s N) S (fun r => law P (YM M (Real.toNNReal r))) :=
      HRS.MP.SelfSimP4Impl.p4_flow_hyp_proof P hβ.le hS hV.cont_b hV.lip (hYM M) (by
        have e : law P (YM M 0) = law P (Y 0) := congrArg (law P) (funext (hYM0 M))
        rw [e]; exact hm0)
    obtain ⟨C, h5⟩ := HRS.MP.SelfSimP4Mol.p4_mollified_ineq_proof hβ hS.le hV hF
    have hFp := hF.prob
    have hfin0 : gibbsEntropyW (p4GibbsOf invβ (p4Pot (gM M) s N 0))
        (law P (YM M (Real.toNNReal 0))) < ⊤ := by
      rw [hlaw0 M]
      exact lt_of_le_of_lt (((hG M 0).2.2 (law P (Y 0))).1) hH0
    have : IsProbabilityMeasure (law P (YM M (Real.toNNReal 0))) := hF.prob 0
    obtain ⟨e, he, hinit⟩ := HRS.MP.SelfSimP4Impl.p4_initial_jensen_proof hβ hS.le hV hfin0
    obtain ⟨Cm, hCm, hmom⟩ := hF.mom
    have hv : ∀ n : ℕ, 0 < 1 / ((n : ℝ) + 1) := fun n => by positivity
    have hv0 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝 0) :=
      tendsto_one_div_add_atTop_nhds_zero_nat
    have h7 : ∀ t ∈ Set.Icc (0 : ℝ) S, _ := fun t ht => by
      have : IsProbabilityMeasure (law P (YM M (Real.toNNReal t))) := hF.prob t
      exact HRS.MP.SelfSimP4Impl.p4_mollify_lsc_proof hβ hS.le hV ht (lt_of_le_of_lt (hmom t ht) hCm) hv hv0
    exact HRS.MP.SelfSimP4Impl.p4_level_bookkeeping_proof (θ := invβ) (T := S) (C := C)
      (F := fun v t => p4Free invβ (p4Pot (gM M) s N t) (p4Mol v (law P (YM M (Real.toNNReal t)))))
      (Dv := fun v r => p4Diss invβ (p4Pot (gM M) s N r) (p4Mol v (law P (YM M (Real.toNNReal r)))))
      (H := fun t => gibbsEntropyW (p4GibbsOf invβ (p4Pot (gM M) s N t)) (law P (YM M (Real.toNNReal t))))
      (I := fun r => fisherInfoW (p4GibbsOf invβ (p4Pot (gM M) s N r)) (law P (YM M (Real.toNNReal r))))
      hβ (fun v hv => (h5 v hv).1) (fun v hv => (h5 v hv).2) he hinit
      (fun t ht => (h7 t ht).1) (fun r hr => (h7 r hr).2)
  choose D hDm hDI hDE using hlev
  -- `M → ∞`
  refine HRS.MP.SelfSimP4Impl.p4_limit_bookkeeping_proof (θ := invβ) (S := S)
    (H := fun τ => gibbsEntropyW (selfSimWeight d s invβ N τ) (law P (Y (Real.toNNReal τ))))
    (HM := fun M τ => gibbsEntropyW (p4GibbsOf invβ (p4Pot (gM M) s N τ)) (law P (YM M (Real.toNNReal τ))))
    (I := fun r => fisherInfoW (selfSimWeight d s invβ N r) (law P (Y (Real.toNNReal r))))
    (D := D) (R := gibbsEntropyW (selfSimWeight d s invβ N 0) (law P (Y 0))) hDm ?_ ?_ ?_
  · intro τ hτ
    have : ∀ M, IsProbabilityMeasure (law P (YM M (Real.toNNReal τ))) := fun M =>
      (Measure.isProbabilityMeasure_map_iff (((hYM M).filtered.adapted _).mono (ℱ.le _) le_rfl).aemeasurable).2 inferInstance
    exact (HRS.MP.SelfSimP4Impl.p4_lsc_M_proof hd s hs0 N invβ hβ τ (fun M => (hgM M).1) (htv τ hτ)).1
  · intro r hr
    have : ∀ M, IsProbabilityMeasure (law P (YM M (Real.toNNReal r))) := fun M =>
      (Measure.isProbabilityMeasure_map_iff (((hYM M).filtered.adapted _).mono (ℱ.le _) le_rfl).aemeasurable).2 inferInstance
    refine ((HRS.MP.SelfSimP4Impl.p4_lsc_M_proof hd s hs0 N invβ hβ r (fun M => (hgM M).1) (htv r hr)).2).trans ?_
    exact liminf_le_liminf (Eventually.of_forall fun M => hDI M r hr)
  · intro M τ hτ
    refine (hDE M τ hτ).trans ?_
    rw [hlaw0 M]
    exact ((hG M 0).2.2 (law P (Y 0))).1

example := (@ss_P4_entropy_free_final : type_of% @HRS.MP.SelfSim.ss_P4_entropy_free)

end HRS.MP.SelfSimP4Final
