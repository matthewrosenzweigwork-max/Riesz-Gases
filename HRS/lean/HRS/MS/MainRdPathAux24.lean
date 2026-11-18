import HRS.MS.MainRdPathAux23

/-!
# S.A.9, packet P6b: the identification of the finite-dimensional laws and the assembly of the convergence in law
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff BoundedContinuousFunction

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.HNegInfra HRS.MS.IidInit

variable {d : ℕ} {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {Γ : ℕ}

theorem sa9_toHNegPath_apply {Ω : Type*} {T : ℝ} {q : ℝ} (Y : ℝ → Ω → HNeg d q) {ζ : Ω}
    (hζ : Continuous fun t : Set.Icc (0 : ℝ) T => Y t ζ) (t : Set.Icc (0 : ℝ) T) :
    (toHNegPath q T Y ζ).at' t = Y t ζ := by
  have h : toHNegPath q T Y ζ = ((⟨fun t => Y t ζ, hζ⟩ : C(Set.Icc (0 : ℝ) T, HNeg d q)) :
      HNegPath d q T) := by
    unfold toHNegPath
    exact dif_pos hζ
  rw [h]
  rfl

theorem sa9_assemble (hConc : Sa9Conc S R Γ) {Ω' : Type} [MeasurableSpace Ω'] (P' : Measure Ω')
    [IsProbabilityMeasure P'] (Y : ℝ → Ω' → HNeg d ((Γ + 2 : ℕ) : ℝ))
    (hYc : ∀ᵐ ζ ∂P', Continuous fun t : Set.Icc (0 : ℝ) S.T => Y t ζ)
    (hYm : AEMeasurable (toHNegPath ((Γ + 2 : ℕ) : ℝ) S.T Y) P')
    (hfdd : ∀ (p : ℕ) (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ), (∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) →
      (∀ a, ∃ ψ : SchwartzMap (Euc d) ℝ, ⇑ψ = φ a) →
      HRS.Main.ConvergesInLaw
        (fun N => fluctStatLawRd (R N).P (S.sigma N) (R N).X (S.ρ N) ts φ)
        (law P' (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing (φ a) (Y (ts a) ζ) :
          EuclideanSpace ℝ (Fin p)))))
    (Ξ : ∀ N, (R N).Ω → HNegPath d ((Γ + 2 : ℕ) : ℝ) S.T) (hΞm : ∀ N : ℕ, 1 ≤ N → Measurable (Ξ N))
    (hΞ : ∀ N : ℕ, 1 ≤ N → IsFluctPathRepr S R N (Γ + 2) (Ξ N)) :
    HRS.Main.ConvergesInLaw (fun N => law (R N).P (Ξ N))
      (law P' (toHNegPath ((Γ + 2 : ℕ) : ℝ) S.T Y)) := by
  classical
  let Ξ' : ∀ N, (R N).Ω → C(Set.Icc (0 : ℝ) S.T, HNeg d ((Γ + 2 : ℕ) : ℝ)) := fun N ζ => sa9_toC (Ξ N ζ)
  let Yp : Ω' → C(Set.Icc (0 : ℝ) S.T, HNeg d ((Γ + 2 : ℕ) : ℝ)) :=
    fun ζ => sa9_toC (toHNegPath ((Γ + 2 : ℕ) : ℝ) S.T Y ζ)
  have hΞ'm : ∀ N : ℕ, 1 ≤ N → Measurable (Ξ' N) := fun N hN => hΞm N hN
  have hYp : AEMeasurable Yp P' := hYm
  have htight' : IsTightMeasureSet {μ | ∃ N : ℕ, 2 ≤ N ∧ μ = (R N).P.map (Ξ' N)} := hConc.2 Ξ hΞ
  show HRS.Main.ConvergesInLaw (fun N => law (R N).P (Ξ' N)) (law P' Yp)
  refine (HRS.Main.A9.a9_conv_shift 2).2 ?_
  have hμ : ∀ n : ℕ, IsProbabilityMeasure (law (R (n + 2)).P (Ξ' (n + 2))) := fun n => by
    unfold law; infer_instance
  have hμ' : IsProbabilityMeasure (law P' Yp) := by
    unfold law; infer_instance
  refine @sa9_path_conv_sch d (Γ + 2) S.T (fun n => law (R (n + 2)).P (Ξ' (n + 2))) hμ
    (law P' Yp) hμ' ?_ fun p g h => ?_
  · refine htight'.subset ?_
    rintro _ ⟨n, rfl⟩
    exact ⟨n + 2, by omega, rfl⟩
  · have hfdc : Continuous (sa27_fd (sa27_pathF S.T (sa9_pfS d (Γ + 2))) g) :=
      sa27_fd_continuous _ (sa27_pathF_continuous S.T (sa9_pfS d (Γ + 2)) (sa9_pfS_continuous (Γ + 2))) g
    have hL : ∀ n : ℕ, ((law (R (n + 2)).P (Ξ' (n + 2))).map (sa27_fd (sa27_pathF S.T (sa9_pfS d (Γ + 2))) g)) =
        fluctStatLawRd (R (n + 2)).P (S.sigma (n + 2)) (R (n + 2)).X (S.ρ (n + 2))
          (fun a => ((g a).1 : ℝ)) (fun a => (g a).2.1) := by
      intro n
      unfold law
      rw [Measure.map_map hfdc.measurable (hΞ'm (n + 2) (by omega))]
      unfold fluctStatLawRd law
      refine Measure.map_congr ?_
      have hall0 := fun a : Fin p => hΞ (n + 2) (by omega) (g a).1 ((g a).2.1)
        (sa9_sch_test (Γ + 2) (g a).2)
      have hall := ae_all_iff.2 hall0
      filter_upwards [hall] with ζ hζ
      ext a
      simp only [sa27_fd, sa27_pathF, sa9_pfS, fluctStatRd, Function.comp, Ξ', sa9_toC]
      exact hζ a
    have hR : (law P' Yp).map (sa27_fd (sa27_pathF S.T (sa9_pfS d (Γ + 2))) g) =
        law P' (fun ζ => (WithLp.toLp 2 fun a => HNeg.pairing ((g a).2.1) (Y ((g a).1 : ℝ) ζ) :
          EuclideanSpace ℝ (Fin p))) := by
      unfold law
      rw [AEMeasurable.map_map_of_aemeasurable hfdc.measurable.aemeasurable hYp]
      refine Measure.map_congr ?_
      filter_upwards [hYc] with ζ hζ
      ext a
      simp only [sa27_fd, sa27_pathF, sa9_pfS, Function.comp, Yp, sa9_toC]
      exact congrArg _ (sa9_toHNegPath_apply Y hζ (g a).1)
    have hconv : Tendsto (fun n : ℕ => ∫ y, h y ∂(fluctStatLawRd (R (n + 2)).P (S.sigma (n + 2))
          (R (n + 2)).X (S.ρ (n + 2)) (fun a => ((g a).1 : ℝ)) (fun a => (g a).2.1))) atTop
        (𝓝 (∫ y, h y ∂(law P' (fun ζ => (WithLp.toLp 2 fun a =>
          HNeg.pairing ((g a).2.1) (Y ((g a).1 : ℝ) ζ) : EuclideanSpace ℝ (Fin p)))))) :=
      (HRS.Main.A9.a9_conv_shift 2).1
        (hfdd p (fun a => ((g a).1 : ℝ)) (fun a => (g a).2.1) (fun a => (g a).1.2)
          (fun a => (g a).2.2)) h
    simp only [hL, hR]
    exact hconv

end HRS.MS.MainRdPath
