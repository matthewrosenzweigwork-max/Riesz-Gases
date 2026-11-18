import HRS.MS.MainRdPathAux6

/-!
# S.A.9, packets P1 and P4: the path representatives and the tightness of their laws

* `sa9_rep_ae_eq`: every `IsFluctPathRepr` representative is a.s. the continuous path of the bundle field `Z`;
* `sa9_pathRepr_exists`: part (a) of `RdPathConclusion` (existence of a measurable path representative);
* `sa9_tight_reps`: given fixed-time tightness of `Z`, the laws of all measurable path representatives, `N ≥ 2`,
  form a tight family in `C([0,T]; H^{-q})`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MS.MainRdField HRS.MH.DualityRd HRS.MP.RdGen HRS.MP.KC

/-- A path in `HNegPath` as a continuous map. -/
abbrev sa9_toC {d : ℕ} {Γ T : ℝ} (w : HNegPath d Γ T) : C(Set.Icc (0 : ℝ) T, HNeg d Γ) := w

variable {d : ℕ} {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {Γ : ℕ}

theorem sa9_rep_ae_eq (B : Sa9Bundle S R Γ) {N : ℕ} (hN : 1 ≤ N)
    (Ξ : (R N).Ω → HNegPath d ((Γ + 2 : ℕ) : ℝ) S.T) (hΞ : IsFluctPathRepr S R N (Γ + 2) Ξ) :
    ∀ᵐ ζ ∂(R N).P, sa9_toC (Ξ ζ) =
      contPathOf S.T (fun t => B.Z N t ζ) := by
  obtain ⟨Ξc, hΞcm, hΞc, hΞce⟩ := sa9_pathRepr (T := S.T) (R N).P (B.Z N) (B.hZm N hN) (B.hZc N hN)
  have h1 := sa9_path_ae_eq (q := Γ + 2) (R N).P (fun ζ => sa9_toC (Ξ ζ)) Ξc (fun t φ hφ => by
      filter_upwards [hΞ t φ hφ, hΞc t] with ζ h1 h2
      have : HNegPath.at' (Ξ ζ) t = sa9_toC (Ξ ζ) t := rfl
      rw [← this, h1, h2, B.hZp N hN t.1 t.2 ζ φ hφ])
  filter_upwards [h1, hΞce] with ζ a b
  rw [a, b]

theorem sa9_pathRepr_exists (B : Sa9Bundle S R Γ) {N : ℕ} (hN : 1 ≤ N) :
    ∃ Ξ : (R N).Ω → HNegPath d ((Γ + 2 : ℕ) : ℝ) S.T, Measurable Ξ ∧ IsFluctPathRepr S R N (Γ + 2) Ξ := by
  obtain ⟨Ξc, hΞcm, hΞc, -⟩ := sa9_pathRepr (T := S.T) (R N).P (B.Z N) (B.hZm N hN) (B.hZc N hN)
  refine ⟨Ξc, hΞcm, fun t φ hφ => ?_⟩
  filter_upwards [hΞc t] with ζ h
  have : HNegPath.at' (show HNegPath d ((Γ + 2 : ℕ) : ℝ) S.T from Ξc ζ) t = Ξc ζ t := rfl
  rw [this, h, B.hZp N hN t.1 t.2 ζ φ hφ]

theorem sa9_tight_reps {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ} {C₁ m₂ K' : ℝ} {e : ℕ → ℝ}
    (B : Sa9Bundle S R Γ)
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 5) (Γ + 5) C₀ 𝔈) (hΛ : 1 ≤ Λ)
    (hm₂ : PropagatedSecondMoment S R m₂)
    (hker : ∀ N : ℕ, 1 ≤ N → KernelBoundRd (S.coeff N) S.T (Γ + 2) C₁)
    (he : ∀ N, 0 ≤ e N) (hsel : SelectedCommutatorInput S (Γ : ℝ) S.T K' C₀ Λ e)
    (hsmall : Tendsto (fun N => S.sigma N * (𝔈 N + e N)) atTop (𝓝 0))
    (hfix : ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (R N).P.map (B.Z N t)})
    (Ξ : ∀ N, (R N).Ω → HNegPath d ((Γ + 2 : ℕ) : ℝ) S.T)
    (hΞ : ∀ N : ℕ, 1 ≤ N → IsFluctPathRepr S R N (Γ + 2) (Ξ N)) :
    IsTightMeasureSet {μ | ∃ N : ℕ, 2 ≤ N ∧ μ = (R N).P.map (Ξ N)} := by
  have h := sa9_tight_of_fix hS hΛ hm₂ hker he hsel hsmall B.Z B.Iq B.Mq B.Rm B.ℱ B.W' B.hfilt B.hMq
    B.hRm B.hdec B.hZm B.hZc B.Ic B.hIc hfix
  refine h.subset ?_
  rintro _ ⟨N, hN, rfl⟩
  exact ⟨N, hN, Measure.map_congr (sa9_rep_ae_eq B (by omega) (Ξ N) (hΞ N (by omega)))⟩

end HRS.MS.MainRdPath
