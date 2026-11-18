import HRS.MS.GenPathAux21
import HRS.MS.OrbIdTie

/-!
# S5.6 packet P6a: identification clause for the clamped integrand; classical adjoint solutions of oscillator data
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.GenPath

open HRS HRS.Whole HRS.MS.S52 HRS.MP.RdRem

variable {d : ℕ}

lemma s56_pair_Φ {C : WholeCoeff d} {m T q : ℝ} {N : ℕ} {Ω : Type*}
    (X : ℝ≥0 → Ω → EucConfig d N) (r : ℝ) (ω : Ω) (k : Fin N × Fin d) (y : KSpace d m T) :
    inner ℝ (s56Phi C m T q X r ω k) y =
      Real.sqrt (2 * q / N) * inner ℝ (gradFeature C m T k.2 (mrrClamp T r) (X (Real.toNNReal r) ω k.1)) y := by
  unfold s56Phi
  rw [real_inner_smul_left]

/-- Identification clause of Lemma S5.2 for the clamped integrand `s56Phi` (copy of `orbit_maximal_identification_allhorizon`). -/
theorem s56_ident (C : WholeCoeff d) (m T q : ℝ) (N : ℕ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin N × Fin d → ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (M : ℝ → Ω → KSpace d m T) (hN : 1 ≤ N) (hW : IsCylindricalBrownian P ℱ W)
    (hΦ : ∀ T' : ℝ, IsHSIntegrand P ℱ T' (s56Phi C m T q X))
    (hM : IsHilbertItoIntegral P ℱ W (s56Phi C m T q X) M)
    (hC : OscAdjointInput C m T) :
    ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ᵐ ζ ∂P,
      OscDual.coord (reconstructPath m T M ζ t) α =
        itoIntegral P ℱ W (fun r ζ' ia => if r ∈ Set.Icc (0 : ℝ) t then Real.sqrt (2 * q / N) *
          gradComp ia.2 (propagatorW C r t (oscTestFun m α)) (X (Real.toNNReal r) ζ' ia.1) else 0) t ζ := by
  classical
  intro t ht α
  have hT : 0 ≤ T := ht.1.trans ht.2
  have hW' : IsBrownianFiltration P ℱ W := s52_brownian_of_cyl hW
  set Φ := s56Phi C m T q X with hΦdef
  set c0 : ℝ := Real.sqrt (2 * q / N) with hc0
  set u1 : ℝ → Ω → Fin N × Fin d → ℝ := fun r ω k => inner ℝ (Φ r ω k) (s52y1 m T t α) with hu1
  set u2 : ℝ → Ω → Fin N × Fin d → ℝ := fun r ω k => inner ℝ (Φ r ω k) (s52y2 m T α) with hu2
  have hL1 : IsProgressiveL2 P ℱ u1 := s52_pairL2 hΦ _
  have hL2 : IsProgressiveL2 P ℱ u2 := s52_pairL2 hΦ _
  have hLd : IsProgressiveL2 P ℱ (fun r ω k => u1 r ω k - u2 r ω k) := isProgressiveL2_sub hL1 hL2
  set ud : ℝ → Ω → Fin N × Fin d → ℝ := fun r ω k => u1 r ω k - u2 r ω k with hud
  -- pointwise values of the pairings
  have hu2val : ∀ r ω (k : Fin N × Fin d), u2 r ω k =
      c0 * gradComp k.2 (oscTestFun m α) (X (Real.toNNReal r) ω k.1) := by
    intro r ω k
    simp only [hu2, hΦdef, hc0]
    rw [s56_pair_Φ, s52_pair_grad_y2 hC hT]
  have hu1val : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ ω (k : Fin N × Fin d), u1 r ω k =
      c0 * (if r ≤ t then gradComp k.2 (propagatorW C r t (oscTestFun m α))
        (X (Real.toNNReal r) ω k.1) else gradComp k.2 (oscTestFun m α) (X (Real.toNNReal r) ω k.1)) := by
    intro r hr ω k
    simp only [hu1, hΦdef, hc0]
    rw [s56_pair_Φ, mrrClamp_of_mem hr, s52_pair_grad_y1 hC ht.2 k.2 hr]
  -- the pairings with the Itô integrals
  have hp1T := s52_pair_ito hW' hM (s52y1 m T t α)
    (pc_isProgressiveL2_inner hΦ (s52y1 m T t α) Finset.univ) hT
  have hp2T := s52_pair_ito hW' hM (s52y2 m T α) (pc_isProgressiveL2_inner hΦ (s52y2 m T α) Finset.univ) hT
  have hp2t := s52_pair_ito hW' hM (s52y2 m T α) (pc_isProgressiveL2_inner hΦ (s52y2 m T α) Finset.univ) ht.1
  have hsub := itoIntegral_sub hW' hL1 hL2
  -- the integral of the difference stops at `t`
  have hagreeE : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ ω, ud r ω = (fun r ω k => if r ≤ t then ud r ω k else 0) r ω := by
    intro r hr ω
    funext k
    by_cases hrt : r ≤ t
    · simp [hrt]
    · simp only [hrt, if_false, hud, hu2val r ω k, hu1val r hr ω k]
      simp
  have hLdt : IsProgressiveL2 P ℱ (fun r ω k => if r ≤ t then ud r ω k else 0) := by
    have := s52_isProgressiveL2_ite hLd (measurableSet_Iic (a := t))
    simpa using this
  have hlcE := s52_lc hW' hLd hLdt hT hagreeE
  have hkillE := s52_kill hW' hLd ht.1
  -- the target integrand
  set ψ : ℝ → Ω → Fin N × Fin d → ℝ := fun r ζ' ia => if r ∈ Set.Icc (0 : ℝ) t then Real.sqrt (2 * q / N) *
    gradComp ia.2 (propagatorW C r t (oscTestFun m α)) (X (Real.toNNReal r) ζ' ia.1) else 0 with hψ
  have hψeq : ψ = fun r ω k => if r ∈ Set.Icc (0 : ℝ) t then u1 r ω k else 0 := by
    funext r ω k
    by_cases hr : r ∈ Set.Icc (0 : ℝ) t
    · have hrT : r ∈ Set.Icc (0 : ℝ) T := ⟨hr.1, hr.2.trans ht.2⟩
      simp only [hψ, hr, if_true, hu1val r hrT ω k, hr.2]
      rfl
    · simp only [hψ, if_neg hr]
  have hLψ : IsProgressiveL2 P ℱ ψ := by
    rw [hψeq]; exact s52_isProgressiveL2_ite hL1 measurableSet_Icc
  have hagreeG : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ ω, u1 r ω = ψ r ω := by
    intro r hr ω
    rw [hψeq]
    simp [hr]
  have hlcG := s52_lc hW' hL1 hLψ ht.1 hagreeG
  filter_upwards [hp1T, hp2T, hp2t, hsub, hlcE, hkillE, hlcG] with ζ h1 h2 h3 h4 h5 h6 h7
  rw [s52_coord_recon ht.1 ht.2]
  have k0a : inner ℝ (M T ζ) (s52y1 m T t α) = itoIntegral P ℱ W u1 T ζ := h1
  have k0b : inner ℝ (M T ζ) (s52y2 m T α) = itoIntegral P ℱ W u2 T ζ := h2
  have k0c : inner ℝ (M t ζ) (s52y2 m T α) = itoIntegral P ℱ W u2 t ζ := h3
  have k1 : itoIntegral P ℱ W ud T ζ = itoIntegral P ℱ W u1 T ζ - itoIntegral P ℱ W u2 T ζ := h4 T
  have k2 : itoIntegral P ℱ W ud t ζ = itoIntegral P ℱ W u1 t ζ - itoIntegral P ℱ W u2 t ζ := h4 t
  have k3 : itoIntegral P ℱ W ud (min T T) ζ =
      itoIntegral P ℱ W (fun r ω k => if r ≤ t then ud r ω k else 0) (min T T) ζ := h5 T hT
  have k4 : itoIntegral P ℱ W (fun r ω k => if r ≤ t then ud r ω k else 0) T ζ =
      itoIntegral P ℱ W ud (min T t) ζ := h6 T hT
  have k5 : itoIntegral P ℱ W u1 (min t t) ζ = itoIntegral P ℱ W ψ (min t t) ζ := h7 t ht.1
  rw [min_self] at k3 k5
  rw [min_eq_right ht.2] at k4
  rw [k0a, k0b, k0c]
  linarith



end HRS.MS.GenPath
