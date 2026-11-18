import HRS.MS.R2GenInitAux23
import HRS.MS.GenPathAux22

/-!
# S10.5 window comparison, packet B10: the identification clause for the window martingale

`s105_ident`: for the `𝒦_T`-valued Itô integral `M` of the window integrand `s105Phi Γ (b+T) q X` (with `Γ = r2WindowFeature`), the coordinate `α` of the
window reconstruction `reconstructPath m T (τ ↦ M(b+τ)) (u)` is a.s. the real Itô integral
`√(2q/N) ∑_{i,a} ∫_0^{b+u} ∂_aU(r,b+u)φ_α(x_i^r) dB_i^a(r)` (copy of `s56_ident` with the Itô horizon `b+T` and the `𝒦` horizon `T`).
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2GenInit

open HRS HRS.Whole HRS.MS.S52 HRS.MP.RdRem HRS.MS.GenPath

variable {d : ℕ}

/-- The window analogue of `IsOrbitFeatureK`: the window feature has no junk values. -/
def S105WinK (C : WholeCoeff d) (m T b : ℝ) (a : Fin d) (r : ℝ) (x : Euc d) : Prop :=
  Memℓp (fun α => gradComp a (propagatorW C r (max b r) (oscTestFun m α)) x) 2 ∧
  Memℓp (fun α => if b ≤ r then gradComp a (oscTestFun m α) x else 0) 2 ∧
  (∀ u ∈ Set.Icc (0 : ℝ) T, r < b + u → Memℓp (fun α => gradComp a (propagatorW C r (b + u)
    (generatorW C (b + u) (oscTestFun m α))) x) 2) ∧
  MemLp (fun u : ℝ => if r < b + u then ellVec (d := d) m (fun α => gradComp a (propagatorW C r (b + u)
    (generatorW C (b + u) (oscTestFun m α))) x) else 0) 2 (volume.restrict (Set.Icc (0 : ℝ) T))

lemma s105_pair_Φ {C : WholeCoeff d} {m T b q : ℝ} {N : ℕ} {Ω : Type*}
    (X : ℝ≥0 → Ω → EucConfig d N) (r : ℝ) (ω : Ω) (k : Fin N × Fin d) (y : KSpace d m T) :
    inner ℝ (s105Phi (fun a r x => r2WindowFeature C m T (gradComp a) b r x) (b + T) q X r ω k) y =
      Real.sqrt (2 * q / N) * inner ℝ (r2WindowFeature C m T (gradComp k.2) b (mrrClamp (b + T) r)
        (X (Real.toNNReal r) ω k.1)) y := by
  unfold s105Phi
  rw [real_inner_smul_left]

theorem s105_ident (C : WholeCoeff d) (m T b q : ℝ) (N : ℕ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (ℱ : Filtration ℝ mΩ) (W : ℝ≥0 → Ω → Fin N × Fin d → ℝ) (X : ℝ≥0 → Ω → EucConfig d N)
    (M : ℝ → Ω → KSpace d m T) (hN : 1 ≤ N) (hb : 0 ≤ b) (hT : 0 ≤ T) (hW : IsCylindricalBrownian P ℱ W)
    (hΦ : ∀ T' : ℝ, IsHSIntegrand P ℱ T' (s105Phi (fun a r x => r2WindowFeature C m T (gradComp a) b r x) (b + T) q X))
    (hM : IsHilbertItoIntegral P ℱ W (s105Phi (fun a r x => r2WindowFeature C m T (gradComp a) b r x) (b + T) q X) M)
    (hC : OscAdjointInput C m (b + T))
    (hK : ∀ (a : Fin d) (r : ℝ), r ∈ Set.Icc (0 : ℝ) (b + T) → ∀ x, S105WinK C m T b a r x) :
    ∀ u ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d, ∀ᵐ ζ ∂P,
      OscDual.coord (reconstructPath m T (fun τ ζ => M (b + τ) ζ) ζ u) α =
        itoIntegral P ℱ W (fun r ζ' ia => if r ∈ Set.Icc (0 : ℝ) (b + u) then Real.sqrt (2 * q / N) *
          gradComp ia.2 (propagatorW C r (b + u) (oscTestFun m α)) (X (Real.toNNReal r) ζ' ia.1) else 0)
          (b + u) ζ := by
  classical
  intro u hu α
  set t : ℝ := b + u with htdef
  have ht0 : 0 ≤ t := by linarith [hu.1]
  have htτ : t ≤ b + T := by linarith [hu.2]
  have hτ : 0 ≤ b + T := by linarith
  have hW' : IsBrownianFiltration P ℱ W := s52_brownian_of_cyl hW
  set Γ : Fin d → ℝ → Euc d → KSpace d m T := fun a r x => r2WindowFeature C m T (gradComp a) b r x with hΓ
  set Φ := s105Phi Γ (b + T) q X with hΦdef
  set c0 : ℝ := Real.sqrt (2 * q / N) with hc0
  set u1 : ℝ → Ω → Fin N × Fin d → ℝ := fun r ω k => inner ℝ (Φ r ω k) (s52y1 m T u α) with hu1
  set u2 : ℝ → Ω → Fin N × Fin d → ℝ := fun r ω k => inner ℝ (Φ r ω k) (s52y2 m T α) with hu2
  have hL1 : IsProgressiveL2 P ℱ u1 := s52_pairL2 hΦ _
  have hL2 : IsProgressiveL2 P ℱ u2 := s52_pairL2 hΦ _
  have hLd : IsProgressiveL2 P ℱ (fun r ω k => u1 r ω k - u2 r ω k) := isProgressiveL2_sub hL1 hL2
  set ud : ℝ → Ω → Fin N × Fin d → ℝ := fun r ω k => u1 r ω k - u2 r ω k with hud
  -- pointwise values of the pairings
  have hu2val : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ ω (k : Fin N × Fin d), u2 r ω k =
      c0 * (if b ≤ r then gradComp k.2 (oscTestFun m α) (X (Real.toNNReal r) ω k.1) else 0) := by
    intro r hr ω k
    simp only [hu2, hΦdef, hc0]
    rw [s105_pair_Φ (C := C) (b := b), mrrClamp_of_mem hr]
    obtain ⟨h1, h2, h3, h4⟩ := hK k.2 r hr (X (Real.toNNReal r) ω k.1)
    rw [s105_pair_y2 C m T b r k.2 _ h1 h2 h4]
  have hu1val : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ ω (k : Fin N × Fin d), u1 r ω k =
      c0 * (if r ≤ t then gradComp k.2 (propagatorW C r t (oscTestFun m α)) (X (Real.toNNReal r) ω k.1)
        else gradComp k.2 (oscTestFun m α) (X (Real.toNNReal r) ω k.1)) := by
    intro r hr ω k
    simp only [hu1, hΦdef, hc0, htdef]
    rw [s105_pair_Φ (C := C) (b := b), mrrClamp_of_mem hr]
    obtain ⟨h1, h2, h3, h4⟩ := hK k.2 r hr (X (Real.toNNReal r) ω k.1)
    rw [s105_pair_y1 C hC hb hr.1 hr.2 hu k.2 _ h1 h3 h4]
  -- the pairings with the Itô integrals
  have hp1T := s52_pair_ito hW' hM (s52y1 m T u α)
    (pc_isProgressiveL2_inner hΦ (s52y1 m T u α) Finset.univ) hτ
  have hp2T := s52_pair_ito hW' hM (s52y2 m T α) (pc_isProgressiveL2_inner hΦ (s52y2 m T α) Finset.univ) hτ
  have hp2t := s52_pair_ito hW' hM (s52y2 m T α) (pc_isProgressiveL2_inner hΦ (s52y2 m T α) Finset.univ) ht0
  have hsub := itoIntegral_sub hW' hL1 hL2
  -- the integral of the difference stops at `t`
  have hagreeE : ∀ r ∈ Set.Icc (0 : ℝ) (b + T), ∀ ω,
      ud r ω = (fun r ω k => if r ≤ t then ud r ω k else 0) r ω := by
    intro r hr ω
    funext k
    by_cases hrt : r ≤ t
    · simp [hrt]
    · have hbr : b ≤ r := by linarith [not_le.1 hrt, hu.1]
      simp only [hrt, if_false, hud, hu2val r hr ω k, hu1val r hr ω k, hbr, if_true]
      simp
  have hLdt : IsProgressiveL2 P ℱ (fun r ω k => if r ≤ t then ud r ω k else 0) := by
    have := s52_isProgressiveL2_ite hLd (measurableSet_Iic (a := t))
    simpa using this
  have hlcE := s52_lc hW' hLd hLdt hτ hagreeE
  have hkillE := s52_kill hW' hLd ht0
  -- the target integrand
  set ψ : ℝ → Ω → Fin N × Fin d → ℝ := fun r ζ' ia => if r ∈ Set.Icc (0 : ℝ) t then Real.sqrt (2 * q / N) *
    gradComp ia.2 (propagatorW C r t (oscTestFun m α)) (X (Real.toNNReal r) ζ' ia.1) else 0 with hψ
  have hψeq : ψ = fun r ω k => if r ∈ Set.Icc (0 : ℝ) t then u1 r ω k else 0 := by
    funext r ω k
    by_cases hr : r ∈ Set.Icc (0 : ℝ) t
    · have hrT : r ∈ Set.Icc (0 : ℝ) (b + T) := ⟨hr.1, hr.2.trans htτ⟩
      simp only [hψ, hr, if_true, hu1val r hrT ω k, hr.2]
      rfl
    · simp only [hψ, if_neg hr]
  have hLψ : IsProgressiveL2 P ℱ ψ := by
    rw [hψeq]; exact s52_isProgressiveL2_ite hL1 measurableSet_Icc
  have hagreeG : ∀ r ∈ Set.Icc (0 : ℝ) t, ∀ ω, u1 r ω = ψ r ω := by
    intro r hr ω
    rw [hψeq]
    simp [hr]
  have hlcG := s52_lc hW' hL1 hLψ ht0 hagreeG
  filter_upwards [hp1T, hp2T, hp2t, hsub, hlcE, hkillE, hlcG] with ζ h1 h2 h3 h4 h5 h6 h7
  have hrec := s52_coord_recon (t := u) hu.1 hu.2 (fun τ ζ => M (b + τ) ζ) ζ α
  rw [hrec]
  have k0a : inner ℝ (M (b + T) ζ) (s52y1 m T u α) = itoIntegral P ℱ W u1 (b + T) ζ := h1
  have k0b : inner ℝ (M (b + T) ζ) (s52y2 m T α) = itoIntegral P ℱ W u2 (b + T) ζ := h2
  have k0c : inner ℝ (M (b + u) ζ) (s52y2 m T α) = itoIntegral P ℱ W u2 t ζ := h3
  have k1 : itoIntegral P ℱ W ud (b + T) ζ = itoIntegral P ℱ W u1 (b + T) ζ - itoIntegral P ℱ W u2 (b + T) ζ := h4 _
  have k2 : itoIntegral P ℱ W ud t ζ = itoIntegral P ℱ W u1 t ζ - itoIntegral P ℱ W u2 t ζ := h4 _
  have k3 : itoIntegral P ℱ W ud (min (b + T) (b + T)) ζ =
      itoIntegral P ℱ W (fun r ω k => if r ≤ t then ud r ω k else 0) (min (b + T) (b + T)) ζ := h5 _ hτ
  have k4 : itoIntegral P ℱ W (fun r ω k => if r ≤ t then ud r ω k else 0) (b + T) ζ =
      itoIntegral P ℱ W ud (min (b + T) t) ζ := h6 _ hτ
  have k5 : itoIntegral P ℱ W u1 (min t t) ζ = itoIntegral P ℱ W ψ (min t t) ζ := h7 t ht0
  rw [min_self] at k3 k5
  rw [min_eq_right htτ] at k4
  rw [k0a, k0b, k0c]
  linarith

end HRS.MS.R2GenInit
