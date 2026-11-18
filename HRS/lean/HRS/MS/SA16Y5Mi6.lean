import HRS.MS.SA16Y5Mi5

/-!
# S.A.16 (SA16Y5) Mi6: the level-`m` energy bound for the fractional-order Duhamel solution (B8, part 6)

`sa16y5f_energy`: with `Bf r = sa16so_B d (m+1) p (bc r)` (`SA16DerCoef`/`SA16BddCoef` coefficients) and the dissipativity
`d(jetEnergy_m)_{ι²G}(-N_r G) ≤ cNl jetEnergy_m(ι²G)` of the fractional operator (`N_r : W^{m+2} → W^m`), the mild solution satisfies
`jetEnergy_m(ι² u τ) ≤ jetEnergy_m(ι² φ) e^{(p cTr + cNl) τ}` (via `sa16y3_energy_strongD`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16V2

section Mi6
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

set_option maxHeartbeats 3200000 in
theorem sa16y5f_energy {m : ℕ} {ν T B B' BB BN CN cNl γ : ℝ} (hν : 0 < ν) (hT : 0 < T) (hγ : 1 / 2 ≤ γ) (hγ1 : γ < 1)
    (bc : ℝ → Fin d → Euc d → ℝ) (hbc : ∀ r ∈ Icc (0 : ℝ) T, SA16DerCoef (m + 1) B (bc r))
    (hbo : ∀ r ∈ Icc (0 : ℝ) T, SA16BddCoef (m + 1) B' (bc r))
    (Bf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d (m + 1) p)
    (hBf : ∀ r, Bf r = sa16so_B d (m + 1) p (bc r))
    (hBb : ∀ r ∈ Icc (0 : ℝ) T, ‖Bf r‖ ≤ BB)
    (hBc : ∀ x, ContinuousOn (fun r => Bf r x) (Icc 0 T))
    (Nf : ℝ → WmpSpace d (m + 1 + 1) p →L[ℝ] WmpSpace d m p)
    (hNb : ∀ r ∈ Icc (0 : ℝ) T, ‖Nf r‖ ≤ BN)
    (hNc : ∀ x, ContinuousOn (fun r => Nf r x) (Icc 0 T))
    (hsharp : ∀ r ∈ Icc (0 : ℝ) T, ∀ s ∈ Ioc (0 : ℝ) T, ‖sa16y5_Qh d m p (ν * s) (Nf r)‖ ≤ CN * s ^ (-γ))
    (hiota : ∀ r ∈ Icc (0 : ℝ) T, ∀ a : ℝ, 0 < a → ∀ x : WmpSpace d (m + 1 + 1) p,
      sa16r_iota d (m + 1) p (sa16y5_Qh d m p a (Nf r) x) = sa16r_Gam d m p a (Nf r x))
    (hN : ∀ r ∈ Icc (0 : ℝ) T, ∀ G : WmpSpace d (m + 1 + 1) p,
      fderiv ℝ (jetEnergy d m p) (sa16sz_iota2 d m p G) (-(Nf r G)) ≤ cNl * jetEnergy d m p (sa16sz_iota2 d m p G))
    (φ : WmpSpace d (m + 1 + 1) p) {u : ℝ → WmpSpace d (m + 1 + 1) p} (hu : ContinuousOn u (Icc 0 T))
    (hsol : ∀ τ ∈ Icc (0 : ℝ) T, u τ = sa16r_f0 d (m + 1) p ν φ τ +
      voltOp (fun τ s => sa16y5f_kernel d m p ν Bf Nf s (τ - s)) u τ) :
    ∀ τ ∈ Icc (0 : ℝ) T, jetEnergy d m p (sa16sz_iota2 d m p (u τ)) ≤
      jetEnergy d m p (sa16sz_iota2 d m p φ) * Real.exp ((p * sa16sz_cTr d m p B + cNl) * τ) := by
  have hder : ∀ τ ∈ Ioo (0 : ℝ) T, HasDerivAt (fun r => sa16sz_iota2 d m p (u r))
      (ν • sa16so_Lap d m p (u τ) + sa16r_iota d m p (sa16so_B d (m + 1) p (bc τ) (u τ)) -
        (fun r G => Nf r G) τ (u τ)) τ := by
    intro τ hτ
    have := sa16y5f_hasDerivAt hν hT hγ hγ1 Bf hBb hBc Nf hNb hNc hsharp hiota φ hu hsol hτ
    unfold sa16y5f_f at this
    rw [hBf τ] at this
    exact this
  have key := sa16y3_energy_strongD (m := m) (ν := ν) (T := T) (B := B) (B' := B') (cNl := cNl) hν.le bc
    (fun r hr => hbc r ⟨hr.1.le, hr.2.le⟩) (fun r hr => hbo r ⟨hr.1.le, hr.2.le⟩) (fun r G => Nf r G)
    (fun r hr G => hN r ⟨hr.1.le, hr.2.le⟩ G) hu hder
  intro τ hτ
  have h0 := sa16y5f_strong hν hT hγ hγ1 Bf hBb hBc Nf hNb hNc hsharp hiota φ hu hsol 0 ⟨le_rfl, hT.le⟩
  have hu0 : sa16sz_iota2 d m p (u 0) = sa16sz_iota2 d m p φ := by
    simp only [intervalIntegral.integral_same, add_zero] at h0
    unfold sa16sz_iota2
    simp only [ContinuousLinearMap.comp_apply]
    exact h0
  have := key τ hτ
  rwa [hu0] at this

end Mi6

end HRS.Whole.AppendixA.Phase2SA16R
