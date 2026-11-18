import HRS.MS.SA12X3C6
import HRS.MS.SA12BuildC18
import HRS.MS.SA12BuildC21
import HRS.MH.ScreenedF1

/-!
# S.A.12 C7 (SA12X3), part A: the periodic near identity on moving cells, with uniform geometry

For the advected cutoff `η = χ̂_{c0}^τ` and every `x` with `χ_{c0}^τ(x) ≠ 0`, `periodic_near_identity` (C21) applies with the
period box centred at `Ψ_τ c0`, radius `R' = R+1` (R35), separation `h = 4 e^{-CF T}` (`flow_lip_sep_proof`) and the
local decomposition of `γ` (C18), once `L ≥ L₂`.  All the constants are uniform in the data.
-/

set_option autoImplicit false
set_option maxHeartbeats 3200000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Construction

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12
  HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

theorem sa12x3_per_identity (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (Cb T : ℝ)
    (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ (R' δ h L₂ : ℝ) (q : Euc d → ℝ), 0 < R' ∧ 0 < δ ∧ 0 < h ∧ ContDiff ℝ ∞ q ∧
      ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d), IsAdvectingDrift m Cb T b → HRS.Whole.IsNegDriftFlow T b Ψ →
      ∀ τ ∈ Icc (0 : ℝ) T, ∀ c0 : Euc d, ∀ (L : ℝ) (γ : Euc d → ℝ), L₂ ≤ L → 1 ≤ L →
        IsPeriodicRieszKernel d s L γ →
        ∀ (M : Matrix (Fin d) (Fin d) ℝ) (μ F : Euc d → ℝ), ContDiff ℝ ∞ μ → ContDiff ℝ ∞ F →
        (∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x) →
        (∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) →
        ∀ x : Euc d, advCutoff χ Ψ τ c0 x ≠ 0 →
          perNonlocal L γ M μ F x =
            eucNonlocal s M (fun y => advCutoff χh Ψ τ c0 y * μ y) F x +
            (∑ i : Fin d, ∑ j : Fin d, M j i * (L ^ (-s - 1) *
              ∫ y, fderiv ℝ q (L⁻¹ • (x - y)) (EuclideanSpace.single i (1 : ℝ)) *
                (advCutoff χh Ψ τ c0 y * μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))))) +
            (∑ i : Fin d, ∑ j : Fin d, M j i *
              ∫ y in {y | y - Ψ τ c0 ∈ centeredBox d L},
                fderiv ℝ γ (x - y) (EuclideanSpace.single i (1 : ℝ)) *
                  ((1 - advCutoff χh Ψ τ c0 y) * (μ y * fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))))) := by
  obtain ⟨δ, q, hδ, hq, hker⟩ := periodic_kernel_local hd s hs0 hsd
  obtain ⟨B, R, hB, hR1, hfacts⟩ := advected_cutoff_jets d hd m Cb T χ χh hχ
  obtain ⟨CF, hCF0, hCF⟩ := HRS.MH.Screened.flow_lip_sep_proof hd m Cb T χ χh hχ
  refine ⟨R + 1, δ, 4 * Real.exp (-(CF * T)), max (4 * (R + 1) + 1) (2 * (R + 1) / δ + 1), q,
    by linarith, hδ, by positivity, hq, ?_⟩
  intro b Ψ hb hΨ τ hτ c0 L γ hL hL1 hγ M μ F hμ hF hμp hFp x hx
  obtain ⟨c₁, -, hdec⟩ := hker L hL1 γ hγ
  have hcut := hfacts b Ψ hb hΨ τ hτ c0
  have hsupp : Function.support (advCutoff χh Ψ τ c0) ⊆ closedBall (Ψ τ c0) R := hcut.2.2
  have hxb : x ∈ ball (Ψ τ c0) (R + 1) := by
    have := hsupp (sa12z3_adv_support_le hχ Ψ τ c0 hx)
    exact closedBall_subset_ball (by linarith) this
  have hηs : tsupport (advCutoff χh Ψ τ c0) ⊆ ball (Ψ τ c0) (R + 1) :=
    (closure_minimal hsupp isClosed_closedBall).trans (closedBall_subset_ball (by linarith))
  have hηm : MemCb 1 (advCutoff χh Ψ τ c0) := by
    refine ⟨hcut.1.2.of_le (by exact_mod_cast (show 1 ≤ m + 1 by omega)), fun j hj => ⟨B, ?_⟩⟩
    rintro _ ⟨y, rfl⟩
    exact (hcut.2.1 j (by omega) y).2
  have hη1 : ∀ y ∈ ball x (4 * Real.exp (-(CF * T))), advCutoff χh Ψ τ c0 y = 1 := by
    intro y hy
    by_contra hne
    have hy1 : y ∈ tsupport (fun y => 1 - advCutoff χh Ψ τ c0 y) :=
      subset_tsupport _ (Function.mem_support.2 (fun h0 => hne (by linarith)))
    have hx1 : x ∈ tsupport (advCutoff χ Ψ τ c0) := subset_tsupport _ hx
    have hsep := (hCF b Ψ hb hΨ τ hτ).2.2 c0 x y hx1 hy1
    have hle : Real.exp (-(CF * T)) ≤ Real.exp (-(CF * τ)) :=
      Real.exp_le_exp.2 (by nlinarith [hτ.2, hCF0])
    have hd' : ‖x - y‖ < 4 * Real.exp (-(CF * T)) := by
      have hy' := mem_ball.1 hy
      rw [dist_eq_norm] at hy'
      rwa [norm_sub_rev]
    linarith
  have hbox : 4 * (R + 1) < L := by
    have := (le_max_left _ _).trans hL
    linarith
  have hloc : 2 * (R + 1) < δ * L := by
    have h1 : 2 * (R + 1) / δ + 1 ≤ L := (le_max_right _ _).trans hL
    have h2 : 2 * (R + 1) / δ < L := by linarith
    have := (div_lt_iff₀ hδ).1 h2
    linarith
  exact periodic_near_identity hd s hs0 hsd δ L (R + 1) (4 * Real.exp (-(CF * T))) hL1 (by linarith)
    (by positivity) hbox hloc q γ hq hγ c₁ hdec M μ F hμ hF hμp hFp (Ψ τ c0) x hxb
    (advCutoff χh Ψ τ c0) hηm hηs hη1

end HRS.MH.AdjointRd.Phase2SA12Construction
