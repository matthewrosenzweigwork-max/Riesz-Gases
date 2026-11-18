import HRS.MS.SA16SOp5

/-!
# S.A.16 (SA16Y4) Nl1: the nonlocal operator on `WmpSpace d ℓ p` for a SMOOTH weighted coefficient (levels `ℓ`, `ℓ+1`)

`sa16y4_G_exists_smooth`: for `a` smooth with all derivatives bounded (`sa16q_SB a`) and
`‖D^κ a(x)‖ ≤ W (1+‖x‖)^{-(d+3)}` for `κ ≤ ℓ+1`, there is `T : W^{ℓ,p} → W^{ℓ,p}` with `‖T‖ ≤ C` (`C` depends only on
`d, ℓ, s, p, MB, W`) and zeroth component `eucNonlocal s M a φ` on `Jcc φ`.  This is `sa16so_G_exists` with the regularity hypothesis
replaced by the weighted derivative bounds that are actually used (so it applies at level `ℓ = m+1` to mollified `μ_n`, whose
derivatives up to order `m+2` are bounded uniformly in `n`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Nl1
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

theorem sa16y4_G_exists_smooth (d m : ℕ) (s p MB W : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs2 : s ≤ (d : ℝ) - 2) (hfar : (d : ℝ) < p * (s + 1)) (hW : 0 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) → ∀ a : Euc d → ℝ,
      sa16q_SB a → (∀ κ ≤ m + 1, ∀ x, ‖iteratedFDeriv ℝ κ a x‖ ≤ W * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) →
        ∃ T : WmpSpace d m p →L[ℝ] WmpSpace d m p, ‖T‖ ≤ C ∧ ∀ φ : ccSub d,
          wrep d m p (T (sa16r_Jcc d m p φ)) =ᵐ[volume]
            HRS.MH.AdjointRd.eucNonlocal s M a φ.1 := by
  have hp2 : (2 : ℝ) ≤ p := Fact.out
  have hd2 : 2 ≤ d := by
    have : (2 : ℝ) ≤ d := by linarith
    exact_mod_cast this
  obtain ⟨K, hK, hKb⟩ := sa16q_unif_master hd2 hs0 hs2 hp2 hfar m MB W hW
  set card : ℝ≥0∞ := (Fintype.card (WIndex d m) : ℝ≥0∞) with hcard
  have hcardt : card ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcKt : card * K ≠ ⊤ := ENNReal.mul_ne_top hcardt hK
  refine ⟨(card * K).toReal + 1, by positivity, fun M hM a hSB hwt => ?_⟩
  set C : ℝ := (card * K).toReal + 1 with hC
  have hCpos : 0 < C := by positivity
  have hcK : card * K ≤ ENNReal.ofReal C := by
    rw [← ENNReal.ofReal_toReal hcKt]
    exact ENNReal.ofReal_le_ofReal (by rw [hC]; linarith)
  obtain ⟨hμ1, B0, B1, hB0, hB1⟩ := sa16q_SB_C1 hSB
  -- finiteness and bound
  have hfin : ∀ φ : ccSub d, wNormE m p (HRS.MH.AdjointRd.eucNonlocal s M a φ.1) ≤
      ENNReal.ofReal (C * ‖sa16r_Jcc d m p φ‖) := by
    intro φ
    set u := sa16so_schw φ with hu
    have hS : MemLp (sa16j_S d m ⇑u) (ENNReal.ofReal p) volume := sa16j_S_memLp m p u
    have hWjeq : wNormE m p ⇑u = eLpNorm (wJet m ⇑u) (ENNReal.ofReal p) volume :=
      sa16j_wNormE_eq d m p u.smooth' hS
    have hWjt : eLpNorm (wJet m ⇑u) (ENNReal.ofReal p) volume ≠ ⊤ :=
      (sa16j_jet_memLp d m p u.smooth' hS).eLpNorm_lt_top.ne
    have hb := sa16y_wnorm_of_pd d m p (f := HRS.MH.AdjointRd.eucNonlocal s M a ⇑u)
      (sa16q_F_smooth hd2 hs0 hs2 M hSB u)
      (K := K * eLpNorm (wJet m ⇑u) (ENNReal.ofReal p) volume)
      (ENNReal.mul_lt_top hK.lt_top hWjt.lt_top)
      (fun {j} hj idx => hKb M hM hSB hwt u hj idx)
    rw [sa16so_schw_coe] at hb
    rw [sa16so_schw_coe, sa16so_wNormE_cc] at hWjeq
    refine hb.trans ?_
    rw [ENNReal.ofReal_mul hCpos.le, ← hWjeq, ← mul_assoc]
    exact mul_le_mul' hcK le_rfl
  have hex : ∀ φ : ccSub d, ∃ G : WmpSpace d m p,
      wrep d m p G =ᵐ[volume] HRS.MH.AdjointRd.eucNonlocal s M a φ.1 := fun φ =>
    sa16so_lift_exists m (lt_of_le_of_lt (hfin φ) ENNReal.ofReal_lt_top)
  choose A hA using hex
  have hAnorm : ∀ φ : ccSub d, ‖A φ‖ ≤ C * ‖sa16r_Jcc d m p φ‖ := by
    intro φ
    have h1 := wNormE_eq_lift_norm d m p (A φ) (HRS.MH.AdjointRd.eucNonlocal s M a φ.1) (by
      filter_upwards [hA φ] with x hx
      exact hx)
    have h2 := hfin φ
    rw [h1] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hCpos.le (norm_nonneg _))).1 h2
  -- linearity
  have hadd : ∀ φ ψ : ccSub d, A (φ + ψ) = A φ + A ψ := by
    intro φ ψ
    refine sa16r_wrep_inj d m p _ _ ?_
    filter_upwards [hA (φ + ψ), hA φ, hA ψ, sa16r_wrep_add d m p (A φ) (A ψ)] with x h1 h2 h3 h4
    rw [h4, h1, h2, h3]
    have := sa16so_F_add hd2 hs0 hs2 M hμ1 hB0 hB1 (sa16so_schw φ) (sa16so_schw ψ) x
    exact this
  have hsmul : ∀ (c : ℝ) (φ : ccSub d), A (c • φ) = c • A φ := by
    intro c φ
    refine sa16r_wrep_inj d m p _ _ ?_
    filter_upwards [hA (c • φ), hA φ, sa16r_wrep_smul d m p c (A φ)] with x h1 h2 h3
    rw [h3, h1, h2]
    have := sa16so_F_smul hd2 hs0 hs2 M hμ1 hB0 hB1 c (sa16so_schw φ) x
    exact this
  let Al : ccSub d →ₗ[ℝ] WmpSpace d m p := { toFun := A, map_add' := hadd, map_smul' := hsmul }
  obtain ⟨T, hT1, hT2, -⟩ := sa16r_ext_abstract (sa16r_Jcc d m p) (sa16r_Jcc_dense d m p) Al hCpos.le hAnorm
  refine ⟨T, hT1, fun φ => ?_⟩
  rw [hT2 φ]
  exact hA φ


end Nl1

end HRS.Whole.AppendixA.Phase2SA16R
