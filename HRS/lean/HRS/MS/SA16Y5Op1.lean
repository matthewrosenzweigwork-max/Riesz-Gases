import HRS.MS.SA16Y4Io10

/-!
# S.A.16 (SA16Y5) Op1: the order-one nonlocal operator `W^{m+1,p} → W^{m,p}` for a smooth coefficient with decay

`sa16y5_G_smooth` (`0 ≤ s < d-1`, `d < p(s+1)`): for `|M_ij| ≤ MB`, `a ∈ SB` with `‖D^κ a(x)‖ ≤ W (1+|x|)^{-(d+3)}` (`κ ≤ m+2`)
there is a CLM `T : W^{m+1,p} → W^{m,p}`, `‖T‖ ≤ C` (`C = C(d,m,s,p,MB,W)`) with `wrep (T (Jcc φ)) = eucNonlocal s M a φ` a.e.
(the order-one analogue of `sa16y4_G_exists_smooth`; applied to the mollified and time-interpolated densities).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer
open HRS.Whole.AppendixA.Phase2SA16Q

section Op1
variable {d : ℕ}

theorem sa16y5_G_smooth (d m : ℕ) (hd : 1 ≤ d) (s p MB W : ℝ) [Fact (2 ≤ p)] (hs0 : 0 ≤ s)
    (hs1 : s < (d : ℝ) - 1) (hfar : (d : ℝ) < p * (s + 1)) (hW : 0 ≤ W) :
    ∃ C : ℝ, 0 < C ∧ ∀ M : Matrix (Fin d) (Fin d) ℝ, (∀ i j, |M i j| ≤ MB) → ∀ a : Euc d → ℝ, sa16q_SB a →
      (∀ κ ≤ m + 2, ∀ x, ‖iteratedFDeriv ℝ κ a x‖ ≤ W * (1 + ‖x‖) ^ (-((d + 3 : ℕ) : ℝ))) →
        ∃ T : WmpSpace d (m + 1) p →L[ℝ] WmpSpace d m p, ‖T‖ ≤ C ∧ ∀ φ : ccSub d,
          wrep d m p (T (sa16r_Jcc d (m + 1) p φ)) =ᵐ[volume]
            HRS.MH.AdjointRd.eucNonlocal s M a φ.1 := by
  have hp2 : 2 ≤ p := Fact.out
  obtain ⟨K, hK, hKb⟩ := sa16y4io_master hd hs0 hs1 hp2 hfar m MB W hW
  set card : ℝ≥0∞ := (Fintype.card (WIndex d m) : ℝ≥0∞) with hcard
  have hcardt : card ≠ ⊤ := ENNReal.natCast_ne_top _
  have hcK : card * K ≠ ⊤ := ENNReal.mul_ne_top hcardt hK
  set C : ℝ := (card * K).toReal + 1 with hC
  have hC0 : 0 < C := by positivity
  refine ⟨C, hC0, fun M hM a ha hdec => ?_⟩
  have ha1 : ContDiff ℝ 1 a := ha.1.of_le (by exact_mod_cast le_top)
  obtain ⟨_, B0, B1, hB0, hB1⟩ := sa16q_SB_C1 ha
  have hfin : ∀ φ : ccSub d, wNormE m p (HRS.MH.AdjointRd.eucNonlocal s M a φ.1) ≤
      ENNReal.ofReal (C * ‖sa16r_Jcc d (m + 1) p φ‖) := by
    intro φ
    set u := sa16so_schw φ with hu
    have hS : MemLp (sa16j_S d (m + 1) ⇑u) (ENNReal.ofReal p) volume := sa16j_S_memLp (m + 1) p u
    have hWjeq : wNormE (m + 1) p ⇑u = eLpNorm (wJet (m + 1) ⇑u) (ENNReal.ofReal p) volume :=
      sa16j_wNormE_eq d (m + 1) p u.smooth' hS
    set Wj := eLpNorm (wJet (m + 1) ⇑u) (ENNReal.ofReal p) volume with hWj
    have hWjt : Wj ≠ ⊤ := (sa16j_jet_memLp d (m + 1) p u.smooth' hS).eLpNorm_lt_top.ne
    have hb := sa16y_wnorm_of_pd d m p (f := HRS.MH.AdjointRd.eucNonlocal s M a ⇑u)
      (sa16y4io_F_smooth hd hs0 hs1 M ha u) (K := K * Wj) (ENNReal.mul_lt_top hK.lt_top hWjt.lt_top)
      (fun {j} hj idx => hKb M hM ha hdec u hj idx)
    have hnorm : wNormE (m + 1) p φ.1 = Wj := by
      rw [← hWjeq, hu, sa16so_schw_coe]
    rw [sa16so_wNormE_cc (m + 1)] at hnorm
    rw [ENNReal.ofReal_mul hC0.le, hnorm]
    refine hb.trans ?_
    rw [← mul_assoc]
    refine mul_le_mul' ?_ le_rfl
    calc card * K = ENNReal.ofReal (card * K).toReal := (ENNReal.ofReal_toReal hcK).symm
      _ ≤ ENNReal.ofReal C := ENNReal.ofReal_le_ofReal (by rw [hC]; linarith)
  have hex : ∀ φ : ccSub d, ∃ G : WmpSpace d m p,
      wrep d m p G =ᵐ[volume] HRS.MH.AdjointRd.eucNonlocal s M a φ.1 := fun φ =>
    sa16so_lift_exists m (lt_of_le_of_lt (hfin φ) ENNReal.ofReal_lt_top)
  choose A hA using hex
  have hAnorm : ∀ φ : ccSub d, ‖A φ‖ ≤ C * ‖sa16r_Jcc d (m + 1) p φ‖ := by
    intro φ
    have h1 := wNormE_eq_lift_norm d m p (A φ) (HRS.MH.AdjointRd.eucNonlocal s M a φ.1) (by
      filter_upwards [hA φ] with x hx
      exact hx)
    have h2 := hfin φ
    rw [h1] at h2
    exact (ENNReal.ofReal_le_ofReal_iff (mul_nonneg hC0.le (norm_nonneg _))).1 h2
  have hadd : ∀ φ ψ : ccSub d, A (φ + ψ) = A φ + A ψ := by
    intro φ ψ
    refine sa16r_wrep_inj d m p _ _ ?_
    filter_upwards [hA (φ + ψ), hA φ, hA ψ, sa16r_wrep_add d m p (A φ) (A ψ)] with x h1 h2 h3 h4
    rw [h4, h1, h2, h3]
    have := sa16y4io_F_add hd hs0 hs1 M ha1 hB0 hB1 (sa16so_schw φ) (sa16so_schw ψ) x
    exact this
  have hsmul : ∀ (c : ℝ) (φ : ccSub d), A (c • φ) = c • A φ := by
    intro c φ
    refine sa16r_wrep_inj d m p _ _ ?_
    filter_upwards [hA (c • φ), hA φ, sa16r_wrep_smul d m p c (A φ)] with x h1 h2 h3
    rw [h3, h1, h2]
    have := sa16y4io_F_smul hd hs0 hs1 M ha1 hB0 hB1 c (sa16so_schw φ) x
    exact this
  let Al : ccSub d →ₗ[ℝ] WmpSpace d m p := { toFun := A, map_add' := hadd, map_smul' := hsmul }
  obtain ⟨T, hT1, hT2, -⟩ := sa16r_ext_abstract (sa16r_Jcc d (m + 1) p) (sa16r_Jcc_dense d (m + 1) p) Al hC0.le hAnorm
  refine ⟨T, hT1, fun φ => ?_⟩
  rw [hT2 φ]
  exact hA φ

end Op1

end HRS.Whole.AppendixA.Phase2SA16R
