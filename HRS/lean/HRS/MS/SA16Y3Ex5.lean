import HRS.MS.SA16Y3Ex4

/-!
# S.A.16 (SA16Y3) Ex5: the zeroth-component identity of the cut-off extension on all of `WmpSpace` (SA16S item (iii), step (c3))

`sa16y3_wrep_sub`: `wrep (A - B) =ᵐ wrep A - wrep B`.
`sa16y3_T_wrep`: for the extension `T` of `ψ ↦ cutmol n ψ` from `Jcc` (with `‖T‖ ≤ C`),
`wrep (T G) =ᵐ cutmol n (wrep G)` for every `G ∈ WmpSpace`.
Proof: density of `Jcc` and the bound `‖cutmol n f‖_p ≤ B ‖f‖_p` (Ex3), `‖wrep H‖_p ≤ ‖H‖` (Ex4).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal ContDiff Pointwise

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution

variable {d : ℕ}

lemma sa16y3_wrep_sub {p : ℝ} [Fact (2 ≤ p)] {m : ℕ} (A B : WmpSpace d m p) :
    wrep d m p (A - B) =ᵐ[volume] fun x => wrep d m p A x - wrep d m p B x := by
  filter_upwards [Lp.coeFn_sub (A : WLp d m p) (B : WLp d m p)] with x hx
  show (((A - B : WmpSpace d m p) : WLp d m p) : EuclideanSpace ℝ (Fin d) → (WIndex d m → ℝ)) x (wZero d m) = _
  rw [show ((A - B : WmpSpace d m p) : WLp d m p) = (A : WLp d m p) - (B : WLp d m p) from rfl, hx]
  rfl

lemma sa16y3_wrep_aesm {p : ℝ} [Fact (2 ≤ p)] {m : ℕ} (H : WmpSpace d m p) :
    AEStronglyMeasurable (fun x => wrep d m p H x) volume :=
  (continuous_apply (wZero d m)).comp_aestronglyMeasurable (Lp.aestronglyMeasurable (H : WLp d m p))

lemma sa16y3_wrep_memLp {p : ℝ} [Fact (2 ≤ p)] {m : ℕ} (H : WmpSpace d m p) :
    MemLp (fun x => wrep d m p H x) (ENNReal.ofReal p) volume := by
  exact (sa16y3_wrep_eLp H).trans_lt ENNReal.ofReal_lt_top

theorem sa16y3_T_wrep {p : ℝ} [Fact (2 ≤ p)] {m : ℕ} (n : ℕ) {C : ℝ}
    (T : WmpSpace d m p →L[ℝ] WmpSpace d m p) (hT : ‖T‖ ≤ C)
    (hTJ : ∀ ψ : ccSub d, T (sa16r_Jcc d m p ψ) = sa16r_J d m p (sa16y3_Lop m p n ψ))
    (G : WmpSpace d m p) :
    wrep d m p (T G) =ᵐ[volume] sa16y3_cutmol d n (wrep d m p G) := by
  have hp1r : 1 ≤ p := le_trans one_le_two (Fact.out : 2 ≤ p)
  have hp1 : 1 ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp1r
  have hp : 1 < p := lt_of_lt_of_le one_lt_two (Fact.out : 2 ≤ p)
  have hp0 : ENNReal.ofReal p ≠ 0 :=
    (ENNReal.ofReal_pos.2 (lt_of_lt_of_le zero_lt_two (Fact.out : 2 ≤ p))).ne'
  have hC0 : 0 ≤ C := (norm_nonneg T).trans hT
  obtain ⟨B, hB0, hB⟩ := sa16y3_cut_bound (d := d) 0
  have hχ : ∀ k : ℕ, ∀ x : EuclideanSpace ℝ (Fin d), ‖sa16y3_cut d k x‖ ≤ B := fun k x => by
    simpa using hB k 0 (le_refl 0) x
  have hbound : ∀ δ : ℝ, 0 < δ → eLpNorm (fun x => wrep d m p (T G) x - sa16y3_cutmol d n (wrep d m p G) x)
      (ENNReal.ofReal p) volume ≤ ENNReal.ofReal ((C + B) * δ) := by
    intro δ hδ
    obtain ⟨ψ, hψd⟩ := (sa16r_Jcc_dense d m p).exists_dist_lt G hδ
    have hGJ : ‖G - sa16r_Jcc d m p ψ‖ < δ := by
      rw [← dist_eq_norm]; exact hψd
    have hdec : (fun x => wrep d m p (T G) x - sa16y3_cutmol d n (wrep d m p G) x) =
        fun x => (wrep d m p (T G) x - wrep d m p (T (sa16r_Jcc d m p ψ)) x) +
          (wrep d m p (T (sa16r_Jcc d m p ψ)) x - sa16y3_cutmol d n (wrep d m p (sa16r_Jcc d m p ψ)) x) +
          (sa16y3_cutmol d n (wrep d m p (sa16r_Jcc d m p ψ)) x - sa16y3_cutmol d n (wrep d m p G) x) := by
      funext x; ring
    have hJw : MemLp (fun x => wrep d m p (sa16r_Jcc d m p ψ) x) (ENNReal.ofReal p) volume :=
      sa16y3_wrep_memLp _
    have hGw : MemLp (fun x => wrep d m p G x) (ENNReal.ofReal p) volume := sa16y3_wrep_memLp G
    have hCeq : (fun x => sa16y3_cutmol d n (wrep d m p (sa16r_Jcc d m p ψ)) x -
        sa16y3_cutmol d n (wrep d m p G) x) =
        sa16y3_cutmol d n (fun x => wrep d m p (sa16r_Jcc d m p ψ) x - wrep d m p G x) := by
      funext x
      exact (congrFun (sa16y3_cutmol_sub hp hJw hGw n) x).symm
    have hBz : (fun x => wrep d m p (T (sa16r_Jcc d m p ψ)) x -
        sa16y3_cutmol d n (wrep d m p (sa16r_Jcc d m p ψ)) x) =ᵐ[volume] 0 := by
      filter_upwards [sa16y3_T_wrep_cc (p := p) m n T hTJ ψ] with x hx
      simp only [Pi.zero_apply]
      exact sub_eq_zero.2 hx
    have hAw : (fun x => wrep d m p (T G) x - wrep d m p (T (sa16r_Jcc d m p ψ)) x) =ᵐ[volume]
        fun x => wrep d m p (T (G - sa16r_Jcc d m p ψ)) x := by
      have h := sa16y3_wrep_sub (T G) (T (sa16r_Jcc d m p ψ))
      rw [← map_sub] at h
      filter_upwards [h] with x hx
      exact hx.symm
    have hAn : eLpNorm (fun x => wrep d m p (T G) x - wrep d m p (T (sa16r_Jcc d m p ψ)) x)
        (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (C * δ) := by
      rw [eLpNorm_congr_ae hAw]
      refine (sa16y3_wrep_eLp _).trans (ENNReal.ofReal_le_ofReal ?_)
      calc ‖T (G - sa16r_Jcc d m p ψ)‖ ≤ ‖T‖ * ‖G - sa16r_Jcc d m p ψ‖ := T.le_opNorm _
        _ ≤ C * δ := mul_le_mul hT hGJ.le (norm_nonneg _) hC0
    have hCn : eLpNorm (fun x => sa16y3_cutmol d n (wrep d m p (sa16r_Jcc d m p ψ)) x -
        sa16y3_cutmol d n (wrep d m p G) x) (ENNReal.ofReal p) volume ≤ ENNReal.ofReal (B * δ) := by
      rw [hCeq]
      have hdiff : MemLp (fun x => wrep d m p (sa16r_Jcc d m p ψ) x - wrep d m p G x) (ENNReal.ofReal p) volume :=
        hJw.sub hGw
      refine (sa16y3_cutmol_eLp hp1r hB0 hχ n
        ((sa16y3_wrep_aesm _).sub (sa16y3_wrep_aesm _))).trans ?_
      have hJG := sa16y3_wrep_sub (sa16r_Jcc d m p ψ) G
      have hJG2 : eLpNorm (fun x => wrep d m p (sa16r_Jcc d m p ψ) x - wrep d m p G x) (ENNReal.ofReal p) volume =
          eLpNorm (wrep d m p (sa16r_Jcc d m p ψ - G)) (ENNReal.ofReal p) volume :=
        eLpNorm_congr_ae hJG.symm
      calc ENNReal.ofReal B * eLpNorm (fun x => wrep d m p (sa16r_Jcc d m p ψ) x - wrep d m p G x)
            (ENNReal.ofReal p) volume
          = ENNReal.ofReal B * eLpNorm (wrep d m p (sa16r_Jcc d m p ψ - G)) (ENNReal.ofReal p) volume := by
            rw [hJG2]
        _ ≤ ENNReal.ofReal B * ENNReal.ofReal ‖sa16r_Jcc d m p ψ - G‖ :=
            mul_le_mul' le_rfl (sa16y3_wrep_eLp _)
        _ ≤ ENNReal.ofReal (B * δ) := by
            rw [← ENNReal.ofReal_mul hB0]
            apply ENNReal.ofReal_le_ofReal
            rw [norm_sub_rev]
            exact mul_le_mul_of_nonneg_left hGJ.le hB0
    have hBn : eLpNorm (fun x => wrep d m p (T (sa16r_Jcc d m p ψ)) x -
        sa16y3_cutmol d n (wrep d m p (sa16r_Jcc d m p ψ)) x) (ENNReal.ofReal p) volume = 0 := by
      rw [eLpNorm_congr_ae hBz]
      exact eLpNorm_zero
    rw [hdec]
    calc eLpNorm (fun x => (wrep d m p (T G) x - wrep d m p (T (sa16r_Jcc d m p ψ)) x) +
          (wrep d m p (T (sa16r_Jcc d m p ψ)) x - sa16y3_cutmol d n (wrep d m p (sa16r_Jcc d m p ψ)) x) +
          (sa16y3_cutmol d n (wrep d m p (sa16r_Jcc d m p ψ)) x - sa16y3_cutmol d n (wrep d m p G) x))
          (ENNReal.ofReal p) volume
        ≤ eLpNorm (fun x => (wrep d m p (T G) x - wrep d m p (T (sa16r_Jcc d m p ψ)) x) +
          (wrep d m p (T (sa16r_Jcc d m p ψ)) x - sa16y3_cutmol d n (wrep d m p (sa16r_Jcc d m p ψ)) x))
          (ENNReal.ofReal p) volume +
          eLpNorm (fun x => sa16y3_cutmol d n (wrep d m p (sa16r_Jcc d m p ψ)) x -
            sa16y3_cutmol d n (wrep d m p G) x) (ENNReal.ofReal p) volume := eLpNorm_add_le hp1
      _ ≤ (eLpNorm (fun x => wrep d m p (T G) x - wrep d m p (T (sa16r_Jcc d m p ψ)) x) (ENNReal.ofReal p) volume +
          eLpNorm (fun x => wrep d m p (T (sa16r_Jcc d m p ψ)) x -
            sa16y3_cutmol d n (wrep d m p (sa16r_Jcc d m p ψ)) x) (ENNReal.ofReal p) volume) +
          eLpNorm (fun x => sa16y3_cutmol d n (wrep d m p (sa16r_Jcc d m p ψ)) x -
            sa16y3_cutmol d n (wrep d m p G) x) (ENNReal.ofReal p) volume :=
          add_le_add (eLpNorm_add_le hp1) le_rfl
      _ ≤ (ENNReal.ofReal (C * δ) + 0) + ENNReal.ofReal (B * δ) :=
          add_le_add (add_le_add hAn hBn.le) hCn
      _ = ENNReal.ofReal ((C + B) * δ) := by
          rw [add_zero, ← ENNReal.ofReal_add (mul_nonneg hC0 hδ.le) (mul_nonneg hB0 hδ.le)]
          congr 1
          ring
  have hmeas : AEStronglyMeasurable (fun x => wrep d m p (T G) x - sa16y3_cutmol d n (wrep d m p G) x)
      volume := (sa16y3_wrep_aesm _).sub (sa16y3_cutmol_aesm (sa16y3_wrep_aesm G) n)
  have hz : eLpNorm (fun x => wrep d m p (T G) x - sa16y3_cutmol d n (wrep d m p G) x)
      (ENNReal.ofReal p) volume = 0 := by
    refine le_antisymm ?_ bot_le
    apply ENNReal.le_of_forall_pos_le_add
    intro ε hε _
    have hεr : (0 : ℝ) < (ε : ℝ) := NNReal.coe_pos.2 hε
    have hCB1 : (0 : ℝ) < C + B + 1 := by linarith
    have hpos : (0 : ℝ) < (ε : ℝ) / (C + B + 1) := div_pos hεr hCB1
    refine (hbound _ hpos).trans ?_
    rw [zero_add]
    have hfrac : (C + B) / (C + B + 1) ≤ 1 := (div_le_one hCB1).2 (by linarith)
    have hle : (C + B) * ((ε : ℝ) / (C + B + 1)) ≤ (ε : ℝ) := by
      calc (C + B) * ((ε : ℝ) / (C + B + 1)) = (ε : ℝ) * ((C + B) / (C + B + 1)) := by ring
        _ ≤ (ε : ℝ) * 1 := mul_le_mul_of_nonneg_left hfrac hεr.le
        _ = (ε : ℝ) := mul_one _
    calc ENNReal.ofReal ((C + B) * ((ε : ℝ) / (C + B + 1))) ≤ ENNReal.ofReal (ε : ℝ) :=
          ENNReal.ofReal_le_ofReal hle
      _ = (ε : ℝ≥0∞) := ENNReal.ofReal_coe_nnreal
  have hF0 := (eLpNorm_eq_zero_iff hp0).1 hz
  filter_upwards [hF0] with x hx
  exact sub_eq_zero.1 hx

end HRS.Whole.AppendixA.Phase2SA16R
