import HRS.MC.E214H2
import HRS.MC.E213P
import HRS.MD.EQGaussWindow

/-!
# E214H3: window paths and the sup-norm bound

`procWin` of a process continuous on `[0,a+T]` is the honest path; the embedding `epath` is norm-decreasing;
the norm of `epath (procWin η - procWin ηs)` is bounded by the `iSup` of the `ENNReal` norms of the
differences.
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal

namespace HRS.MC.E214H

open HRS HRS.Main HRS.Sec7

variable {d : ℕ}

theorem procWin_at {r T a : ℝ} (ha : 0 ≤ a) {Ω : Type} (η : ℝ → Ω → NegSobolev d r) (ω : Ω)
    (hω : ContinuousOn (fun t => η t ω) (Set.Icc 0 (a + T))) (t : Set.Icc (0 : ℝ) T) :
    (procWin r T a η ω).at' t = η (a + t) ω := by
  have hc : Continuous fun t : Set.Icc (0 : ℝ) T => η (a + t) ω := by
    have : ContinuousOn (fun t => η (a + t) ω) (Set.Icc 0 T) :=
      hω.comp (continuousOn_const.add continuousOn_id)
        (fun t ht => ⟨by linarith [ht.1], by linarith [ht.2]⟩)
    exact continuousOn_iff_continuous_domRestrict.1 this
  have e1 : procWin r T a η ω =
      (⟨fun t : Set.Icc (0 : ℝ) T => η (a + t) ω, hc⟩ : C(Set.Icc (0 : ℝ) T, NegSobolev d r)) :=
    dif_pos hc
  rw [e1]
  rfl

theorem norm_epath_le {r m : ℝ} (hrm : r ≤ m) (T : ℝ) (w : PathSpace d r T) :
    ‖HRS.MD.EQInterp.epath hrm T w‖ ≤ ‖w‖ := by
  refine (ContinuousMap.norm_le _ (norm_nonneg _)).2 fun t => ?_
  have h1 : ‖(HRS.MD.EQInterp.epath hrm T w).at' t‖ ≤ ‖w.at' t‖ := by
    rw [HRS.MD.EQInterp.epath_at']
    exact NegSobolev.norm_embed_le m hrm _
  exact h1.trans (ContinuousMap.norm_coe_le_norm (show C(Set.Icc (0 : ℝ) T, NegSobolev d r) from w) t)

theorem enorm_epath_sub_le {r m T a : ℝ} (hrm : r ≤ m) (ha : 0 ≤ a) {Ω : Type}
    (η ηs : ℝ → Ω → NegSobolev d r) (ω : Ω)
    (h1 : ContinuousOn (fun t => η t ω) (Set.Icc 0 (a + T)))
    (h2 : ContinuousOn (fun t => ηs t ω) (Set.Icc 0 (a + T))) :
    ‖HRS.MD.EQInterp.epath hrm T (procWin r T a η ω) - HRS.MD.EQInterp.epath hrm T (procWin r T a ηs ω)‖ₑ ≤
      ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖η (a + t) ω - ηs (a + t) ω‖ₑ := by
  set b : ℝ≥0∞ := ⨆ t ∈ Set.Icc (0 : ℝ) T, ‖η (a + t) ω - ηs (a + t) ω‖ₑ with hb
  by_cases htop : b = ⊤
  · rw [htop]; exact le_top
  have hbt : b.toReal ≥ 0 := ENNReal.toReal_nonneg
  have hle : ∀ t : Set.Icc (0 : ℝ) T, ‖η (a + t) ω - ηs (a + t) ω‖ ≤ b.toReal := by
    intro t
    have : ‖η (a + t) ω - ηs (a + t) ω‖ₑ ≤ b := le_iSup₂ (f := fun t (_ : t ∈ Set.Icc (0 : ℝ) T) =>
      ‖η (a + t) ω - ηs (a + t) ω‖ₑ) (t : ℝ) t.2
    have h := ENNReal.toReal_mono htop this
    simpa using h
  rw [← map_sub]
  have key : ∀ t : Set.Icc (0 : ℝ) T,
      ‖(show C(Set.Icc (0 : ℝ) T, NegSobolev d r) from
        (procWin r T a η ω - procWin r T a ηs ω)) t‖ ≤ b.toReal := by
    intro t
    have : (show C(Set.Icc (0 : ℝ) T, NegSobolev d r) from
        (procWin r T a η ω - procWin r T a ηs ω)) t = η (a + t) ω - ηs (a + t) ω := by
      show (procWin r T a η ω).at' t - (procWin r T a ηs ω).at' t = _
      rw [procWin_at ha η ω h1 t, procWin_at ha ηs ω h2 t]
    rw [this]; exact hle t
  have hn : ‖HRS.MD.EQInterp.epath hrm T (procWin r T a η ω - procWin r T a ηs ω)‖ ≤ b.toReal :=
    (norm_epath_le hrm T _).trans ((ContinuousMap.norm_le _ hbt).2 key)
  rw [← ofReal_norm]
  calc ENNReal.ofReal _ ≤ ENNReal.ofReal b.toReal := ENNReal.ofReal_le_ofReal hn
    _ = b := ENNReal.ofReal_toReal htop

end HRS.MC.E214H

end
