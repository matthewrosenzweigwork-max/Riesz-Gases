import HRS.MS.SA16StrongWnormAlg
import HRS.MS.SA16TransferFamilyDefs

/-!
# S.A.16: lower semicontinuity of `wNormE` along a Cauchy sequence

`sa16y_wnorm_limit`: if `F_n → F` pointwise, `wNormE m p (F_n - F_l) → 0` and `wNormE m p F_n ≤ b < ∞`, then
`wNormE m p F ≤ b`.  The lifts `G_n ∈ W^{m,p}` of `F_n` (unique by SL4) form a Cauchy sequence (SL6), converge in the
complete space `WmpSpace`, and the limit is a lift of `F`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16
open HRS HRS.Whole HRS.Whole.AppendixA

section Limit
variable {d : ℕ}

lemma sa16y_exists_lift (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] {u : Euc d → ℝ} (hu : wNormE m p u < ⊤) :
    ∃ G : WmpSpace d m p, ∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = u x := by
  unfold wNormE at hu
  rw [iInf_lt_iff] at hu
  obtain ⟨G, hG⟩ := hu
  rw [iInf_lt_iff] at hG
  obtain ⟨h, -⟩ := hG
  exact ⟨G, h⟩

lemma sa16y_zero_sub (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (G H : WmpSpace d m p) :
    ∀ᵐ x ∂(volume : Measure (Euc d)),
      (((G - H : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) =
        ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) -
          ((H : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) := by
  have h := Lp.coeFn_sub (G : WLp d m p) (H : WLp d m p)
  filter_upwards [h] with x hx
  have : (((G - H : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x =
      ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x - ((H : WLp d m p) : Euc d → (WIndex d m → ℝ)) x := hx
  rw [this]
  rfl

theorem sa16y_wnorm_limit (m : ℕ) (p : ℝ) [Fact (2 ≤ p)] (F : ℕ → Euc d → ℝ) (F' : Euc d → ℝ)
    (b : ℝ≥0∞) (hb : b < ⊤) (hbd : ∀ n, wNormE m p (F n) ≤ b)
    (hlim : ∀ᵐ x ∂(volume : Measure (Euc d)), Tendsto (fun n => F n x) atTop (𝓝 (F' x)))
    (hC : ∀ ε : ℝ, 0 < ε → ∃ N : ℕ, ∀ n ≥ N, ∀ l ≥ N,
      wNormE m p (fun x => F n x - F l x) ≤ ENNReal.ofReal ε) :
    wNormE m p F' ≤ b := by
  have hp1 : (1 : ℝ) ≤ p := by have : (2 : ℝ) ≤ p := Fact.out; linarith
  have hfin : ∀ n, wNormE m p (F n) < ⊤ := fun n => lt_of_le_of_lt (hbd n) hb
  choose G hG using fun n => sa16y_exists_lift m p (hfin n)
  -- norms
  have hnorm : ∀ n, ENNReal.ofReal ‖G n‖ = wNormE m p (F n) := fun n =>
    (wNormE_eq_lift_norm d m p (G n) (F n) (hG n)).symm
  have hdiff : ∀ n l, wNormE m p (fun x => F n x - F l x) = ENNReal.ofReal ‖G n - G l‖ := by
    intro n l
    refine wNormE_eq_lift_norm d m p (G n - G l) _ ?_
    filter_upwards [sa16y_zero_sub m p (G n) (G l), hG n, hG l] with x hx h1 h2
    rw [hx, h1, h2]
  -- Cauchy
  have hcauchy : CauchySeq G := by
    rw [Metric.cauchySeq_iff']
    intro ε hε
    obtain ⟨N, hN⟩ := hC (ε / 2) (by positivity)
    refine ⟨N, fun n hn => ?_⟩
    have := hN n hn N le_rfl
    rw [hdiff n N] at this
    rw [dist_eq_norm]
    have h2 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 this
    linarith
  obtain ⟨G', hG'⟩ := cauchySeq_tendsto_of_complete hcauchy
  -- the zeroth components
  set z : ℕ → Euc d → ℝ := fun n x => ((G n : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) with hz
  set z' : Euc d → ℝ := fun x => ((G' : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) with hz'
  have hzmeas : ∀ n, AEStronglyMeasurable (z n) volume := by
    intro n
    exact (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : WIndex d m => ℝ) (wZero d m)).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (G n : WLp d m p))
  have hz'meas : AEStronglyMeasurable z' volume :=
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : WIndex d m => ℝ) (wZero d m)).continuous.comp_aestronglyMeasurable
      (Lp.aestronglyMeasurable (G' : WLp d m p))
  have hzT : Tendsto (fun n => eLpNorm (z n - z') (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    have hnT : Tendsto (fun n => ‖G n - G'‖) atTop (𝓝 0) := tendsto_iff_norm_sub_tendsto_zero.1 hG'
    have hle : ∀ n, eLpNorm (z n - z') (ENNReal.ofReal p) volume ≤ ENNReal.ofReal ‖G n - G'‖ := by
      intro n
      have hnorm' : ‖G n - G'‖ = (eLpNorm (fun x => ((((G n - G' : WmpSpace d m p) : WLp d m p) :
          Euc d → (WIndex d m → ℝ)) x)) (ENNReal.ofReal p) volume).toReal := by
        have : ‖G n - G'‖ = ‖((G n - G' : WmpSpace d m p) : WLp d m p)‖ := rfl
        rw [this, Lp.norm_def]
      have hfin' : eLpNorm (fun x => ((((G n - G' : WmpSpace d m p) : WLp d m p) :
          Euc d → (WIndex d m → ℝ)) x)) (ENNReal.ofReal p) volume < ⊤ :=
        Lp.eLpNorm_lt_top _
      rw [hnorm', ENNReal.ofReal_toReal hfin'.ne]
      refine eLpNorm_mono_ae ((hzmeas n).sub hz'meas) ?_
      have h := Lp.coeFn_sub (G n : WLp d m p) (G' : WLp d m p)
      filter_upwards [h] with x hx
      have : (((G n - G' : WmpSpace d m p) : WLp d m p) : Euc d → (WIndex d m → ℝ)) x =
        ((G n : WLp d m p) : Euc d → (WIndex d m → ℝ)) x - ((G' : WLp d m p) : Euc d → (WIndex d m → ℝ)) x := hx
      rw [this]
      simp only [Pi.sub_apply, hz, hz']
      exact norm_le_pi_norm (((G n : WLp d m p) : Euc d → (WIndex d m → ℝ)) x -
        ((G' : WLp d m p) : Euc d → (WIndex d m → ℝ)) x) (wZero d m)
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds ?_ (fun n => bot_le) hle
    have : Tendsto (fun n => ENNReal.ofReal ‖G n - G'‖) atTop (𝓝 (ENNReal.ofReal 0)) :=
      ENNReal.tendsto_ofReal hnT
    simpa using this
  have hpe : ENNReal.ofReal p ≠ 0 := by simpa using (by linarith : 0 < p)
  have hinM := tendstoInMeasure_of_tendsto_eLpNorm hpe hzT
  obtain ⟨ns, hns, hae⟩ := hinM.exists_seq_tendsto_ae
  have hzF : ∀ᵐ x ∂(volume : Measure (Euc d)), ∀ n, z n x = F n x := by
    rw [ae_all_iff]; intro n; exact hG n
  have hlift : ∀ᵐ x ∂(volume : Measure (Euc d)), z' x = F' x := by
    filter_upwards [hae, hzF, hlim] with x hx1 hx2 hxl
    have h1 : Tendsto (fun i => F (ns i) x) atTop (𝓝 (F' x)) := hxl.comp hns.tendsto_atTop
    have h2 : Tendsto (fun i => F (ns i) x) atTop (𝓝 (z' x)) := by
      refine hx1.congr fun i => ?_
      exact hx2 (ns i)
    exact tendsto_nhds_unique h2 h1
  -- conclude
  have h1 : wNormE m p F' = ENNReal.ofReal ‖G'‖ := wNormE_eq_lift_norm d m p G' F' hlift
  rw [h1]
  have hbR : ∀ n, ‖G n‖ ≤ b.toReal := by
    intro n
    have := (hnorm n).trans_le (hbd n)
    exact (ENNReal.ofReal_le_iff_le_toReal hb.ne).1 this
  have : ‖G'‖ ≤ b.toReal := le_of_tendsto (hG'.norm) (Eventually.of_forall hbR)
  calc ENNReal.ofReal ‖G'‖ ≤ ENNReal.ofReal b.toReal := ENNReal.ofReal_le_ofReal this
    _ = b := ENNReal.ofReal_toReal hb.ne

end Limit

end HRS.Whole.AppendixA.Phase2SA16
