import HRS.MS.Fp81S21PredMap8
import HRS.MS.R2InterpAux126

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical Filter Topology Set
open scoped ENNReal RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

/-- Joint continuity of the charted propagated distribution in both times
and its coefficient input. -/
theorem fp81s21_chartVprop_joint_cont
    {d r : ℕ} {Pw m T : ℝ} {C : WholeCoeff d} {c : MultiIndex d → ℝ}
    (hP : (d : ℝ) < 2 * Pw) (hD : S101Data C m T r c)
    (hlin : S102Lin C m T) (E : r26t6_WeightedChart d r Pw) :
    ContinuousOn (fun p : (ℝ × ℝ) × r26t6_Coeff =>
      r2Vprop C m p.1.2 p.1.1 (fp81s21_chartAction E p.2))
      {p | 0 ≤ p.1.1 ∧ p.1.1 ≤ p.1.2 ∧ p.1.2 ≤ T} := by
  by_cases hT : 0 ≤ T
  · let tri : Set (ℝ × ℝ) := {p | 0 ≤ p.1 ∧ p.1 ≤ p.2 ∧ p.2 ≤ T}
    let K : ℝ := s102_KV d r Pw c
    have hQT : T ∈ Icc (0 : ℝ) T := ⟨hT, le_rfl⟩
    have hQd : ∀ t : ℝ, 0 ≤ t → t < T → ∀ δ > 0,
        ∃ q ∈ Icc (0 : ℝ) T, t < q ∧ q < t + δ ∧ q ≤ T := by
      intro t ht0 htT δ hδ
      obtain ⟨q, hq1, hq2⟩ :=
        exists_rat_btwn (lt_min htT (by linarith : t < t + δ))
      have hqT : (q : ℝ) < T := hq2.trans_le (min_le_left _ _)
      have hqt : (q : ℝ) < t + δ := hq2.trans_le (min_le_right _ _)
      refine ⟨q, ⟨ht0.trans hq1.le, hqT.le⟩, hq1, hqt, hqT.le⟩
    have hfixed (z : r26t6_Coeff) : ContinuousOn
        (fun p : ℝ × ℝ => r2Vprop C m p.2 p.1
          (fp81s21_chartAction E z)) tri := by
      let Kz : ℝ := ‖z‖ * K
      have hKz : 0 ≤ Kz := mul_nonneg (norm_nonneg z) (s102_KV_nonneg d r Pw c)
      have hslice : ∀ q ∈ Icc (0 : ℝ) T,
          ContinuousOn (fun u => r2Vprop C m q u (fp81s21_chartAction E z))
            (Icc 0 q) := by
        intro q hq
        exact fp81s21_chartVprop_source_cont hP hD hlin E z hq
      have hlip : ∀ u t t' : ℝ, 0 ≤ u → u ≤ t' → t' ≤ t → t ≤ T →
          ‖r2Vprop C m t u (fp81s21_chartAction E z) -
            r2Vprop C m t' u (fp81s21_chartAction E z)‖ ≤ Kz * (t - t') := by
        intro u t t' hu hut' htt' htT
        have huT : u ∈ Icc (0 : ℝ) T := ⟨hu, hut'.trans (htt'.trans htT)⟩
        have ht'I : t' ∈ Icc u T := ⟨hut', htt'.trans htT⟩
        have htI : t ∈ Icc u T := ⟨hut'.trans htt', htT⟩
        have hl := fp81s21_chartVprop_terminal_lipschitz hP hD hlin E z huT ht'I htI htt'
        rw [← fp81s21_chartVprop_physical hP hD hlin E z
            (fp81s21_chartAction E z) (fp81s21_chartAction_S102Z E z)
            (fun f _ => rfl) huT htI,
          ← fp81s21_chartVprop_physical hP hD hlin E z
            (fp81s21_chartAction E z) (fp81s21_chartAction_S102Z E z)
            (fun f _ => rfl) huT ht'I]
        simpa [Kz, K] using hl
      have hj := s102_joint_cont (T := T) (K := Kz)
        hKz
        (fun u t =>
          r2Vprop C m t u (fp81s21_chartAction E z))
        (Icc (0 : ℝ) T) hQT hQd hlip hslice
      simpa [tri] using hj
    rw [continuousOn_iff_continuous_domRestrict]
    refine (continuous_iff_seqContinuous).2 ?_
    intro ps p hps
    let F : ((ℝ × ℝ) × r26t6_Coeff) → OscDual d m := fun x =>
      r2Vprop C m x.1.2 x.1.1 (fp81s21_chartAction E x.2)
    let G : ℝ × ℝ → OscDual d m := fun x =>
      r2Vprop C m x.2 x.1 (fp81s21_chartAction E p.1.2)
    have hraw : Tendsto (fun n => (ps n : (ℝ × ℝ) × r26t6_Coeff)) atTop
        (𝓝 (p : (ℝ × ℝ) × r26t6_Coeff)) :=
      (continuous_subtype_val.tendsto p).comp hps
    have hrawTimes : Tendsto
        (fun n => ((ps n : (ℝ × ℝ) × r26t6_Coeff).1)) atTop
        (𝓝 ((p : (ℝ × ℝ) × r26t6_Coeff).1)) :=
      (continuous_fst.tendsto (p : (ℝ × ℝ) × r26t6_Coeff)).comp hraw
    have hrawCoeff : Tendsto
        (fun n => ((ps n : (ℝ × ℝ) × r26t6_Coeff).2)) atTop
        (𝓝 ((p : (ℝ × ℝ) × r26t6_Coeff).2)) :=
      (continuous_snd.tendsto (p : (ℝ × ℝ) × r26t6_Coeff)).comp hraw
    have hpTri : p.1.1 ∈ tri := by
      change 0 ≤ p.1.1.1 ∧ p.1.1.1 ≤ p.1.1.2 ∧ p.1.1.2 ≤ T
      exact p.2
    have hnTri : ∀ n, (ps n).1.1 ∈ tri := by
      intro n
      change 0 ≤ (ps n).1.1.1 ∧ (ps n).1.1.1 ≤ (ps n).1.1.2 ∧ (ps n).1.1.2 ≤ T
      exact (ps n).2
    have htimesWithin : Tendsto (fun n => (ps n).1.1) atTop (𝓝[tri] p.1.1) :=
      tendsto_nhdsWithin_iff.2 ⟨by simpa using hrawTimes,
        Filter.Eventually.of_forall hnTri⟩
    have hfix : Tendsto (fun n => G (ps n).1.1) atTop (𝓝 (G p.1.1)) :=
      (hfixed p.1.2 p.1.1 hpTri).tendsto.comp htimesWithin
    have hcoefTendsto : Tendsto (fun n => (ps n).1.2) atTop (𝓝 p.1.2) := by
      simpa using hrawCoeff
    have hcoefNorm : Tendsto (fun n => ‖(ps n).1.2 - p.1.2‖) atTop (𝓝 0) :=
      (tendsto_iff_norm_sub_tendsto_zero).1 hcoefTendsto
    have hvarBound : ∀ n,
        ‖F (ps n) - G (ps n).1.1‖ ≤ K * ‖(ps n).1.2 - p.1.2‖ := by
      intro n
      have hp : 0 ≤ (ps n).1.1.1 ∧
          (ps n).1.1.1 ≤ (ps n).1.1.2 ∧ (ps n).1.1.2 ≤ T := (ps n).2
      have hs : (ps n).1.1.1 ∈ Icc (0 : ℝ) T :=
        ⟨hp.1, hp.2.1.trans hp.2.2⟩
      have ht : (ps n).1.1.2 ∈ Icc (ps n).1.1.1 T :=
        ⟨hp.2.1, hp.2.2⟩
      let V := fp81s21_chartVprop hP hD hlin E hs ht
      change ‖V (ps n).1.2 - V p.1.2‖ ≤ K * ‖(ps n).1.2 - p.1.2‖
      rw [← map_sub]
      calc
        ‖V ((ps n).1.2 - p.1.2)‖ ≤ ‖V‖ * ‖(ps n).1.2 - p.1.2‖ := V.le_opNorm _
        _ ≤ K * ‖(ps n).1.2 - p.1.2‖ :=
          mul_le_mul_of_nonneg_right
            (fp81s21_chartVprop_norm_le hP hD hlin E hs ht)
            (norm_nonneg _)
    have hupper : Tendsto (fun n => K * ‖(ps n).1.2 - p.1.2‖) atTop (𝓝 0) := by
      simpa using (tendsto_const_nhds.mul hcoefNorm)
    have hvarNorm : Tendsto (fun n => ‖F (ps n) - G (ps n).1.1‖) atTop (𝓝 0) := by
      refine squeeze_zero' (Filter.Eventually.of_forall fun n => norm_nonneg _) ?_ hupper
      exact Filter.Eventually.of_forall hvarBound
    have hvar : Tendsto (fun n => F (ps n) - G (ps n).1.1) atTop (𝓝 0) := by
      rw [tendsto_iff_norm_sub_tendsto_zero]
      simpa using hvarNorm
    have hsum := hvar.add hfix
    have heq : (fun n => (F (ps n) - G (ps n).1.1) + G (ps n).1.1) =
        fun n => F (ps n) := by
      funext n
      simp
    rw [heq] at hsum
    change Tendsto (fun n => F (ps n)) atTop (𝓝 (F p))
    simpa [F, G] using hsum
  · intro p hp
    exact (hT (hp.1.trans (hp.2.1.trans hp.2.2))).elim

#print axioms HRS.Fp81.S21.fp81s21_chartVprop_joint_cont

end HRS.Fp81.S21
