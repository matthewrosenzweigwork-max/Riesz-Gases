import HRS.Commutator.Torus.TPOSAux13

/-!
# T-POS helpers, part 14: `g_η^𝕋` is the Fourier series of `gTcoef`; value at the origin
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ} {s η : ℝ}

lemma tpos_fTrunc_bound (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ z : Euc d, z ≠ 0 →
      |Whole.fTrunc s η z| ≤ C * ‖z‖ ^ (-(2 * (d : ℝ) + 4)) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hs2 : s < 2 * (d : ℝ) + 4 := by linarith
  have hcp := Whole.cPhi_pos d hs0 hs2
  have h2 : (0 : ℝ) < 2 * (d : ℝ) + 4 - s := by linarith
  refine ⟨Whole.cPhi d s / (2 * (d : ℝ) + 4 - s) * η ^ (2 * (d : ℝ) + 4 - s), by positivity, ?_⟩
  intro z hz
  rw [abs_of_nonneg (tpos_fTrunc_nonneg hs0 hs2 η z)]
  exact tpos_fTrunc_le hs0 hs2 hη hz

lemma tpos_fTrunc_continuousOn (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) :
    ContinuousOn (Whole.fTrunc s η : Euc d → ℝ) {z | z ≠ 0} := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  intro z hz
  exact (tpos_fTrunc_continuousAt hs0 (by linarith) hη hz).continuousWithinAt

lemma tpos_S_continuousAt (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) {y0 : Euc d}
    (hy0 : Torus.mk y0 ≠ 0) :
    ContinuousAt (fun y : Euc d => ∑' m : Lattice d, Whole.fTrunc s η (y + Lattice.toEuc m)) y0 := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨C, hC, hb⟩ := tpos_fTrunc_bound hs0 hsd hη
  have := tpos_continuousAt_latsum (d := d) (h := Whole.fTrunc s η) hC (r := 2 * (d : ℝ) + 4)
    (by linarith) hb (tpos_fTrunc_continuousOn hs0 hsd hη) ∅ y0 (fun m _ h => hy0 (by
      have h' := tpos_mk_add_toEuc y0 m
      rw [h, show Torus.mk (0 : Euc d) = 0 by funext i; simp [Torus.mk]] at h'
      exact h'.symm))
  simpa using this

lemma tpos_Sne_continuousAt (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η) :
    ContinuousAt (fun y : Euc d => ∑' m : Lattice d,
      (if m = 0 then 0 else Whole.fTrunc s η (y + Lattice.toEuc m))) 0 := by
  classical
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  obtain ⟨C, hC, hb⟩ := tpos_fTrunc_bound hs0 hsd hη
  have := tpos_continuousAt_latsum (d := d) (h := Whole.fTrunc s η) hC (r := 2 * (d : ℝ) + 4)
    (by linarith) hb (tpos_fTrunc_continuousOn hs0 hsd hη) {0} 0 (fun m hm h => by
      simp only [Finset.mem_singleton] at hm
      apply hm
      have : Lattice.toEuc m = 0 := by simpa using h
      funext i
      have := congrFun (congrArg WithLp.ofLp this) i
      simpa [Lattice.toEuc] using this)
  simpa using this

lemma tpos_Gloc_continuousAt (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η)
    {r : Torus d → ℝ} (hr : Torus.IsSmooth r) : ContinuousAt (tposGloc s η r) 0 := by
  have h1 : Continuous (fun y : Euc d => r (Torus.mk y)) := (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) from hr).continuous
  have h2 : Continuous (fun y : Euc d => Whole.g1 s (η⁻¹ • y)) :=
    (Whole.g1_smooth hd hs0 hsd).continuous.comp (continuous_const_smul _)
  have h3 := tpos_Sne_continuousAt (d := d) hs0 hsd hη
  unfold tposGloc
  refine ContinuousAt.add (ContinuousAt.sub (ContinuousAt.add h1.continuousAt ?_)
    (continuousAt_const.mul h3)) continuousAt_const
  exact (continuousAt_const.mul h2.continuousAt).sub continuousAt_const

open Classical in
/-- `g_η^𝕋` with the origin value replaced by the local continuous extension. -/
def tposGstar (s η : ℝ) (r : Torus d → ℝ) (x : Torus d) : ℝ :=
  if x = 0 then tposGloc s η r 0 else gTorus s η x

lemma tpos_Gstar_lift_continuous (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (hη : 0 < η)
    (r : Torus d → ℝ) (δ : ℝ) (hδ : 0 < δ) (hr : Torus.IsSmooth r)
    (hsing : ∀ x : Euc d, ‖x‖ < δ → x ≠ 0 → periodicRiesz d s (Torus.mk x) =
      (if s = 0 then -Real.log ‖x‖ else ‖x‖ ^ (-s)) + r (Torus.mk x)) :
    Continuous (Torus.lift (tposGstar s η r)) := by
  classical
  have hd0 : (3 : ℝ) ≤ d := by exact_mod_cast hd
  -- continuity at the origin
  have h0 : ContinuousAt (Torus.lift (tposGstar s η r)) 0 := by
    refine (tpos_Gloc_continuousAt hd hs0 hsd hη hr).congr ?_
    have hball : Metric.ball (0 : Euc d) (min δ 1) ∈ 𝓝 (0 : Euc d) :=
      Metric.ball_mem_nhds _ (lt_min hδ one_pos)
    filter_upwards [hball] with y hy
    have hy' : ‖y‖ < min δ 1 := by simpa using hy
    by_cases hy0 : y = 0
    · subst hy0
      simp [Torus.lift, tposGstar, show Torus.mk (0 : Euc d) = 0 by funext i; simp [Torus.mk]]
    · have hne := tpos_mk_ne_zero_small hy0 (lt_of_lt_of_le hy' (min_le_right _ _))
      simp only [Torus.lift, Function.comp, tposGstar, if_neg hne]
      exact (tpos_local_eq hd hs0 hsd hη r δ hsing hy0 (lt_of_lt_of_le hy' (min_le_left _ _))
        (lt_of_lt_of_le hy' (min_le_right _ _))).symm
  rw [continuous_iff_continuousAt]
  intro y0
  by_cases hy0 : Torus.mk y0 = 0
  · obtain ⟨m, hm⟩ := tpos_mk_eq_zero hy0
    have hper : Torus.lift (tposGstar s η r) =
        fun y => Torus.lift (tposGstar s η r) (y + Lattice.toEuc (-m)) := by
      funext y; exact (Torus.lift_periodic _ y (-m)).symm
    rw [hper]
    have : y0 + Lattice.toEuc (-m) = 0 := by
      rw [hm]; ext i; simp [Lattice.toEuc]
    have hc : ContinuousAt (fun y : Euc d => y + Lattice.toEuc (-m)) y0 :=
      (continuous_id.add continuous_const).continuousAt
    exact ContinuousAt.comp (g := Torus.lift (tposGstar s η r)) (by rw [this]; exact h0) hc
  · -- away from the lattice
    have hU : {y : Euc d | Torus.mk y ≠ 0} ∈ 𝓝 y0 := tpos_isOpen_mk_ne.mem_nhds hy0
    set P1 : Euc d → ℝ := fun y => periodicRiesz d s (Torus.mk y)
    have hP1 : ContinuousAt P1 y0 := by
      have := (KernelGrad.contDiffOn_periodicRiesz (d := d) (s := s) (by omega) hs0
        (by linarith)).continuousOn
      exact this.continuousAt hU
    have hS := tpos_S_continuousAt hs0 hsd hη hy0
    have hRHS : ContinuousAt (fun y : Euc d => P1 y - tScale s *
        (∑' m : Lattice d, Whole.fTrunc s η (y + Lattice.toEuc m) -
          ∫ x : Torus d, perio (Whole.fTrunc s η : Euc d → ℝ) x)) y0 :=
      hP1.sub (continuousAt_const.mul (hS.sub continuousAt_const))
    refine hRHS.congr ?_
    filter_upwards [hU] with y hy
    have hy : Torus.mk y ≠ 0 := hy
    simp only [Torus.lift, Function.comp, tposGstar, if_neg hy]
    exact (tpos_lift_gTorus y hy).symm

end HRS.Commutator.TorusNote
