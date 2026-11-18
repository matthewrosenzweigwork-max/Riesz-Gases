import HRS.MS.R26T8AP06d7

/-!
# S8.2 local Newton layer, packet T8A.P06d (part 8): continuous extension of the nested jets of `midPair F`
-/

set_option autoImplicit false
noncomputable section
open Filter Topology
open scoped ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

variable {d : ℕ}

theorem r26t8a_nest_ext (hd : 2 ≤ d) {chi : Euc d → ℝ} (hchi : NewtonCutoff chi) (k b : ℕ) (M σ : ℝ) (hM : 0 ≤ M)
    (hk : (k : ℝ) < -σ) {A : ℝ} (hA : 0 ≤ A) {F : Euc d → Euc d → ℝ} (hF : Conormal (k + 1) b M σ A F)
    (p q : ℕ) (hpq : p + q ≤ k) :
    ∃ g : Euc d × Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin p => Euc d)
        (ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ),
      Continuous g ∧ ∀ w : Euc d × Euc d, w.2 ≠ 0 →
        g w = r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) w.1 w.2 := by
  have hpk : p ≤ k := by omega
  have hk' : ((k - p : ℕ) : ℝ) < -σ := lt_of_le_of_lt (by exact_mod_cast Nat.sub_le k p) hk
  obtain ⟨C, hC0, hCj⟩ := r26t8a_limit_jets hd (k - p) b σ hk'
  set ε : ℝ := min (-σ - ((k - p : ℕ) : ℝ)) 1 / 2 with hεdef
  have hε : 0 < ε := by
    rw [hεdef]; have := lt_min (by linarith : 0 < -σ - ((k - p : ℕ) : ℝ)) one_pos; linarith
  obtain ⟨W, hW⟩ : ∃ W : Euc d → ℝ, W = fun X => 3 ^ (2 * M) * jbracket X ^ (2 * M) := ⟨_, rfl⟩
  have hW0 : ∀ X, 0 ≤ W X := fun X => by
    rw [hW]; exact mul_nonneg (Real.rpow_nonneg (by norm_num) _) (Real.rpow_nonneg (s83_jb_pos X).le _)
  obtain ⟨K, hK⟩ : ∃ K : Euc d → ℝ, K = fun X => C * A * W X := ⟨_, rfl⟩
  have hK0 : ∀ X, 0 ≤ K X := fun X => by rw [hK]; exact mul_nonneg (mul_nonneg hC0 hA) (hW0 X)
  have hKc : Continuous K := by
    rw [hK, hW]
    refine continuous_const.mul ?_
    exact continuous_const.mul ((r26t8a_jbracket_continuous (d := d)).rpow_const (fun x => Or.inr (by positivity)))
  have hF1 := hF.1
  have hF2 := hF.2
  have hCauchy : ∀ X z z' : Euc d, 0 < ‖z‖ → ‖z‖ ≤ 1 / 2 → 0 < ‖z'‖ → ‖z'‖ ≤ 1 / 2 →
      ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) X z -
        r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) X z'‖ ≤ K X * (‖z‖ ^ ε + ‖z'‖ ^ ε) := by
    intro X z z' hz hz1 hz' hz1'
    have hnn : 0 ≤ K X * (‖z‖ ^ ε + ‖z'‖ ^ ε) :=
      mul_nonneg (hK0 X) (add_nonneg (Real.rpow_nonneg (norm_nonneg _) _) (Real.rpow_nonneg (norm_nonneg _) _))
    refine ContinuousMultilinearMap.opNorm_le_bound hnn (fun u => ?_)
    obtain ⟨h, hh⟩ : ∃ h : Euc d → ℝ, h = fun z'' => r26t8a_iterDir ((List.ofFn u).map (ContinuousLinearMap.inl ℝ (Euc d) (Euc d)))
      (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) (X, z'') := ⟨_, rfl⟩
    obtain ⟨Au, hAu⟩ : ∃ Au : ℝ, Au = A * W X * ∏ i, ‖u i‖ := ⟨_, rfl⟩
    have hAu0 : 0 ≤ Au := by rw [hAu]; exact mul_nonneg (mul_nonneg hA (hW0 X)) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    have hcd : ContDiffOn ℝ (((k - p) + 1 : ℕ) : WithTop ℕ∞) h {z | z ≠ 0} := fun z0 hz0 => by
      rw [hh]; exact (r26t8a_contDiffAt_h hchi hF1 hpk hz0 X u).contDiffWithinAt
    have hjet : ∀ i ≤ (k - p) + 1, ∀ z0 : Euc d, 0 < ‖z0‖ → ‖z0‖ ≤ 1 →
        ‖iteratedFDeriv ℝ i h z0‖ ≤ Au * r26t8a_jetEnvelope b (σ + i) ‖z0‖ := by
      intro i hi z0 hz0 hz01
      have hz0' : z0 ≠ 0 := norm_pos_iff.1 hz0
      have e := r26t8a_nest_midPair_eq hchi hF1 (p := p) (i := i) (by omega) hz0' X u
      rw [show iteratedFDeriv ℝ i h z0 = (mixedJet p i F X z0) u by rw [hh]; exact e]
      have hb := hF2 p i (by omega) X z0 hz0'
      have hpw : pairWeight M (X + (1 / 2 : ℝ) • z0) (X - (1 / 2 : ℝ) • z0) ≤ W X :=
        by rw [hW]; exact r26t8a_p01_weight hM (by linarith)
      have henv : 0 ≤ r26t8a_jetEnvelope b (σ + i) ‖z0‖ := by
        unfold r26t8a_jetEnvelope; positivity
      calc ‖(mixedJet p i F X z0) u‖ ≤ ‖mixedJet p i F X z0‖ * ∏ j, ‖u j‖ := (mixedJet p i F X z0).le_opNorm u
        _ ≤ (A * pairWeight M (X + (1 / 2 : ℝ) • z0) (X - (1 / 2 : ℝ) • z0) * r26t8a_jetEnvelope b (σ + i) ‖z0‖) *
              ∏ j, ‖u j‖ := mul_le_mul_of_nonneg_right hb (Finset.prod_nonneg fun j _ => norm_nonneg _)
        _ ≤ (A * W X * r26t8a_jetEnvelope b (σ + i) ‖z0‖) * ∏ j, ‖u j‖ :=
            mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hpw hA) henv)
              (Finset.prod_nonneg fun j _ => norm_nonneg _)
        _ = Au * r26t8a_jetEnvelope b (σ + i) ‖z0‖ := by rw [hAu]; ring
    obtain ⟨Λ, -, -, hΛr⟩ := hCj Au hAu0 h hcd hjet
    have e1 := r26t8a_nest_midPair_eq hchi hF1 (p := p) (i := q) (by omega) (norm_pos_iff.1 hz) X u
    have e2 := r26t8a_nest_midPair_eq hchi hF1 (p := p) (i := q) (by omega) (norm_pos_iff.1 hz') X u
    have hq : q ≤ k - p := by omega
    have a1 := hΛr q hq z hz hz1
    have a2 := hΛr q hq z' hz' hz1'
    calc ‖(r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) X z -
          r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) X z') u‖
        = ‖iteratedFDeriv ℝ q h z - iteratedFDeriv ℝ q h z'‖ := by
          rw [show iteratedFDeriv ℝ q h z = (mixedJet p q F X z) u by rw [hh]; exact e1,
            show iteratedFDeriv ℝ q h z' = (mixedJet p q F X z') u by rw [hh]; exact e2]
          rfl
      _ ≤ ‖iteratedFDeriv ℝ q h z - Λ q‖ + ‖iteratedFDeriv ℝ q h z' - Λ q‖ := by
          rw [← norm_neg (iteratedFDeriv ℝ q h z' - Λ q)]
          refine le_trans (le_of_eq ?_) (norm_add_le _ _)
          congr 1; abel
      _ ≤ C * Au * ‖z‖ ^ ε + C * Au * ‖z'‖ ^ ε := add_le_add a1 a2
      _ = K X * (‖z‖ ^ ε + ‖z'‖ ^ ε) * ∏ i, ‖u i‖ := by rw [hAu, hK]; ring
  have hcont : ContinuousOn (fun w : Euc d × Euc d => r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) w.1 w.2)
      {w | w.2 ≠ 0} := by
    intro w0 hw0
    have hn : 0 < ‖w0.2‖ := norm_pos_iff.2 hw0
    obtain ⟨R, hRdef⟩ : ∃ R : ℝ, R = 2 * ‖w0.2‖ := ⟨_, rfl⟩
    have hRpos : 0 < R := by rw [hRdef]; positivity
    have hΨd := r26t8a_gtilde_contDiff hchi hRpos hF1
    have hΨ' : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
        (fun Yw : Euc d × Euc d => r26t8a_psiCut chi R Yw.2 * midPair F Yw.1 Yw.2) :=
      hΨd.of_le (by exact_mod_cast (by omega : p + q ≤ k + 1))
    have hopen : IsOpen {w : Euc d × Euc d | R / 4 < ‖w.2‖} := isOpen_lt continuous_const (continuous_norm.comp continuous_snd)
    have hc := (r26t8a_p06d_nest_continuous p q hΨ').continuousAt (x := w0)
    refine (hc.congr ?_).continuousWithinAt
    filter_upwards [hopen.mem_nhds (show R / 4 < ‖w0.2‖ by rw [hRdef]; linarith)] with w hw
    exact (r26t8a_nest_gtilde hchi hRpos (F := F) p q w.1 w.2 hw).trans rfl
  have hKloc : ∀ X0 : Euc d, ∃ r K0 : ℝ, 0 < r ∧ ∀ X ∈ Metric.ball X0 r, K X ≤ K0 := fun X0 => by
    obtain ⟨δ, hδ, hδ'⟩ := Metric.continuousAt_iff.1 hKc.continuousAt 1 one_pos
    refine ⟨δ, K X0 + 1, hδ, fun X hX => ?_⟩
    have := hδ' (by simpa using hX : dist X X0 < δ)
    rw [Real.dist_eq] at this
    linarith [(abs_lt.1 this).2]
  haveI : CompleteSpace (ContinuousMultilinearMap ℝ (fun _ : Fin p => Euc d)
      (ContinuousMultilinearMap ℝ (fun _ : Fin q => Euc d) ℝ)) := ContinuousMultilinearMap.instCompleteSpace
  exact r26t8a_cauchy_ext (by omega) (fun X z => r26t8a_nest p q (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) X z)
    K hK0 hε hCauchy hcont hKloc

end HRS.MS.R26T8A
