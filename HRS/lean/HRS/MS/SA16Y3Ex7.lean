import HRS.MS.SA16Y3Ex6

/-!
# S.A.16 (SA16Y3) Ex7: strong convergence of the cut-off extensions on `WmpSpace` (SA16S item (iii), step (d1))

`sa16y3_Lop_eq`: `sa16r_J (Lop n ψ) = Jcc (cutmol n ψ)` (uniqueness of `WmpSpace` elements).
`sa16y3_T_Jcc_tendsto`: `‖T_n (Jcc ψ) - Jcc ψ‖ → 0` for `ψ ∈ C_c^∞`.
`sa16y3_T_tendsto`: `‖T_n G - G‖ → 0` for every `G ∈ WmpSpace` (uniform bound `‖T_n‖ ≤ C`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal ContDiff Pointwise

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution

variable {d : ℕ}

lemma sa16y3_cc_sub {f g : EuclideanSpace ℝ (Fin d) → ℝ} (hf : IsCcInfty f) (hg : IsCcInfty g) :
    IsCcInfty (fun y => f y - g y) :=
  ⟨hf.1.sub hg.1, hf.2.sub hg.2⟩

theorem sa16y3_Lop_eq {p : ℝ} [Fact (2 ≤ p)] (m n : ℕ) (ψ : ccSub d) :
    sa16r_J d m p (sa16y3_Lop m p n ψ) = sa16r_Jcc d m p ⟨sa16y3_cutmol d n ψ.1, sa16y3_cutmol_cc ψ.2 n⟩ := by
  refine sa16r_wrep_inj d m p _ _ ?_
  have h2 : wrep d m p (sa16r_Jcc d m p ⟨sa16y3_cutmol d n ψ.1, sa16y3_cutmol_cc ψ.2 n⟩) =ᵐ[volume]
      sa16y3_cutmol d n ψ.1 := by
    rw [sa16r_Jcc_eq]
    exact sa16r_cc_elt_wrep (p := p) (sa16y3_cutmol_cc ψ.2 n) m
  exact (sa16r_J_spec d m p (sa16y3_Lop m p n ψ)).trans h2.symm

theorem sa16y3_T_Jcc_tendsto {p : ℝ} [Fact (2 ≤ p)] (hp : 1 ≤ p) (m : ℕ)
    (T : ℕ → (WmpSpace d m p →L[ℝ] WmpSpace d m p))
    (hTJ : ∀ (n : ℕ) (ψ : ccSub d), T n (sa16r_Jcc d m p ψ) = sa16r_J d m p (sa16y3_Lop m p n ψ))
    (ψ : ccSub d) :
    Tendsto (fun n => ‖T n (sa16r_Jcc d m p ψ) - sa16r_Jcc d m p ψ‖) atTop (𝓝 0) := by
  obtain ⟨R, hR⟩ := ψ.2.2.isCompact.isBounded.subset_closedBall (0 : EuclideanSpace ℝ (Fin d))
  have hzero : ∀ x : EuclideanSpace ℝ (Fin d), R < ‖x‖ → ψ.1 x = 0 := by
    intro x hx
    apply image_eq_zero_of_notMem_tsupport
    intro hxs
    have := hR hxs
    rw [mem_closedBall, dist_zero_right] at this
    linarith
  -- the difference as a `ccSub` element
  have hdiff : ∀ n : ℕ, T n (sa16r_Jcc d m p ψ) - sa16r_Jcc d m p ψ =
      sa16r_Jcc d m p ⟨fun y => sa16y3_cutmol d n ψ.1 y - ψ.1 y,
        sa16y3_cc_sub (sa16y3_cutmol_cc ψ.2 n) ψ.2⟩ := by
    intro n
    rw [hTJ n ψ, sa16y3_Lop_eq, ← map_sub]
    rfl
  have hnorm : ∀ n : ℕ, ‖T n (sa16r_Jcc d m p ψ) - sa16r_Jcc d m p ψ‖ =
      (eLpNorm (fun x => ‖wJet m (fun y => sa16y3_cutmol d n ψ.1 y - ψ.1 y) x‖) (ENNReal.ofReal p) volume).toReal := by
    intro n
    rw [hdiff n, sa16r_Jcc_norm d m p, sa16y3_norm_wJet_eq
      (sa16y3_cc_sub (sa16y3_cutmol_cc ψ.2 n) ψ.2) m]
  have hE : Tendsto (fun n => eLpNorm (fun x => ‖wJet m (fun y => sa16y3_cutmol d n ψ.1 y - ψ.1 y) x‖)
      (ENNReal.ofReal p) volume) atTop (𝓝 0) := by
    refine (sa16y3_jet_sub_tendsto hp ψ.2 m).congr' ?_
    filter_upwards [eventually_ge_atTop (Nat.ceil R)] with n hn
    have hn' : R ≤ (n : ℝ) + 1 := by
      have h1 : R ≤ (Nat.ceil R : ℝ) := Nat.le_ceil R
      have h2 : (Nat.ceil R : ℝ) ≤ (n : ℝ) := by exact_mod_cast hn
      linarith
    have e : (fun y => sa16y3_cutmol d n ψ.1 y - ψ.1 y) = (fun y => sa16q_mol n ψ.1 y - ψ.1 y) := by
      rw [sa16y3_cutmol_eq_of_supp hzero n hn']
    rw [e]
  have hT : Tendsto (fun n => (eLpNorm (fun x => ‖wJet m (fun y => sa16y3_cutmol d n ψ.1 y - ψ.1 y) x‖)
      (ENNReal.ofReal p) volume).toReal) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp hE
    rw [ENNReal.toReal_zero] at this
    exact this
  refine hT.congr' (Eventually.of_forall fun n => ?_)
  exact (hnorm n).symm


theorem sa16y3_T_tendsto {p : ℝ} [Fact (2 ≤ p)] (hp : 1 ≤ p) (m : ℕ) {C : ℝ} (hC0 : 0 ≤ C)
    (T : ℕ → (WmpSpace d m p →L[ℝ] WmpSpace d m p)) (hT : ∀ n, ‖T n‖ ≤ C)
    (hTJ : ∀ (n : ℕ) (ψ : ccSub d), T n (sa16r_Jcc d m p ψ) = sa16r_J d m p (sa16y3_Lop m p n ψ))
    (G : WmpSpace d m p) :
    Tendsto (fun n => ‖T n G - G‖) atTop (𝓝 0) := by
  rw [Metric.tendsto_nhds]
  intro ε hε
  have hδ : (0 : ℝ) < ε / (2 * (C + 1)) := div_pos hε (by linarith)
  obtain ⟨ψ, hψ⟩ := (sa16r_Jcc_dense d m p).exists_dist_lt G hδ
  have hJ := sa16y3_T_Jcc_tendsto hp m T hTJ ψ
  filter_upwards [hJ.eventually (gt_mem_nhds (half_pos hε))] with n hn
  have hGJ : ‖G - sa16r_Jcc d m p ψ‖ < ε / (2 * (C + 1)) := by
    rw [← dist_eq_norm]; exact hψ
  have hid : (C + 1) * (ε / (2 * (C + 1))) = ε / 2 := by
    field_simp
  have e : T n G - G = T n (G - sa16r_Jcc d m p ψ) + (T n (sa16r_Jcc d m p ψ) - sa16r_Jcc d m p ψ) +
      (sa16r_Jcc d m p ψ - G) := by
    rw [map_sub]; abel
  have hTG : ‖T n (G - sa16r_Jcc d m p ψ)‖ ≤ C * (ε / (2 * (C + 1))) :=
    ((T n).le_opNorm _).trans (mul_le_mul (hT n) hGJ.le (norm_nonneg _) hC0)
  have hJG : ‖sa16r_Jcc d m p ψ - G‖ < ε / (2 * (C + 1)) := by
    rw [norm_sub_rev]; exact hGJ
  have htri : ‖T n G - G‖ ≤ ‖T n (G - sa16r_Jcc d m p ψ)‖ +
      ‖T n (sa16r_Jcc d m p ψ) - sa16r_Jcc d m p ψ‖ + ‖sa16r_Jcc d m p ψ - G‖ := by
    rw [e]; exact norm_add₃_le
  rw [Real.dist_eq, sub_zero, abs_of_nonneg (norm_nonneg _)]
  nlinarith [htri, hTG, hJG, hn, hid]

end HRS.Whole.AppendixA.Phase2SA16R
