import HRS.MS.SA16Y3Ex5

/-!
# S.A.16 (SA16Y3) Ex6: convergence of the cut-off extensions on `WmpSpace` (SA16S item (iii), step (d1))

`sa16y3_pd_sub_smooth`: `∂^κ (f - g) = ∂^κ f - ∂^κ g` for smooth `f, g`.
`sa16y3_jet_sub_tendsto`: `‖J_m (mol_n ψ - ψ)‖_{L^p} → 0` for `ψ ∈ C_c^∞`.
`sa16y3_Lop_eq`: `sa16r_J (Lop n ψ) = Jcc (cutmol n ψ)`.
`sa16y3_T_tendsto`: `‖T_n G - G‖ → 0` for every `G ∈ WmpSpace` (uniform bound `‖T_n‖ ≤ C`, convergence on `Jcc`).
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal ContDiff Pointwise

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Q Phase2SA16Evolution

variable {d : ℕ}

lemma sa16y3_pd_sub_smooth {f g : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ ∞ f) (hg : ContDiff ℝ ∞ g)
    {j : ℕ} (κ : Fin j → Fin d) (x : EuclideanSpace ℝ (Fin d)) :
    partialDeriv κ (fun y => f y - g y) x = partialDeriv κ f x - partialDeriv κ g x := by
  unfold partialDeriv
  rw [show (fun y => f y - g y) = f - g from rfl, iteratedFDeriv_sub_apply (hf.contDiffAt.of_le (by simp)) (hg.contDiffAt.of_le (by simp))]
  rfl

lemma sa16y3_pd_cont {f : EuclideanSpace ℝ (Fin d) → ℝ} (hf : ContDiff ℝ ∞ f) {m : ℕ} (τ : WIndex d m) :
    Continuous (partialDeriv τ.2 f) :=
  (continuous_apply τ).comp (sa16j_jet_cont hf m)

lemma sa16y3_cutmol_eq_of_supp {ψ : EuclideanSpace ℝ (Fin d) → ℝ} {R : ℝ} (hR : ∀ x, R < ‖x‖ → ψ x = 0)
    (n : ℕ) (hn : R ≤ (n : ℝ) + 1) : sa16y3_cutmol d n ψ = sa16q_mol n ψ := by
  funext x
  unfold sa16y3_cutmol
  congr 1
  funext z
  by_cases hz : ‖z‖ ≤ (n : ℝ) + 1
  · have h1 : sa16y3_cut d n z = 1 := by
      unfold sa16y3_cut
      exact sa16j_chi_one d (by positivity) hz
    rw [h1, one_mul]
  · have h1 : ψ z = 0 := hR z (lt_of_le_of_lt hn (not_le.1 hz))
    rw [h1, mul_zero]

lemma sa16y3_jet_sub_tendsto {p : ℝ} (hp : 1 ≤ p) {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ)
    (m : ℕ) :
    Tendsto (fun n : ℕ => eLpNorm (fun x => ‖wJet m (fun y => sa16q_mol n ψ y - ψ y) x‖) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
  -- coordinatewise bound
  have hmolc : ∀ n : ℕ, ContDiff ℝ ∞ (sa16q_mol n ψ) := fun n =>
    sa16y3_conv_contDiff (sa16y_rho_integrable n).locallyIntegrable hψ
  have hsum : ∀ n : ℕ, ∀ x, ‖wJet m (fun y => sa16q_mol n ψ y - ψ y) x‖ ≤
      ∑ τ : WIndex d m, ‖partialDeriv τ.2 (sa16q_mol n ψ) x - partialDeriv τ.2 ψ x‖ := by
    intro n x
    refine (pi_norm_le_iff_of_nonneg (Finset.sum_nonneg fun _ _ => norm_nonneg _)).2 fun τ => ?_
    have e : partialDeriv τ.2 (fun y => sa16q_mol n ψ y - ψ y) x =
        partialDeriv τ.2 (sa16q_mol n ψ) x - partialDeriv τ.2 ψ x :=
      sa16y3_pd_sub_smooth (hmolc n) hψ.1 τ.2 x
    show ‖partialDeriv τ.2 (fun y => sa16q_mol n ψ y - ψ y) x‖ ≤ _
    rw [e]
    exact Finset.single_le_sum (f := fun τ : WIndex d m =>
      ‖partialDeriv τ.2 (sa16q_mol n ψ) x - partialDeriv τ.2 ψ x‖) (fun _ _ => norm_nonneg _) (Finset.mem_univ τ)
  have hp1 : (1 : ENNReal) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 hp
  have hsumE : ∀ n : ℕ, eLpNorm (fun x => ‖wJet m (fun y => sa16q_mol n ψ y - ψ y) x‖) (ENNReal.ofReal p) volume ≤
      ∑ τ : WIndex d m, eLpNorm (fun x => ‖partialDeriv τ.2 (sa16q_mol n ψ) x - partialDeriv τ.2 ψ x‖)
        (ENNReal.ofReal p) volume := by
    intro n
    have hcont : Continuous (fun y => sa16q_mol n ψ y - ψ y) :=
      (hmolc n).continuous.sub hψ.1.continuous
    calc eLpNorm (fun x => ‖wJet m (fun y => sa16q_mol n ψ y - ψ y) x‖) (ENNReal.ofReal p) volume
        ≤ eLpNorm (fun x => ∑ τ : WIndex d m, ‖partialDeriv τ.2 (sa16q_mol n ψ) x - partialDeriv τ.2 ψ x‖)
            (ENNReal.ofReal p) volume :=
          eLpNorm_mono_real ((sa16j_jet_cont ((hmolc n).sub hψ.1) m).norm.aestronglyMeasurable)
            (fun x => by rw [norm_norm]; exact hsum n x)
      _ = eLpNorm (∑ τ : WIndex d m, fun x => ‖partialDeriv τ.2 (sa16q_mol n ψ) x - partialDeriv τ.2 ψ x‖)
            (ENNReal.ofReal p) volume := by
          congr 1
          funext x
          simp [Finset.sum_apply]
      _ ≤ ∑ τ : WIndex d m, eLpNorm (fun x => ‖partialDeriv τ.2 (sa16q_mol n ψ) x - partialDeriv τ.2 ψ x‖)
            (ENNReal.ofReal p) volume := eLpNorm_sum_le hp1
  have hlim : ∀ τ : WIndex d m, Tendsto (fun n : ℕ =>
      eLpNorm (fun x => ‖partialDeriv τ.2 (sa16q_mol n ψ) x - partialDeriv τ.2 ψ x‖) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
    intro τ
    have h := sa16y3_mol_tendsto_Lp hp hψ τ.2
    refine h.congr' (Eventually.of_forall fun n => ?_)
    have hc : Continuous (partialDeriv τ.2 (sa16q_mol n ψ) - partialDeriv τ.2 ψ) :=
      (sa16y3_pd_cont (hmolc n) τ).sub (sa16y3_pd_cont hψ.1 τ)
    exact (eLpNorm_norm _ hc.aestronglyMeasurable).symm
  have hsumT : Tendsto (fun n : ℕ => ∑ τ : WIndex d m,
      eLpNorm (fun x => ‖partialDeriv τ.2 (sa16q_mol n ψ) x - partialDeriv τ.2 ψ x‖) (ENNReal.ofReal p) volume)
      atTop (𝓝 0) := by
    have := tendsto_finset_sum (Finset.univ : Finset (WIndex d m)) (fun τ _ => hlim τ)
    simpa using this
  exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsumT
    (fun _ => bot_le) hsumE

end HRS.Whole.AppendixA.Phase2SA16R
