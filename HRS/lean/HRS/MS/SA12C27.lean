import HRS.MS.SA12C26

/-!
# S.A.12(c), packet E7.04 (part 11): `κ = ρ` a.e. on the cell, `L¹`-bound of `μ ∂_jF`, first jets
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12C

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.AdjointRd
open HRS.MH.AdjointRd.Phase2SA12Construction HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Near

variable {d : ℕ}

/-- `κ = ρ` a.e. on the cell `W`. -/
theorem sa12c_kap_ae_rho {s L c0 : ℝ} (hd : 1 ≤ d) (hL : 40 ≤ L) {q χ χh γ : Euc d → ℝ}
    (hχ : IsCutoffPair χ χh) (hq : ContDiff ℝ ∞ q)
    (hΘ : ∀ z : Euc d, z ≠ 0 → ‖z‖ < 4 → γ z = rieszKernel d s z + sa12cTh s L c0 q z)
    {n : ℕ} (β : Fin n → Fin d) (v : Euc d) (hv : ‖v‖ < 2) :
    ∀ᵐ z ∂(volume.restrict (sa12cWcell d L)),
      sa12cKap s L c0 q χ χh γ β v z = sa12cRho s χh γ β v z := by
  haveI : Nonempty (Fin d) := ⟨⟨0, hd⟩⟩
  have hne : ∀ᵐ z ∂(volume : Measure (Euc d)), z ≠ 0 := compl_mem_ae_iff.2 (measure_singleton (0 : Euc d))
  have hsph : ∀ᵐ z ∂(volume : Measure (Euc d)), ‖z‖ ≠ 4 := by
    have h0 : (volume : Measure (Euc d)) (Metric.sphere (0 : Euc d) 4) = 0 := Measure.addHaar_sphere _ _ _
    filter_upwards [compl_mem_ae_iff.2 h0] with z hz h4
    apply hz
    simpa using h4
  refine (ae_restrict_iff' (sa12c_W_meas (d := d) L)).2 ?_
  filter_upwards [hne, hsph] with z hz0 hz4 hz
  have hzc : ∀ i, |z i| < 3 * L / 5 := fun i => by
    have := sa12c_W_sub_cube L hz i
    linarith
  exact sa12c_deriv_kernel hL hχ hq hΘ β v z hv hz0 hz4 hzc

/-- `(∫_Q |μ ∂_jF|)² ≤ (∫_Q μ²)(∫_Q (∂_jF)²)`. -/
theorem sa12c_L1_bound {L : ℝ} (hL : 0 < L) {μ G : Euc d → ℝ} (hμ : Continuous μ) (hG : Continuous G) :
    (∫ x in periodBox d L, |μ x * G x|) ^ 2 ≤
      (∫ x in periodBox d L, μ x ^ 2) * ∫ x in periodBox d L, G x ^ 2 := by
  have hI : ∀ f : Euc d → ℝ, Continuous f → IntegrableOn f (periodBox d L) := fun f hf =>
    sa12v_integrableOn_box L hf
  have h := sa12c_cs (μ := volume.restrict (periodBox d L)) (a := fun x => |μ x|) (b := fun x => |G x|)
    (by simp_rw [sq_abs]; exact hI _ (hμ.pow 2)) (by simp_rw [sq_abs]; exact hI _ (hG.pow 2))
    (by simp_rw [← abs_mul]; exact (hI _ (hμ.mul hG)).norm)
  simp_rw [sq_abs, ← abs_mul] at h
  exact h

/-- The first jets are controlled by the box energy (`m ≥ 1`). -/
theorem sa12c_first_jet_le {m : ℕ} (hm : 1 ≤ m) (L : ℝ) {F : Euc d → ℝ} (hF : ContDiff ℝ ∞ F) (j : Fin d) :
    ∫ x in periodBox d L, (fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ))) ^ 2 ≤ boxEnergy m L F := by
  unfold boxEnergy
  have hnn : ∀ k, 0 ≤ (Nat.choose m k : ℝ) * ∑ idx : Fin k → Fin d,
      ∫ x in periodBox d L, (partialDeriv idx F x) ^ 2 := fun k =>
    mul_nonneg (Nat.cast_nonneg _) (Finset.sum_nonneg fun idx _ =>
      setIntegral_nonneg (sa12c20_box_meas L) fun x _ => sq_nonneg _)
  have h1 : (Nat.choose m 1 : ℝ) * ∑ idx : Fin 1 → Fin d, ∫ x in periodBox d L, (partialDeriv idx F x) ^ 2 ≤
      ∑ k ∈ Finset.range (m + 1), (Nat.choose m k : ℝ) * ∑ idx : Fin k → Fin d,
        ∫ x in periodBox d L, (partialDeriv idx F x) ^ 2 :=
    Finset.single_le_sum (f := fun k => (Nat.choose m k : ℝ) * ∑ idx : Fin k → Fin d,
      ∫ x in periodBox d L, (partialDeriv idx F x) ^ 2) (fun k _ => hnn k)
      (Finset.mem_range.2 (by omega))
  refine le_trans ?_ h1
  have hc : (1 : ℝ) ≤ (Nat.choose m 1 : ℝ) := by
    have : 1 ≤ Nat.choose m 1 := Nat.choose_pos hm
    exact_mod_cast this
  have h2 : ∫ x in periodBox d L, (partialDeriv (fun _ : Fin 1 => j) F x) ^ 2 ≤
      ∑ idx : Fin 1 → Fin d, ∫ x in periodBox d L, (partialDeriv idx F x) ^ 2 :=
    Finset.single_le_sum (f := fun idx : Fin 1 → Fin d => ∫ x in periodBox d L, (partialDeriv idx F x) ^ 2)
      (fun idx _ => setIntegral_nonneg (sa12c20_box_meas L) fun x _ => sq_nonneg _) (Finset.mem_univ _)
  have h3 : ∀ x, partialDeriv (fun _ : Fin 1 => j) F x = fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ)) := by
    intro x
    unfold partialDeriv
    simp [iteratedFDeriv_one_apply]
  simp_rw [h3] at h2
  have hs : 0 ≤ ∑ idx : Fin 1 → Fin d, ∫ x in periodBox d L, (partialDeriv idx F x) ^ 2 :=
    Finset.sum_nonneg fun idx _ => setIntegral_nonneg (sa12c20_box_meas L) fun x _ => sq_nonneg _
  nlinarith

theorem sa12cKap_continuous {s L c0 : ℝ} (hL : 0 < L) {q χ χh γ : Euc d → ℝ} (hχ : IsCutoffPair χ χh)
    (hq : ContDiff ℝ ∞ q) (hγ : IsPeriodicRieszKernel d s L γ) {n : ℕ} (β : Fin n → Fin d) (v : Euc d) :
    Continuous (fun z => sa12cKap s L c0 q χ χh γ β v z) := by
  have hAs : ContDiff ℝ ∞ (sa12cA s L c0 q χ γ) := sa12cA_contDiff hL hq hχ hγ
  have hBs : ContDiff ℝ ∞ (sa12cB s L χ) := sa12cB_contDiff hL hχ
  unfold sa12cKap
  exact (sa12z3_pd_contDiff_inf hAs β).continuous.sub
    ((hχ.2.1.continuous.comp (continuous_const.sub continuous_id)).mul
      (sa12z3_pd_contDiff_inf hBs β).continuous)

end HRS.MH.AdjointRd.Phase2SA12C
