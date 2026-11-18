import HRS.MS.SA16SOp3

/-!
# S.A.16 (SA16S) Op4: the Laplacian `Δ : W^{k+2,p} → W^{k,p}` and its weak identity
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16 Phase2SA16Evolution Phase2SA16Transfer

section Op4
variable {d : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- the constant of the Laplacian estimate -/
def sa16so_cL (d k : ℕ) : ℝ := ((k : ℝ) + 1) * ((d : ℝ) * ((d : ℝ) + 1) ^ (k + 2))

lemma sa16so_lap_jet (k : ℕ) {φ : Euc d → ℝ} (hφ : ContDiff ℝ ∞ φ) (x : Euc d) :
    ‖wJet k (sa16r_lap φ) x‖ ≤ sa16so_cL d k * ‖wJet (k + 2) φ x‖ := by
  refine (sa16j_jet_norm_le k _ x).trans ?_
  have hJ0 := norm_nonneg (wJet (k + 2) φ x)
  have hdir : ∀ i : Fin d, ContDiff ℝ ∞ (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) :=
    fun i => sa16so_dir_smooth hφ _
  have hterm : ∀ j ∈ Finset.range (k + 1), ‖iteratedFDeriv ℝ j (sa16r_lap φ) x‖ ≤
      (d : ℝ) * (((d : ℝ) + 1) ^ (k + 2) * ‖wJet (k + 2) φ x‖) := by
    intro j hj
    have hj' : j ≤ k := by have := Finset.mem_range.1 hj; omega
    have hfun : sa16r_lap φ = fun y => ∑ i : Fin d, fderiv ℝ (fun y => fderiv ℝ φ y
        (EuclideanSpace.single i 1)) y (EuclideanSpace.single i 1) := rfl
    rw [hfun, iteratedFDeriv_fun_sum_apply (fun i _ => ((sa16so_dir_smooth (hdir i)
      (EuclideanSpace.single i 1)).contDiffAt).of_le (by exact_mod_cast le_top))]
    refine (norm_sum_le _ _).trans ?_
    calc ∑ i : Fin d, ‖iteratedFDeriv ℝ j (fun y => fderiv ℝ (fun y => fderiv ℝ φ y
            (EuclideanSpace.single i 1)) y (EuclideanSpace.single i 1)) x‖
        ≤ ∑ i : Fin d, ((d : ℝ) + 1) ^ (k + 2) * ‖wJet (k + 2) φ x‖ := by
          refine Finset.sum_le_sum fun i _ => ?_
          have h1 := sa16so_norm_iter_dir (hdir i) (EuclideanSpace.single i 1) j x
          have h2 := sa16so_norm_iter_dir hφ (EuclideanSpace.single i 1) (j + 1) x
          rw [PiLp.norm_single, norm_one, one_mul] at h1 h2
          have h3 := sa16y_iter_le_jet φ x (n := k + 2) (l := j + 2) (by omega)
          have h4 : ((d : ℝ)) ^ (j + 2) ≤ ((d : ℝ) + 1) ^ (k + 2) := by
            calc ((d : ℝ)) ^ (j + 2) ≤ ((d : ℝ) + 1) ^ (j + 2) :=
                  pow_le_pow_left₀ (Nat.cast_nonneg d) (by linarith) _
              _ ≤ ((d : ℝ) + 1) ^ (k + 2) :=
                  pow_le_pow_right₀ (by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith) (by omega)
          calc _ ≤ ‖iteratedFDeriv ℝ (j + 1) (fun y => fderiv ℝ φ y (EuclideanSpace.single i 1)) x‖ := h1
            _ ≤ ‖iteratedFDeriv ℝ (j + 1 + 1) φ x‖ := h2
            _ ≤ _ := h3.trans (mul_le_mul_of_nonneg_right h4 hJ0)
      _ = _ := by simp
  refine (Finset.sum_le_sum hterm).trans ?_
  simp only [Finset.sum_const, Finset.card_range, nsmul_eq_mul]
  unfold sa16so_cL
  push_cast
  ring_nf
  exact le_refl _

/-- the linear map `φ ↦ Δφ` on `C_c^∞` -/
def sa16so_lapL (d : ℕ) : ccSub d →ₗ[ℝ] (Euc d → ℝ) where
  toFun φ := sa16r_lap φ.1
  map_add' φ ψ := by
    funext x
    have h1 : ContDiffAt ℝ 2 φ.1 x := (φ.2.1.of_le (by simp)).contDiffAt
    have h2 : ContDiffAt ℝ 2 ψ.1 x := (ψ.2.1.of_le (by simp)).contDiffAt
    have h3 : ContDiff ℝ ∞ (φ.1 + ψ.1) := φ.2.1.add ψ.2.1
    show sa16r_lap (φ.1 + ψ.1) x = sa16r_lap φ.1 x + sa16r_lap ψ.1 x
    rw [sa16sw_lap_eq h3, sa16sw_lap_eq φ.2.1, sa16sw_lap_eq ψ.2.1]
    exact h1.laplacian_add h2
  map_smul' c φ := by
    funext x
    have h1 : ContDiffAt ℝ 2 φ.1 x := (φ.2.1.of_le (by simp)).contDiffAt
    have h3 : ContDiff ℝ ∞ (c • φ.1) := φ.2.1.const_smul c
    show sa16r_lap (c • φ.1) x = c * sa16r_lap φ.1 x
    rw [sa16sw_lap_eq h3, sa16sw_lap_eq φ.2.1]
    simpa using InnerProductSpace.laplacian_smul c h1

theorem sa16so_lap_exists (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] :
    ∃ T : WmpSpace d (k + 2) p →L[ℝ] WmpSpace d k p, ‖T‖ ≤ sa16so_cL d k ∧
      ∀ φ : ccSub d, wrep d k p (T (sa16r_Jcc d (k + 2) p φ)) =ᵐ[volume] sa16r_lap φ.1 := by
  refine sa16so_extend d k (k + 2) p (sa16so_lapL d) (fun φ => (sa16sw_cc_lap φ.2).1) ?_
    (fun φ x => sa16so_lap_jet k φ.2.1 x)
  unfold sa16so_cL; positivity

open Classical in
/-- the Laplacian on `W^{k+2,p}` with values in `W^{k,p}` -/
def sa16so_Lap (d k : ℕ) (p : ℝ) [Fact (2 ≤ p)] : WmpSpace d (k + 2) p →L[ℝ] WmpSpace d k p :=
  Classical.choose (sa16so_lap_exists d k p)

lemma sa16so_Lap_norm (k : ℕ) : ‖sa16so_Lap d k p‖ ≤ sa16so_cL d k :=
  (Classical.choose_spec (sa16so_lap_exists d k p)).1

lemma sa16so_Lap_Jcc (k : ℕ) (φ : ccSub d) :
    wrep d k p (sa16so_Lap d k p (sa16r_Jcc d (k + 2) p φ)) =ᵐ[volume] sa16r_lap φ.1 :=
  (Classical.choose_spec (sa16so_lap_exists d k p)).2 φ

/-- weak identity of the Laplacian: `ℓ_ψ(Δ G) = ℓ_{Δψ}(G)` -/
theorem sa16so_ell_Lap (k : ℕ) {ψ : Euc d → ℝ} (hψ : IsCcInfty ψ) (G : WmpSpace d (k + 2) p) :
    sa16r_ell d k p hψ (sa16so_Lap d k p G) = sa16r_ell d (k + 2) p (sa16sw_cc_lap hψ) G := by
  refine (sa16r_Jcc_dense d (k + 2) p).induction_on G (isClosed_eq ?_ ?_) (fun φ => ?_)
  · exact (sa16r_ell d k p hψ).continuous.comp (sa16so_Lap d k p).continuous
  · exact (sa16r_ell d (k + 2) p (sa16sw_cc_lap hψ)).continuous
  · rw [sa16r_Jcc_eq, sa16r_ell_apply, sa16r_ell_apply]
    have hφ := φ.2
    have e1 : ∫ x, wrep d k p (sa16so_Lap d k p (sa16r_cc_elt hφ (k + 2))) x * ψ x =
        ∫ x, sa16r_lap φ.1 x * ψ x := by
      refine integral_congr_ae ?_
      have := sa16so_Lap_Jcc (p := p) k φ
      rw [sa16r_Jcc_eq] at this
      filter_upwards [this] with x hx
      rw [hx]
    have e2 : ∫ x, wrep d (k + 2) p (sa16r_cc_elt hφ (k + 2)) x * sa16r_lap ψ x =
        ∫ x, φ.1 x * sa16r_lap ψ x := by
      refine integral_congr_ae ?_
      filter_upwards [sa16r_cc_elt_wrep (p := p) hφ (k + 2)] with x hx
      rw [hx]
    rw [e1, e2]
    exact sa16sw_green hφ.1 hψ

end Op4

end HRS.Whole.AppendixA.Phase2SA16R
