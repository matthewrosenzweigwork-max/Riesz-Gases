import HRS.MS.MfeConfAux112

/-!
# S.B.1, packet F9 (part 16): the signed limit of the commutator mean `∫ C^M dμ^M → ∫ C dμ`

`sb1_Cmean_limit`: let `Y^M → X` pathwise (eventually equal, `X` collision-free a.s.), the laws `μ^M` of `Y^M` dominated by the
unnormalised regularised Gibbs measures `c e^{-β H_M} dX` (canonical-Gibbs domination, `sb1_flow_dom`), `u = v_r` Lipschitz and
`ρ_r` a regular density.  Then `C_r(X)` is integrable and `E C^M_r(Y^M) → E C_r(X)` (Vitali + the envelope and tail estimates).
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_meas_fderiv_clm {α : Type*} [MeasurableSpace α] (g : Euc d → ℝ) {z w : α → Euc d}
    (hz : Measurable z) (hw : Measurable w) : Measurable fun a => fderiv ℝ g (z a) (w a) := by
  have e : (fun a => fderiv ℝ g (z a) (w a)) = fun a => ∑ k, w a k * fderiv ℝ g (z a) (sb1e k) :=
    funext fun a => sb1_clm_expand _ _
  rw [e]
  exact Finset.measurable_sum _ fun k _ =>
    (((PiLp.continuous_apply 2 (fun _ : Fin d => ℝ) k).measurable.comp hw)).mul
      ((measurable_fderiv_apply_const ℝ g (sb1e k)).comp hz)

theorem sb1_meas_hk (g : Euc d → ℝ) {u : Euc d → Euc d} (hu : Measurable u) :
    Measurable (fun p : Euc d × Euc d => sb1hk g u p.1 p.2) :=
  sb1_meas_fderiv_clm g (measurable_fst.sub measurable_snd)
    ((hu.comp measurable_fst).sub (hu.comp measurable_snd))

theorem sb1_Hs_eq (D : Whole.WholeDyn d) (k : Euc d → ℝ) (hN : 1 ≤ N) (Z : Whole.EucConfig d N) :
    sb1Hs D k N Z = (N : ℝ) * sb1PM k N Z + ∑ i, D.V (Z i) := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold sb1Hs sb1PM p4k_pairSum
  field_simp

theorem sb1_ell_le (hN : 1 ≤ N) (Z : Whole.EucConfig d N) : sb1ell d N Z ≤ ‖Z‖ + 1 / 2 := by
  have hn : (0 : ℝ) < N := by exact_mod_cast hN
  unfold sb1ell
  have hterm : ∀ i j : Fin N, Real.log (1 + ‖Z i - Z j‖) + 1 ≤ 2 * ‖Z‖ + 1 := by
    intro i j
    have h3 : ‖Z i - Z j‖ ≤ 2 * ‖Z‖ := by
      calc ‖Z i - Z j‖ ≤ ‖Z i‖ + ‖Z j‖ := norm_sub_le _ _
        _ ≤ ‖Z‖ + ‖Z‖ := add_le_add (norm_le_pi_norm Z i) (norm_le_pi_norm Z j)
        _ = 2 * ‖Z‖ := by ring
    have := sb1_log_le_norm (Z i - Z j)
    linarith
  have hsum : ∑ i : Fin N, ∑ j ∈ Finset.univ.erase i, (Real.log (1 + ‖Z i - Z j‖) + 1) ≤ (N : ℝ) ^ 2 * (2 * ‖Z‖ + 1) := by
    have hnn : 0 ≤ 2 * ‖Z‖ + 1 := by positivity
    have : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, (Real.log (1 + ‖Z i - Z j‖) + 1) ≤ (N : ℝ) * (2 * ‖Z‖ + 1) := by
      intro i
      calc _ ≤ ∑ _j ∈ Finset.univ.erase i, (2 * ‖Z‖ + 1) := Finset.sum_le_sum fun j _ => hterm i j
        _ ≤ (N : ℝ) * (2 * ‖Z‖ + 1) := by
          rw [Finset.sum_const, Finset.card_erase_of_mem (Finset.mem_univ i)]
          simp only [Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
          have : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast Nat.sub_le N 1
          exact mul_le_mul_of_nonneg_right this hnn
    calc _ ≤ ∑ _i : Fin N, (N : ℝ) * (2 * ‖Z‖ + 1) := Finset.sum_le_sum fun i _ => this i
      _ = (N : ℝ) ^ 2 * (2 * ‖Z‖ + 1) := by simp; ring
  calc (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, (Real.log (1 + ‖Z i - Z j‖) + 1)
      ≤ (1 / (2 * (N : ℝ) ^ 2)) * ((N : ℝ) ^ 2 * (2 * ‖Z‖ + 1)) :=
        mul_le_mul_of_nonneg_left hsum (by positivity)
    _ = ‖Z‖ + 1 / 2 := by field_simp

end HRS.MS.MfeConf
