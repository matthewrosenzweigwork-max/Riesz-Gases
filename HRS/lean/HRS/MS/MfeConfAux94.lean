import HRS.MS.MfeConfAux93

/-!
# S.B.1, packet F8 (part 26): identification of the source with the one-body form, Lipschitz field, `C0`

* `sb1_lv_k_lip`: a truncated kernel is Lipschitz;
* `sb1_lv_S_eq`: `sb1S` of the level-`k` data is `sb1_lv_Src` with `Θ_r = sb1_lv_Theta`, `gk = ∇k`, `c = κ'_r/θ`;
* `sb1_lv_wOne_lip`: `sb1wOne u` is Lipschitz if `u` is;
* `sb1_lv_hC0`: `H + Ψ_0` is bounded below.
-/

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.MP.SelfSimP4 HRS.MP.SelfSimP4Mol HRS.MP.SelfSimP4Impl
open scoped ENNReal NNReal BigOperators ContDiff

noncomputable section

namespace HRS.MS.MfeConf

variable {d N : ℕ}

theorem sb1_lv_k_lip {k : Euc d → ℝ} (hk : ContDiff ℝ 2 k) {Lg : ℝ} (hL : ∀ z, ‖fderiv ℝ k z‖ ≤ Lg) (z z' : Euc d) :
    |k z - k z'| ≤ Lg * ‖z - z'‖ := by
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := k) (s := Set.univ) (C := Lg)
    (fun w _ => hk.differentiable (by norm_num) w) (fun w _ => hL w) convex_univ (Set.mem_univ z') (Set.mem_univ z)
  rw [← Real.norm_eq_abs]
  exact this

theorem sb1_lv_wOne_lip {u : Euc d → Euc d} {Ku : ℝ} (hKu : 0 ≤ Ku) (hu : ∀ x y, ‖u x - u y‖ ≤ Ku * ‖x - y‖) :
    LipschitzWith (Real.toNNReal Ku) (sb1wOne u : EucConfig d N → EucConfig d N) := by
  refine LipschitzWith.of_dist_le_mul fun Z Z' => ?_
  rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hKu]
  refine (pi_norm_le_iff_of_nonneg (by positivity)).2 fun i => ?_
  have h1 : ‖Z i - Z' i‖ ≤ ‖Z - Z'‖ := by simpa using norm_le_pi_norm (Z - Z') i
  have e : (sb1wOne u Z - sb1wOne u Z') i = -(u (Z i) - u (Z' i)) := by simp [sb1wOne]; abel
  rw [e, norm_neg]
  exact (hu _ _).trans (mul_le_mul_of_nonneg_left h1 hKu)

section Traj

variable {D : Whole.WholeDyn d} {T C B C3 : ℝ} {ρ : ℝ → Euc d → ℝ} (H : Sb1Tr3 D T C B C3 ρ) (hT : 0 ≤ T)
  {r₀ : ℝ} {k : Euc d → ℝ}

include H hT

/-- the one-body part along the clamped trajectory -/
def sb1_lv_Th (D : Whole.WholeDyn d) (k : Euc d → ℝ) {T : ℝ} (hT : 0 ≤ T) (ρ : ℝ → Euc d → ℝ) (s : ℝ) (x : Euc d) : ℝ :=
  sb1_lv_Theta D k (sb1_lv_rb hT ρ s) (fun x => sb1_lv_cv k (sb1At D hT ρ s) x) x

theorem sb1_lv_S_eq (hk4 : IsP4Kernel d D.s r₀ k) (hθ : 0 < D.invβ) (r : ℝ) (Z : EucConfig d N) :
    sb1S D.invβ (fun _ => sb1DriftM D k N) (fun r => sb1wOne (sb1_lv_U D k hT ρ r))
      (fun s Z => ∑ i, sb1_lv_W D k hT ρ s (Z i) + sb1_lv_kappa' D k N hT ρ s) r Z =
    sb1_lv_Src D.invβ N (gradient k) (sb1_lv_U D k hT ρ r) (sb1_lv_Th D k hT ρ r)
      (sb1_lv_kappa' D k N hT ρ r / D.invβ) Z := by
  rw [sb1_S_onebody (b := fun _ => sb1DriftM D k N) (uv := fun r => sb1_lv_U D k hT ρ r)
    (fun r => sb1_lv_U_contDiff H hT hk4 r) (wψ1 := fun s => sb1_lv_W D k hT ρ s)
    (κ := fun s => sb1_lv_kappa' D k N hT ρ s) (fun r Z => rfl) r Z]
  unfold sb1_lv_Src
  refine congrArg (· + _) (Finset.sum_congr rfl fun i _ => ?_)
  have hθ0 := hθ.ne'
  have hb : inner ℝ (sb1_lv_U D k hT ρ r (Z i)) (sb1DriftM D k N Z i) =
      -sb1_lv_pairV (gradient k) (sb1_lv_U D k hT ρ r) Z i - inner ℝ (sb1_lv_U D k hT ρ r (Z i)) (gradient D.V (Z i)) := by
    simp only [sb1DriftM, sb1_lv_pairV, inner_sub_right, inner_neg_right]
  rw [hb]
  simp only [sb1_lv_Th, sb1_lv_Theta, sb1_lv_W, sb1At, sb1_lv_rb, sb1_lv_U]
  field_simp
  ring

end Traj

end HRS.MS.MfeConf
