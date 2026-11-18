import HRS.MS.S104eC0
import HRS.MS.UlTailAux2

/-!
# S104E route C, packet C2, part A: the near part of the cancellation operator for Hölder data

Prefix `s104c2_`, namespace `HRS.MS.S104e.C`.  `HolNear η H g`: `g` is `η`-Hölder with constant `H` on the near range `‖a - b‖ ≤ 1/4`.
The existing near-part theory (`UlTailAux1`: `ultNear`, `ult_near_iter`) needs Lipschitz derivatives; here the top derivative is only Hölder, with
`η > s + 1 - d` so that `‖z‖^{-(s+1)} ‖z‖^η` is integrable near `0`:

* `s104c2_near_integrable`, `s104c2_near_continuous`, `s104c2_near_hasFDerivAt`: Hölder versions;
* `s104c2_near_iter`: `D^m (ultNear κ k) = ultNear κ (D^m k)` for `m ≤ j` and `ultNear κ k ∈ C^j`, if every `D^m k` (`m ≤ j`) is `η`-Hölder near.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000

namespace HRS.MS.S104e.C

open HRS HRS.Whole HRS.MS.Ul

variable {d : ℕ}

/-- `g` is `η`-Hölder with constant `H` on the near range `‖a - b‖ ≤ 1/4`. -/
def HolNear {F : Type*} [NormedAddCommGroup F] (η H : ℝ) (g : Euc d → F) : Prop :=
  ∀ a b : Euc d, ‖a - b‖ ≤ 1 / 4 → ‖g a - g b‖ ≤ H * ‖a - b‖ ^ η

/-- The integrable majorant `1_{‖z‖<1} ‖z‖^{-(s+1-η)}` of the near kernel times the Hölder increment. -/
def s104c2_Psi (d : ℕ) (s η : ℝ) : Euc d → ℝ :=
  (ball (0 : Euc d) 1).indicator (fun z => ‖z‖ ^ (-(s + 1 - η)))

lemma s104c2_Psi_nonneg (s η : ℝ) (z : Euc d) : 0 ≤ s104c2_Psi d s η z :=
  Set.indicator_nonneg (fun z _ => Real.rpow_nonneg (norm_nonneg z) _) z

lemma s104c2_Psi_int (hd : 1 ≤ d) {s η : ℝ} (hs0 : 0 ≤ s) (hη1 : η < 1) (hηd : s + 1 - η < (d : ℝ)) :
    Integrable (s104c2_Psi d s η) volume :=
  (integrable_indicator_iff measurableSet_ball).2
    (u2_integrableOn_ball_rpow hd (a := s + 1 - η) (by linarith) hηd)

lemma s104c2_near_dom {κ : Euc d → ℝ} {s C0 η H : ℝ} (hC0 : 0 ≤ C0)
    (hb : ∀ z : Euc d, z ≠ 0 → ‖κ z‖ ≤ C0 * ‖z‖ ^ (-(s + 1))) (hH : 0 ≤ H)
    {G : Type*} [NormedAddCommGroup G] [NormedSpace ℝ G] {w : G} {z : Euc d} (hz : z ≠ 0)
    (hw : ‖z‖ ≤ 1 / 4 → ‖w‖ ≤ H * ‖z‖ ^ η) :
    ‖ultKN κ z • w‖ ≤ C0 * H * s104c2_Psi d s η z := by
  by_cases h : ‖z‖ ≤ 1 / 4
  · have hmem : z ∈ ball (0 : Euc d) 1 := by rw [mem_ball_zero_iff]; linarith
    have hzp : 0 < ‖z‖ := norm_pos_iff.mpr hz
    have hP : s104c2_Psi d s η z = ‖z‖ ^ (-(s + 1 - η)) := Set.indicator_of_mem hmem _
    rw [hP, norm_smul]
    simp only [ultKN, h, ite_true]
    calc ‖κ z‖ * ‖w‖ ≤ (C0 * ‖z‖ ^ (-(s + 1))) * (H * ‖z‖ ^ η) :=
          mul_le_mul (hb z hz) (hw h) (norm_nonneg _) (by positivity)
      _ = C0 * H * ‖z‖ ^ (-(s + 1 - η)) := by
          rw [show -(s + 1 - η) = -(s + 1) + η by ring, Real.rpow_add hzp]; ring
  · simp only [ultKN, h, ite_false, zero_smul, norm_zero]
    exact mul_nonneg (mul_nonneg hC0 hH) (s104c2_Psi_nonneg s η z)

section Near

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma s104c2_near_integrable (hd : 1 ≤ d) {κ : Euc d → ℝ} {s η H : ℝ} (hK : UlKer κ s) (hη1 : η < 1)
    (hηd : s + 1 - η < (d : ℝ)) (hH : 0 ≤ H) {g : Euc d → F} (hg : Continuous g) (hh : HolNear η H g)
    (x : Euc d) : Integrable (fun z => ultKN κ z • (g (x - z) - g x)) volume := by
  obtain ⟨C0, hC0, hb⟩ := ult_ker_bound hK
  refine ((s104c2_Psi_int hd hK.hs0 hη1 hηd).const_mul (C0 * H)).mono' (ult_near_meas hK.meas hg x) ?_
  filter_upwards [u2_ae_ne_zero hd] with z hz
  refine s104c2_near_dom hC0 hb hH hz (fun h1 => ?_)
  have := hh (x - z) x (by simpa using h1)
  simpa using this

lemma s104c2_near_continuous (hd : 1 ≤ d) {κ : Euc d → ℝ} {s η H : ℝ} (hK : UlKer κ s) (hη1 : η < 1)
    (hηd : s + 1 - η < (d : ℝ)) (hH : 0 ≤ H) {g : Euc d → F} (hg : Continuous g) (hh : HolNear η H g) :
    Continuous (ultNear κ g) := by
  obtain ⟨C0, hC0, hb⟩ := ult_ker_bound hK
  refine continuous_iff_continuousAt.2 fun x0 => ?_
  refine MeasureTheory.continuousAt_of_dominated (μ := volume)
    (F := fun x z => ultKN κ z • (g (x - z) - g x))
    (bound := fun z => C0 * H * s104c2_Psi d s η z)
    (Filter.Eventually.of_forall fun x => ult_near_meas hK.meas hg x) ?_
    ((s104c2_Psi_int hd hK.hs0 hη1 hηd).const_mul (C0 * H)) ?_
  · refine Filter.Eventually.of_forall fun x => ?_
    filter_upwards [u2_ae_ne_zero hd] with z hz
    refine s104c2_near_dom hC0 hb hH hz (fun h1 => ?_)
    have := hh (x - z) x (by simpa using h1)
    simpa using this
  · refine Filter.Eventually.of_forall fun z => ?_
    refine (continuous_const.smul ?_).continuousAt
    exact (hg.comp (continuous_id.sub continuous_const)).sub hg

lemma s104c2_near_hasFDerivAt [CompleteSpace F] (hd : 1 ≤ d) {κ : Euc d → ℝ} {s η H : ℝ} (hK : UlKer κ s)
    (hη1 : η < 1) (hηd : s + 1 - η < (d : ℝ)) (hH : 0 ≤ H) {g : Euc d → F} (hg : Differentiable ℝ g)
    (hfc : Continuous (fderiv ℝ g)) (h0 : HolNear η H g) (h1 : HolNear η H (fderiv ℝ g)) (x0 : Euc d) :
    HasFDerivAt (ultNear κ g) (ultNear κ (fun y => fderiv ℝ g y) x0) x0 := by
  obtain ⟨C0, hC0, hb⟩ := ult_ker_bound hK
  have hgc : Continuous g := hg.continuous
  refine hasFDerivAt_integral_of_dominated_of_fderiv_le (μ := volume)
    (F := fun x z => ultKN κ z • (g (x - z) - g x))
    (F' := fun x z => ultKN κ z • (fderiv ℝ g (x - z) - fderiv ℝ g x))
    (x₀ := x0) (s := ball x0 1)
    (bound := fun z => C0 * H * s104c2_Psi d s η z)
    (ball_mem_nhds x0 one_pos) ?_ ?_ ?_ ?_ ((s104c2_Psi_int hd hK.hs0 hη1 hηd).const_mul (C0 * H)) ?_
  · exact Filter.Eventually.of_forall fun x => ult_near_meas hK.meas hgc x
  · exact s104c2_near_integrable hd hK hη1 hηd hH hgc h0 x0
  · exact ult_near_meas hK.meas hfc x0
  · filter_upwards [u2_ae_ne_zero hd] with z hz x _
    refine s104c2_near_dom (G := Euc d →L[ℝ] F) hC0 hb hH hz (fun h1' => ?_)
    have := h1 (x - z) x (by simpa using h1')
    simpa using this
  · refine Filter.Eventually.of_forall fun z x _ => ?_
    have h1' : HasFDerivAt (fun x : Euc d => g (x - z)) (fderiv ℝ g (x - z)) x := by
      have h2' : HasFDerivAt (fun x : Euc d => x - z) (ContinuousLinearMap.id ℝ (Euc d)) x :=
        (hasFDerivAt_id x).sub_const z
      have := HasFDerivAt.comp x (hg (x - z)).hasFDerivAt h2'
      rw [ContinuousLinearMap.comp_id] at this
      exact this
    exact (h1'.sub (hg x).hasFDerivAt).const_smul (ultKN κ z)

end Near

section Iter

lemma s104c2_iter_cd1 {j : ℕ} {k : Euc d → ℝ} (hk : ContDiff ℝ j k) {m : ℕ} (hm : m + 1 ≤ j) :
    ContDiff ℝ 1 (iteratedFDeriv ℝ m k) := by
  have := hk.iteratedFDeriv_right (m := 1) (i := m) (by
    have : ((1 : ℕ) + m : ℕ) ≤ j := by omega
    exact_mod_cast this)
  exact this

lemma s104c2_hol_zero {η H : ℝ} {k : Euc d → ℝ} (hh : HolNear η H (iteratedFDeriv ℝ 0 k)) : HolNear η H k := by
  intro a b hab
  have := hh a b hab
  rw [iteratedFDeriv_zero_eq_comp] at this
  simpa only [Function.comp_apply, ← map_sub, LinearIsometryEquiv.norm_map] using this

lemma s104c2_fderiv_iter_hol {η H : ℝ} {k : Euc d → ℝ} {m : ℕ}
    (hh : HolNear η H (iteratedFDeriv ℝ (m + 1) k)) : HolNear η H (fderiv ℝ (iteratedFDeriv ℝ m k)) := by
  intro a b hab
  have e : ∀ y, fderiv ℝ (iteratedFDeriv ℝ m k) y =
      continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Euc d) ℝ
        (iteratedFDeriv ℝ (m + 1) k y) := fun y => by
    rw [fderiv_iteratedFDeriv]; rfl
  have h2 := (continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Euc d) ℝ).norm_map
    (iteratedFDeriv ℝ (m + 1) k a - iteratedFDeriv ℝ (m + 1) k b)
  rw [LinearIsometryEquiv.map_sub] at h2
  rw [e a, e b, h2]
  exact hh a b hab

lemma s104c2_near_G_hasFDerivAt (hd : 1 ≤ d) {κ : Euc d → ℝ} {s η H : ℝ} (hK : UlKer κ s) (hη1 : η < 1)
    (hηd : s + 1 - η < (d : ℝ)) (hH : 0 ≤ H) {j : ℕ} {k : Euc d → ℝ} (hk : ContDiff ℝ j k)
    (hh : ∀ m ≤ j, HolNear η H (iteratedFDeriv ℝ m k)) {m : ℕ} (hm : m + 1 ≤ j) (x : Euc d) :
    HasFDerivAt (ultNear κ (iteratedFDeriv ℝ m k))
      (ultNear κ (fun y => fderiv ℝ (iteratedFDeriv ℝ m k) y) x) x := by
  have : CompleteSpace (Euc d [×m]→L[ℝ] ℝ) := inferInstance
  have hc1 := s104c2_iter_cd1 hk hm
  exact s104c2_near_hasFDerivAt hd hK hη1 hηd hH (hc1.differentiable one_ne_zero)
    (hc1.continuous_fderiv one_ne_zero) (hh m (by omega))
    (s104c2_fderiv_iter_hol (hh (m + 1) hm)) x

theorem s104c2_near_iter (hd : 1 ≤ d) {κ : Euc d → ℝ} {s η H : ℝ} (hK : UlKer κ s) (hη1 : η < 1)
    (hηd : s + 1 - η < (d : ℝ)) (hH : 0 ≤ H) {j : ℕ} {k : Euc d → ℝ} (hk : ContDiff ℝ j k)
    (hh : ∀ m ≤ j, HolNear η H (iteratedFDeriv ℝ m k)) :
    (∀ m ≤ j, ∀ x, iteratedFDeriv ℝ m (ultNear κ k) x = ultNear κ (iteratedFDeriv ℝ m k) x) ∧
      ContDiff ℝ j (ultNear κ k) := by
  have hcm : ∀ m ≤ j, Continuous (iteratedFDeriv ℝ m k) := fun m hm =>
    hk.continuous_iteratedFDeriv (by exact_mod_cast hm)
  have key : ∀ m ≤ j, ∀ x, iteratedFDeriv ℝ m (ultNear κ k) x =
      ultNear κ (iteratedFDeriv ℝ m k) x := by
    intro m
    induction m with
    | zero =>
      intro hm x
      have hint0 := s104c2_near_integrable hd hK hη1 hηd hH hk.continuous (s104c2_hol_zero (hh 0 hm)) x
      have h0 := ult_near_clm
        ((continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap)
        κ k x hint0
      rw [iteratedFDeriv_zero_eq_comp]
      exact h0
    | succ m ih =>
      intro hm x
      have hfun : iteratedFDeriv ℝ m (ultNear κ k) = ultNear κ (iteratedFDeriv ℝ m k) :=
        funext (ih (by omega))
      have hd' := s104c2_near_G_hasFDerivAt hd hK hη1 hηd hH hk hh hm x
      have : CompleteSpace (Euc d →L[ℝ] (Euc d [×m]→L[ℝ] ℝ)) := inferInstance
      have hc1 := s104c2_iter_cd1 hk hm
      have hint' := s104c2_near_integrable hd hK hη1 hηd hH (hc1.continuous_fderiv one_ne_zero)
        (s104c2_fderiv_iter_hol (hh (m + 1) hm)) x
      have h1 := ult_near_clm
        ((continuousMultilinearCurryLeftEquiv ℝ (fun _ : Fin (m + 1) => Euc d) ℝ).symm.toContinuousLinearEquiv.toContinuousLinearMap)
        κ (fun y => fderiv ℝ (iteratedFDeriv ℝ m k) y) x hint'
      rw [iteratedFDeriv_succ_eq_comp_left (f := ultNear κ k),
        iteratedFDeriv_succ_eq_comp_left (f := k)]
      simp only [Function.comp_apply]
      rw [hfun, hd'.fderiv]
      exact h1
  refine ⟨key, ?_⟩
  rw [contDiff_nat_iff_continuous_differentiable]
  refine ⟨fun m hm => ?_, fun m hm => ?_⟩
  · have hm' : m ≤ j := by exact_mod_cast hm
    have : (fun x => iteratedFDeriv ℝ m (ultNear κ k) x) = ultNear κ (iteratedFDeriv ℝ m k) :=
      funext (key m hm')
    rw [this]
    exact s104c2_near_continuous hd hK hη1 hηd hH (hcm m hm') (hh m hm')
  · have hm' : m + 1 ≤ j := by exact_mod_cast hm
    have : (fun x => iteratedFDeriv ℝ m (ultNear κ k) x) = ultNear κ (iteratedFDeriv ℝ m k) :=
      funext (key m (by omega))
    rw [this]
    exact fun x => (s104c2_near_G_hasFDerivAt hd hK hη1 hηd hH hk hh hm' x).differentiableAt

end Iter

end HRS.MS.S104e.C

end
