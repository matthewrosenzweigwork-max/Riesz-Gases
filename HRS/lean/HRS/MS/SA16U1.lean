import HRS.MS.SA16CutDefs
import HRS.MS.SA16JetSchwartz
import HRS.MS.CzPvAux1

/-!
# S.A.16 K1: `splice_div_curl`

`spliceKernel i z = z_i * kap |z|` with the radial profile `kap`.  Divergence identity: dilation `t * z`, the profile
transforms as `t^(-d) kap (r/t)` and the t-derivative at `1` of the regularised integral gives `theta * jumpCut`
(the atom is the `v 0` subtraction).  Curl identity: rotation in the `(i,j)`-plane, which preserves `kap |z|`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff SchwartzMap

namespace HRS.Whole.AppendixA.Phase2SA16Cutoff
open HRS HRS.Whole HRS.Whole.AppendixA HRS.CZ.Pv Phase2SA16

section K1
variable {d : ℕ}

/-- radial profile of the splice kernel -/
def sa16u_kap (d : ℕ) (θ δ r : ℝ) : ℝ :=
  if δ < r then r ^ (-((d : ℝ) + θ)) else δ ^ (-θ) * r ^ (-(d : ℝ))

lemma sa16u_kernel (θ δ : ℝ) (i : Fin d) (z : Euc d) :
    spliceKernel d θ δ i z = z i * sa16u_kap d θ δ ‖z‖ := by
  unfold spliceKernel sa16u_kap
  split_ifs with h
  · rw [Real.rpow_neg (norm_nonneg _)]; ring
  · rw [Real.rpow_neg (norm_nonneg _)]; ring

lemma sa16u_kap_meas (θ δ : ℝ) : Measurable (sa16u_kap d θ δ) :=
  Measurable.ite (measurableSet_lt measurable_const measurable_id) (measurable_id.pow_const _)
    (measurable_const.mul (measurable_id.pow_const _))

lemma sa16u_kap_nonneg (θ δ : ℝ) {r : ℝ} (hr : 0 ≤ r) (hδ : 0 < δ) : 0 ≤ sa16u_kap d θ δ r := by
  unfold sa16u_kap
  split_ifs
  · exact Real.rpow_nonneg hr _
  · exact mul_nonneg (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg hr _)

lemma sa16u_M_in (hd : 1 ≤ d) {θ δ : ℝ} (hδ : 0 < δ) {z : Euc d} (hz : ¬ δ < ‖z‖) :
    sa16u_kap d θ δ ‖z‖ * ‖z‖ ≤ δ ^ (-θ) * ‖z‖ ^ (-((d : ℝ) - 1)) := by
  unfold sa16u_kap
  rw [if_neg hz]
  by_cases h0 : ‖z‖ = 0
  · rw [h0, mul_zero]
    exact mul_nonneg (Real.rpow_nonneg hδ.le _) (Real.rpow_nonneg le_rfl _)
  · rw [mul_assoc, ← Real.rpow_add_one h0]
    have : -(d : ℝ) + 1 = -((d : ℝ) - 1) := by ring
    rw [this]

lemma sa16u_M_out (hd : 1 ≤ d) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) {z : Euc d} (hz : δ < ‖z‖) :
    sa16u_kap d θ δ ‖z‖ * ‖z‖ ≤ δ ^ (1 - ((d : ℝ) + θ)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  unfold sa16u_kap
  rw [if_pos hz, ← Real.rpow_add_one (by linarith : ‖z‖ ≠ 0)]
  have : -((d : ℝ) + θ) + 1 = 1 - ((d : ℝ) + θ) := by ring
  rw [this]
  exact Real.rpow_le_rpow_of_nonpos hδ hz.le (by linarith)

/-- the weight `kap |z| |z|` is bounded by a ball-integrable singularity plus a constant -/
lemma sa16u_M_le (hd : 1 ≤ d) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (z : Euc d) :
    sa16u_kap d θ δ ‖z‖ * ‖z‖ ≤ (closedBall (0 : Euc d) δ).indicator
        (fun z => δ ^ (-θ) * ‖z‖ ^ (-((d : ℝ) - 1))) z + δ ^ (1 - ((d : ℝ) + θ)) := by
  have hc : 0 ≤ δ ^ (1 - ((d : ℝ) + θ)) := Real.rpow_nonneg hδ.le _
  have hI : 0 ≤ (closedBall (0 : Euc d) δ).indicator
        (fun z => δ ^ (-θ) * ‖z‖ ^ (-((d : ℝ) - 1))) z :=
    Set.indicator_nonneg (fun w _ => mul_nonneg (Real.rpow_nonneg hδ.le _)
      (Real.rpow_nonneg (norm_nonneg _) _)) z
  by_cases hz : δ < ‖z‖
  · have := sa16u_M_out hd hθ hδ hz
    linarith
  · have hz' : z ∈ closedBall (0 : Euc d) δ := by simpa using hz
    rw [Set.indicator_of_mem hz'] at hI ⊢
    have := sa16u_M_in (θ := θ) hd hδ hz
    linarith

lemma sa16u_dec_int (d : ℕ) : Integrable (fun z : Euc d => ((1 + ‖z‖) ^ (d + 1))⁻¹) := by
  have h := integrable_one_add_norm (E := Euc d) (μ := volume) (r := (d : ℝ) + 1)
    (by rw [finrank_euclideanSpace_fin]; linarith)
  refine h.congr (Eventually.of_forall fun z => ?_)
  show (1 + ‖z‖) ^ (-((d : ℝ) + 1)) = _
  rw [Real.rpow_neg (by positivity)]
  congr 1
  exact_mod_cast Real.rpow_natCast (1 + ‖z‖) (d + 1)

lemma sa16u_M_int (hd : 1 ≤ d) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) :
    Integrable (fun z : Euc d => sa16u_kap d θ δ ‖z‖ * ‖z‖ * ((1 + ‖z‖) ^ (d + 1))⁻¹) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  have hball : Integrable ((closedBall (0 : Euc d) δ).indicator
        (fun z => δ ^ (-θ) * ‖z‖ ^ (-((d : ℝ) - 1)))) := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact ((pvapi_integrableOn_ball_rpow hd (α := (d : ℝ) - 1) (by linarith) (2 * δ)).mono_set
      (closedBall_subset_ball (by linarith))).const_mul _
  have hmaj := hball.add ((sa16u_dec_int d).const_mul (δ ^ (1 - ((d : ℝ) + θ))))
  refine Integrable.mono' hmaj ?_ (Eventually.of_forall fun z => ?_)
  · exact (((sa16u_kap_meas θ δ).comp measurable_norm).mul measurable_norm).mul
      ((measurable_const.add measurable_norm).pow_const _).inv |>.aestronglyMeasurable
  · have h1 : 0 < ((1 + ‖z‖) ^ (d + 1))⁻¹ := by positivity
    have h2 : ((1 + ‖z‖) ^ (d + 1))⁻¹ ≤ 1 := inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg z]))
    have h3 : 0 ≤ sa16u_kap d θ δ ‖z‖ * ‖z‖ :=
      mul_nonneg (sa16u_kap_nonneg θ δ (norm_nonneg z) hδ) (norm_nonneg z)
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg h3 h1.le)]
    have hI : 0 ≤ (closedBall (0 : Euc d) δ).indicator
        (fun z => δ ^ (-θ) * ‖z‖ ^ (-((d : ℝ) - 1))) z :=
      Set.indicator_nonneg (fun w _ => mul_nonneg (Real.rpow_nonneg hδ.le _)
        (Real.rpow_nonneg (norm_nonneg _) _)) z
    have := sa16u_M_le hd hθ hδ z
    set I : ℝ := (closedBall (0 : Euc d) δ).indicator
        (fun z => δ ^ (-θ) * ‖z‖ ^ (-((d : ℝ) - 1))) z with hIdef
    show _ ≤ I + δ ^ (1 - ((d : ℝ) + θ)) * ((1 + ‖z‖) ^ (d + 1))⁻¹
    nlinarith [mul_le_mul_of_nonneg_right this h1.le, mul_le_mul_of_nonneg_left h2 hI]

lemma sa16u_grad_bound (v : 𝓢(Euc d, ℝ)) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ y, ‖fderiv ℝ v y‖ ≤ C * ((1 + ‖y‖) ^ (d + 1))⁻¹ := by
  set K : ℝ := 2 ^ (d + 1) * (Finset.Iic ((d + 1, 1) : ℕ × ℕ)).sup
    (fun m => SchwartzMap.seminorm ℝ m.1 m.2) v with hK
  have hb : ∀ y, (1 + ‖y‖) ^ (d + 1) * ‖fderiv ℝ v y‖ ≤ K := fun y => by
    have h := SchwartzMap.one_add_le_sup_seminorm_apply (𝕜 := ℝ) (m := ((d + 1, 1) : ℕ × ℕ))
      (k := d + 1) (n := 1) le_rfl le_rfl v y
    rwa [norm_iteratedFDeriv_one] at h
  have hK0 : 0 ≤ K := le_trans (by positivity) (hb 0)
  refine ⟨K, hK0, fun y => ?_⟩
  rw [← div_eq_mul_inv, le_div_iff₀ (by positivity), mul_comm]
  exact hb y

lemma sa16u_lip (v : 𝓢(Euc d, ℝ)) : ∃ L : ℝ, 0 ≤ L ∧ ∀ w, |v w - v 0| ≤ L * ‖w‖ := by
  obtain ⟨C, hC0, hC⟩ := sa16u_grad_bound v
  refine ⟨C, hC0, fun w => ?_⟩
  have h := Convex.norm_image_sub_le_of_norm_fderiv_le (f := ⇑v) (s := (Set.univ : Set (Euc d)))
    (C := C) (fun x _ => v.differentiableAt) (fun x _ => ?_) convex_univ (Set.mem_univ 0) (Set.mem_univ w)
  · simpa [Real.norm_eq_abs] using h
  · refine (hC x).trans ?_
    have : ((1 + ‖x‖) ^ (d + 1))⁻¹ ≤ 1 :=
      inv_le_one_of_one_le₀ (one_le_pow₀ (by linarith [norm_nonneg x]))
    nlinarith

/-- the far tail `|w|^(-s)` outside the ball of radius `δ` is integrable for `s > d` -/
lemma sa16u_tail_int (hd : 1 ≤ d) {δ : ℝ} (hδ : 0 < δ) {s : ℝ} (hs : (d : ℝ) < s) :
    Integrable ({w : Euc d | δ < ‖w‖}.indicator (fun w => ‖w‖ ^ (-s))) := by
  have hS : MeasurableSet {w : Euc d | δ < ‖w‖} := measurableSet_lt measurable_const measurable_norm
  have h := integrable_one_add_norm (E := Euc d) (μ := volume) (r := s)
    (by rw [finrank_euclideanSpace_fin]; exact hs)
  have hs0 : 0 ≤ s := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  refine Integrable.mono' (h.const_mul ((1 + δ⁻¹) ^ s)) ?_ (Eventually.of_forall fun w => ?_)
  · exact ((measurable_norm.pow_const _).indicator hS).aestronglyMeasurable
  · by_cases hw : δ < ‖w‖
    · rw [Set.indicator_of_mem (show w ∈ {w : Euc d | δ < ‖w‖} from hw)]
      have hn : 0 < ‖w‖ := hδ.trans hw
      rw [Real.norm_of_nonneg (Real.rpow_nonneg hn.le _)]
      have h1 : (1 + ‖w‖) / (1 + δ⁻¹) ≤ ‖w‖ := by
        rw [div_le_iff₀ (by positivity)]
        have : 1 ≤ ‖w‖ * δ⁻¹ := by
          rw [← div_eq_mul_inv, le_div_iff₀ hδ]; linarith
        nlinarith
      have h2 := Real.rpow_le_rpow_of_nonpos (by positivity) h1 (by linarith : -s ≤ 0)
      refine h2.trans (le_of_eq ?_)
      rw [Real.div_rpow (by positivity) (by positivity), Real.rpow_neg (by positivity : (0:ℝ) ≤ 1 + δ⁻¹)]
      field_simp
    · rw [Set.indicator_of_notMem (show w ∉ {w : Euc d | δ < ‖w‖} from hw)]
      simp only [norm_zero]
      positivity

lemma sa16u_G_int (hd : 1 ≤ d) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (v : 𝓢(Euc d, ℝ)) :
    Integrable (fun w : Euc d => sa16u_kap d θ δ ‖w‖ * (v w - v 0)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨L, hL0, hL⟩ := sa16u_lip v
  obtain ⟨B, hB⟩ := sa16j_schwartz_bdd v
  have hball : Integrable ((closedBall (0 : Euc d) δ).indicator
        (fun z => δ ^ (-θ) * ‖z‖ ^ (-((d : ℝ) - 1)))) := by
    rw [integrable_indicator_iff measurableSet_closedBall]
    exact ((pvapi_integrableOn_ball_rpow hd (α := (d : ℝ) - 1) (by linarith) (2 * δ)).mono_set
      (closedBall_subset_ball (by linarith))).const_mul _
  have htail := sa16u_tail_int hd hδ (s := (d : ℝ) + θ) (by linarith)
  refine Integrable.mono' ((hball.const_mul L).add (htail.const_mul (2 * B))) ?_
    (Eventually.of_forall fun w => ?_)
  · exact (((sa16u_kap_meas θ δ).comp measurable_norm).aestronglyMeasurable).mul
      ((v.continuous.sub continuous_const).aestronglyMeasurable)
  · rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs,
      abs_of_nonneg (sa16u_kap_nonneg θ δ (norm_nonneg w) hδ)]
    by_cases hw : δ < ‖w‖
    · have hnot : w ∉ closedBall (0 : Euc d) δ := by simpa using hw
      show _ ≤ L * (closedBall (0 : Euc d) δ).indicator _ w + 2 * B * {w : Euc d | δ < ‖w‖}.indicator _ w
      rw [Set.indicator_of_notMem hnot, Set.indicator_of_mem (show w ∈ {w : Euc d | δ < ‖w‖} from hw)]
      have hk : sa16u_kap d θ δ ‖w‖ = ‖w‖ ^ (-((d : ℝ) + θ)) := by unfold sa16u_kap; rw [if_pos hw]
      rw [hk, mul_zero, zero_add]
      have h2 : |v w - v 0| ≤ 2 * B := by
        have := abs_sub (v w) (v 0)
        linarith [hB w, hB 0]
      exact mul_comm (2 * B) _ ▸ mul_le_mul_of_nonneg_left h2 (Real.rpow_nonneg (norm_nonneg _) _)
        |>.trans_eq (by ring)
    · have hin : w ∈ closedBall (0 : Euc d) δ := by simpa using hw
      show _ ≤ L * (closedBall (0 : Euc d) δ).indicator _ w + 2 * B * {w : Euc d | δ < ‖w‖}.indicator _ w
      rw [Set.indicator_of_mem hin, Set.indicator_of_notMem (show w ∉ {w : Euc d | δ < ‖w‖} from hw),
        mul_zero, add_zero]
      calc sa16u_kap d θ δ ‖w‖ * |v w - v 0| ≤ sa16u_kap d θ δ ‖w‖ * (L * ‖w‖) :=
            mul_le_mul_of_nonneg_left (hL w) (sa16u_kap_nonneg θ δ (norm_nonneg w) hδ)
        _ = L * (sa16u_kap d θ δ ‖w‖ * ‖w‖) := by ring
        _ ≤ L * (δ ^ (-θ) * ‖w‖ ^ (-((d : ℝ) - 1))) :=
            mul_le_mul_of_nonneg_left (sa16u_M_in hd hδ hw) hL0

lemma sa16u_fderiv_cont (v : 𝓢(Euc d, ℝ)) : Continuous (fderiv ℝ v) :=
  (v.smooth 1).continuous_fderiv (by norm_num)

lemma sa16u_inv_le {t : ℝ} (ht : 1 / 2 < t) (r : ℝ) (hr : 0 ≤ r) :
    ((1 + t * r) ^ (d + 1))⁻¹ ≤ 2 ^ (d + 1) * ((1 + r) ^ (d + 1))⁻¹ := by
  have h1 : 1 + r ≤ 2 * (1 + t * r) := by nlinarith
  have h2 : (1 + r) ^ (d + 1) ≤ 2 ^ (d + 1) * (1 + t * r) ^ (d + 1) := by
    rw [← mul_pow]; exact pow_le_pow_left₀ (by positivity) h1 _
  have hp : 0 < (1 + t * r) := by nlinarith
  rw [inv_le_comm₀ (by positivity) (by positivity), mul_inv, inv_inv]
  rw [← div_eq_inv_mul, div_le_iff₀ (by positivity)] 
  nlinarith [h2]

lemma sa16u_dil_deriv (hd : 1 ≤ d) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (v : 𝓢(Euc d, ℝ)) :
    HasDerivAt (fun t : ℝ => ∫ z : Euc d, sa16u_kap d θ δ ‖z‖ * (v (t • z) - v 0))
      (∫ z : Euc d, sa16u_kap d θ δ ‖z‖ * fderiv ℝ v z z) 1 := by
  obtain ⟨C, hC0, hC⟩ := sa16u_grad_bound v
  have hm : ∀ t : ℝ, AEStronglyMeasurable (fun z : Euc d => sa16u_kap d θ δ ‖z‖ * (v (t • z) - v 0)) volume :=
    fun t => (((sa16u_kap_meas θ δ).comp measurable_norm).aestronglyMeasurable).mul
      (by fun_prop : Continuous fun z : Euc d => v (t • z) - v 0).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Euc d)))
    (F := fun (t : ℝ) (z : Euc d) => sa16u_kap d θ δ ‖z‖ * (v (t • z) - v 0))
    (F' := fun (t : ℝ) (z : Euc d) => sa16u_kap d θ δ ‖z‖ * fderiv ℝ v (t • z) z)
    (x₀ := 1) (bound := fun z => 2 ^ (d + 1) * C * (sa16u_kap d θ δ ‖z‖ * ‖z‖ * ((1 + ‖z‖) ^ (d + 1))⁻¹))
    (s := ball (1 : ℝ) (1 / 2)) (Metric.ball_mem_nhds _ (by norm_num)) (Eventually.of_forall hm)
    (by simpa using sa16u_G_int hd hθ hδ v)
    (by
      simp only [one_smul]
      exact (((sa16u_kap_meas θ δ).comp measurable_norm).aestronglyMeasurable).mul
        ((sa16u_fderiv_cont v).clm_apply continuous_id).aestronglyMeasurable)
    (Eventually.of_forall fun z t ht => ?_)
    (((sa16u_M_int hd hθ hδ).const_mul (2 ^ (d + 1) * C)))
    (Eventually.of_forall fun z t ht => ?_)
  · simpa using key.2
  · have ht' : 1 / 2 < t := by
      have := (Metric.mem_ball.1 ht); rw [Real.dist_eq, abs_lt] at this; linarith [this.1]
    have htp : 0 < t := by linarith
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sa16u_kap_nonneg θ δ (norm_nonneg z) hδ)]
    have h1 : ‖fderiv ℝ v (t • z) z‖ ≤ C * (2 ^ (d + 1) * ((1 + ‖z‖) ^ (d + 1))⁻¹) * ‖z‖ := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      refine mul_le_mul_of_nonneg_right ((hC (t • z)).trans ?_) (norm_nonneg _)
      rw [norm_smul, Real.norm_of_nonneg htp.le]
      exact mul_le_mul_of_nonneg_left (sa16u_inv_le ht' _ (norm_nonneg _)) hC0
    calc sa16u_kap d θ δ ‖z‖ * ‖fderiv ℝ v (t • z) z‖
        ≤ sa16u_kap d θ δ ‖z‖ * (C * (2 ^ (d + 1) * ((1 + ‖z‖) ^ (d + 1))⁻¹) * ‖z‖) :=
          mul_le_mul_of_nonneg_left h1 (sa16u_kap_nonneg θ δ (norm_nonneg z) hδ)
      _ = _ := by ring
  · have h1 : HasDerivAt (fun t : ℝ => v (t • z)) (fderiv ℝ v (t • z) z) t := by
      have := (v.differentiableAt (x := t • z)).hasFDerivAt.comp_hasDerivAt t
        ((hasDerivAt_id t).smul_const z)
      simp only [one_smul] at this
      exact this
    exact (h1.sub_const (v 0)).const_mul _

lemma sa16u_kap_zero (hd : 1 ≤ d) (θ δ : ℝ) (hδ : 0 < δ) : sa16u_kap d θ δ 0 = 0 := by
  have hd1 : (d : ℝ) ≠ 0 := by have : (1 : ℝ) ≤ d := by exact_mod_cast hd
                               linarith
  unfold sa16u_kap
  rw [if_neg (not_lt.2 hδ.le), Real.zero_rpow (neg_ne_zero.2 hd1), mul_zero]

/-- the rescaled-profile defect `t^(-d) kap(r/t) - kap r` -/
def sa16u_D (d : ℕ) (θ δ t r : ℝ) : ℝ := (t ^ d)⁻¹ * sa16u_kap d θ δ (r / t) - sa16u_kap d θ δ r

lemma sa16u_scale_aux {t r : ℝ} (ht : 0 < t) (hr : 0 < r) (a : ℝ) :
    (t ^ d)⁻¹ * (r / t) ^ (-((d : ℝ) + a)) = t ^ a * r ^ (-((d : ℝ) + a)) := by
  rw [Real.div_rpow hr.le ht.le, Real.rpow_neg ht.le, div_inv_eq_mul, Real.rpow_neg hr.le,
    Real.rpow_add ht, Real.rpow_natCast, ← Real.rpow_neg hr.le]
  field_simp

lemma sa16u_D_in (hd : 1 ≤ d) {θ δ t r : ℝ} (hδ : 0 < δ) (ht : 1 < t) (hr0 : 0 ≤ r) (hr : r ≤ δ) :
    sa16u_D d θ δ t r = 0 := by
  have htp : 0 < t := by linarith
  unfold sa16u_D
  rcases hr0.eq_or_lt with h | h
  · subst h
    simp [sa16u_kap_zero hd θ δ hδ]
  · have h1 : ¬ δ < r := not_lt.2 hr
    have h2 : ¬ δ < r / t := not_lt.2 ((div_le_self hr0 ht.le).trans hr)
    unfold sa16u_kap
    rw [if_neg h1, if_neg h2]
    have := sa16u_scale_aux (d := d) htp h 0
    simp only [add_zero] at this
    rw [mul_left_comm, this, Real.rpow_zero, one_mul]
    ring

lemma sa16u_D_far {θ δ t r : ℝ} (hδ : 0 < δ) (ht : 1 < t) (hr : t * δ < r) :
    sa16u_D d θ δ t r = (t ^ θ - 1) * r ^ (-((d : ℝ) + θ)) := by
  have htp : 0 < t := by linarith
  have hrp : 0 < r := by nlinarith
  have h1 : δ < r := by nlinarith
  have h2 : δ < r / t := by rw [lt_div_iff₀ htp]; linarith
  unfold sa16u_D sa16u_kap
  rw [if_pos h1, if_pos h2, sa16u_scale_aux htp hrp θ]
  ring

lemma sa16u_D_shell {θ δ t r : ℝ} (hδ : 0 < δ) (ht : 1 < t) (hθ : 0 < θ) (h1 : δ < r) (h2 : r ≤ t * δ) :
    0 ≤ sa16u_D d θ δ t r ∧ sa16u_D d θ δ t r ≤ (t ^ θ - 1) * r ^ (-((d : ℝ) + θ)) := by
  have htp : 0 < t := by linarith
  have hrp : 0 < r := hδ.trans h1
  have h3 : ¬ δ < r / t := not_lt.2 (by rw [div_le_iff₀ htp]; linarith)
  have e1 : (t ^ d)⁻¹ * (δ ^ (-θ) * (r / t) ^ (-(d : ℝ))) = δ ^ (-θ) * r ^ (-(d : ℝ)) := by
    have := sa16u_scale_aux (d := d) htp hrp 0
    simp only [add_zero, Real.rpow_zero, one_mul] at this
    rw [mul_left_comm, this]
  have e2 : r ^ (-((d : ℝ) + θ)) = r ^ (-(d : ℝ)) * r ^ (-θ) := by
    rw [← Real.rpow_add hrp]; congr 1; ring
  have hD : sa16u_D d θ δ t r = r ^ (-(d : ℝ)) * (δ ^ (-θ) - r ^ (-θ)) := by
    unfold sa16u_D sa16u_kap
    rw [if_pos h1, if_neg h3, e1, e2]
    ring
  have hrd : 0 ≤ r ^ (-(d : ℝ)) := Real.rpow_nonneg hrp.le _
  have hle : r ^ (-θ) ≤ δ ^ (-θ) := Real.rpow_le_rpow_of_nonpos hδ h1.le (by linarith)
  have hge : δ ^ (-θ) ≤ t ^ θ * r ^ (-θ) := by
    have h4 := Real.rpow_le_rpow_of_nonpos hrp h2 (by linarith : -θ ≤ 0)
    rw [Real.mul_rpow htp.le hδ.le] at h4
    have h5 : t ^ θ * t ^ (-θ) = 1 := by rw [← Real.rpow_add htp]; simp
    have h6 : 0 ≤ t ^ θ := Real.rpow_nonneg htp.le _
    calc δ ^ (-θ) = t ^ θ * (t ^ (-θ) * δ ^ (-θ)) := by rw [← mul_assoc, h5, one_mul]
      _ ≤ t ^ θ * r ^ (-θ) := mul_le_mul_of_nonneg_left h4 h6
  refine ⟨by rw [hD]; exact mul_nonneg hrd (by linarith), ?_⟩
  rw [hD, e2]
  nlinarith [mul_le_mul_of_nonneg_left hge hrd]

lemma sa16u_D_bd (hd : 1 ≤ d) {θ δ t r : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (ht : 1 < t) (hr : 0 ≤ r) :
    0 ≤ sa16u_D d θ δ t r ∧ sa16u_D d θ δ t r ≤
      (t ^ θ - 1) * (if δ < r then r ^ (-((d : ℝ) + θ)) else 0) := by
  have h1t : 1 ≤ t ^ θ := Real.one_le_rpow ht.le hθ.le
  by_cases h1 : δ < r
  · rw [if_pos h1]
    by_cases h2 : r ≤ t * δ
    · exact sa16u_D_shell hδ ht hθ h1 h2
    · have := sa16u_D_far (d := d) (θ := θ) hδ ht (not_le.1 h2)
      rw [this]
      exact ⟨mul_nonneg (by linarith) (Real.rpow_nonneg hr _), le_rfl⟩
  · rw [if_neg h1, mul_zero, sa16u_D_in hd hδ ht hr (not_lt.1 h1)]
    exact ⟨le_rfl, le_rfl⟩

lemma sa16u_rpow_sub_one_le {θ t : ℝ} (hθ : 0 < θ) (ht : 1 < t) : t ^ θ - 1 ≤ θ * t ^ θ * (t - 1) := by
  have htp : 0 < t := by linarith
  have h1 : Real.log t ≤ t - 1 := Real.log_le_sub_one_of_pos htp
  have h2 : 1 - θ * Real.log t ≤ t ^ (-θ) := by
    rw [Real.rpow_def_of_pos htp]
    have := Real.add_one_le_exp (Real.log t * (-θ))
    linarith
  have h3 : t ^ θ * t ^ (-θ) = 1 := by rw [← Real.rpow_add htp]; simp
  have h4 : 0 < t ^ θ := Real.rpow_pos_of_pos htp _
  have h5 : 1 - θ * (t - 1) ≤ t ^ (-θ) := by nlinarith
  nlinarith [mul_le_mul_of_nonneg_left h5 h4.le]

/-- change of variables `z = w / t` -/
lemma sa16u_dil_eq {t : ℝ} (ht : 0 < t) (v : 𝓢(Euc d, ℝ)) (θ δ : ℝ) :
    ∫ z : Euc d, sa16u_kap d θ δ ‖z‖ * (v (t • z) - v 0) =
      ∫ w : Euc d, (t ^ d)⁻¹ * sa16u_kap d θ δ (‖w‖ / t) * (v w - v 0) := by
  have h := Measure.integral_comp_smul (volume : Measure (Euc d))
    (fun w : Euc d => sa16u_kap d θ δ (‖w‖ / t) * (v w - v 0)) t
  rw [finrank_euclideanSpace_fin, smul_eq_mul, abs_of_nonneg (by positivity)] at h
  have h2 : ∫ w : Euc d, (t ^ d)⁻¹ * sa16u_kap d θ δ (‖w‖ / t) * (v w - v 0) =
      (t ^ d)⁻¹ * ∫ w : Euc d, sa16u_kap d θ δ (‖w‖ / t) * (v w - v 0) := by
    rw [← integral_const_mul]
    exact integral_congr_ae (Eventually.of_forall fun w => by simp only [mul_assoc])
  rw [h2, ← h]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [norm_smul, Real.norm_of_nonneg ht.le]
  rw [mul_div_cancel_left₀ _ ht.ne']

lemma sa16u_D_meas (θ δ t : ℝ) : Measurable (sa16u_D d θ δ t) :=
  (measurable_const.mul ((sa16u_kap_meas θ δ).comp (measurable_id.div_const t))).sub
    (sa16u_kap_meas θ δ)

lemma sa16u_Dv_int (hd : 1 ≤ d) {θ δ t : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (ht : 1 < t)
    (v : 𝓢(Euc d, ℝ)) :
    Integrable (fun w : Euc d => sa16u_D d θ δ t ‖w‖ * (v w - v 0)) := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨B, hB⟩ := sa16j_schwartz_bdd v
  have htail := sa16u_tail_int hd hδ (s := (d : ℝ) + θ) (by linarith)
  refine Integrable.mono' (htail.const_mul ((t ^ θ - 1) * (2 * B))) ?_ (Eventually.of_forall fun w => ?_)
  · exact (((sa16u_D_meas θ δ t).comp measurable_norm).aestronglyMeasurable).mul
      ((v.continuous.sub continuous_const).aestronglyMeasurable)
  · obtain ⟨h0, h1⟩ := sa16u_D_bd hd hθ hδ ht (norm_nonneg w)
    have h2 : |v w - v 0| ≤ 2 * B := by
      have := abs_sub (v w) (v 0)
      linarith [hB w, hB 0]
    have h3 : 0 ≤ t ^ θ - 1 := by linarith [Real.one_le_rpow ht.le hθ.le]
    rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0]
    have hind : {w : Euc d | δ < ‖w‖}.indicator (fun w => ‖w‖ ^ (-((d : ℝ) + θ))) w =
        if δ < ‖w‖ then ‖w‖ ^ (-((d : ℝ) + θ)) else 0 := by
      by_cases h : δ < ‖w‖
      · rw [Set.indicator_of_mem (show w ∈ {w : Euc d | δ < ‖w‖} from h), if_pos h]
      · rw [Set.indicator_of_notMem (show w ∉ {w : Euc d | δ < ‖w‖} from h), if_neg h]
    show _ ≤ (t ^ θ - 1) * (2 * B) * {w : Euc d | δ < ‖w‖}.indicator (fun w => ‖w‖ ^ (-((d : ℝ) + θ))) w
    rw [hind]
    have hI : 0 ≤ (if δ < ‖w‖ then ‖w‖ ^ (-((d : ℝ) + θ)) else 0) := by
      split_ifs
      · exact Real.rpow_nonneg (norm_nonneg _) _
      · exact le_rfl
    calc sa16u_D d θ δ t ‖w‖ * |v w - v 0|
        ≤ ((t ^ θ - 1) * (if δ < ‖w‖ then ‖w‖ ^ (-((d : ℝ) + θ)) else 0)) * (2 * B) :=
          mul_le_mul h1 h2 (abs_nonneg _) (mul_nonneg h3 hI)
      _ = _ := by ring

lemma sa16u_gt_int (hd : 1 ≤ d) {θ δ t : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (ht : 1 < t)
    (v : 𝓢(Euc d, ℝ)) :
    Integrable (fun w : Euc d => (t ^ d)⁻¹ * sa16u_kap d θ δ (‖w‖ / t) * (v w - v 0)) := by
  refine ((sa16u_G_int hd hθ hδ v).add (sa16u_Dv_int hd hθ hδ ht v)).congr
    (Eventually.of_forall fun w => ?_)
  simp only [Pi.add_apply, sa16u_D]
  ring

/-- divergence identity, in dilation form -/
theorem sa16u_div_formula (hd : 1 ≤ d) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (v : 𝓢(Euc d, ℝ)) :
    ∫ z : Euc d, sa16u_kap d θ δ ‖z‖ * fderiv ℝ v z z =
      θ * ∫ w : Euc d, {w : Euc d | δ < ‖w‖}.indicator
        (fun w => ‖w‖ ^ (-((d : ℝ) + θ)) * (v w - v 0)) w := by
  have hd1 : (1 : ℝ) ≤ d := by exact_mod_cast hd
  obtain ⟨B, hB⟩ := sa16j_schwartz_bdd v
  set Φ : ℝ → ℝ := fun t => ∫ z : Euc d, sa16u_kap d θ δ ‖z‖ * (v (t • z) - v 0) with hΦ
  have hder := sa16u_dil_deriv hd hθ hδ v
  have hslope : Tendsto (slope Φ 1) (𝓝[>] (1 : ℝ))
      (𝓝 (∫ z : Euc d, sa16u_kap d θ δ ‖z‖ * fderiv ℝ v z z)) :=
    (hasDerivAt_iff_tendsto_slope.1 hder).mono_left (nhdsGT_le_nhdsNE (1 : ℝ))
  -- the quotient as an integral
  set q : ℝ → Euc d → ℝ := fun t w => (t - 1)⁻¹ * (sa16u_D d θ δ t ‖w‖ * (v w - v 0)) with hq
  have hslope_eq : ∀ t : ℝ, 1 < t → slope Φ 1 t = ∫ w, q t w := by
    intro t ht
    have h1 : Φ 1 = ∫ w : Euc d, sa16u_kap d θ δ ‖w‖ * (v w - v 0) := by
      simp only [hΦ, one_smul]
    have h2 : Φ t = ∫ w : Euc d, (t ^ d)⁻¹ * sa16u_kap d θ δ (‖w‖ / t) * (v w - v 0) :=
      sa16u_dil_eq (by linarith) v θ δ
    rw [slope_def_field, h1, h2, div_eq_inv_mul, ← integral_sub (sa16u_gt_int hd hθ hδ ht v)
      (sa16u_G_int hd hθ hδ v), ← integral_const_mul]
    refine integral_congr_ae (Eventually.of_forall fun w => ?_)
    simp only [hq, sa16u_D]
    ring
  -- dominated convergence
  have hind_int := sa16u_tail_int hd hδ (s := (d : ℝ) + θ) (by linarith)
  set f : Euc d → ℝ := fun w => θ * {w : Euc d | δ < ‖w‖}.indicator
        (fun w => ‖w‖ ^ (-((d : ℝ) + θ)) * (v w - v 0)) w with hf
  have hlim : Tendsto (fun t => ∫ w, q t w) (𝓝[>] (1 : ℝ)) (𝓝 (∫ w, f w)) := by
    refine tendsto_integral_filter_of_dominated_convergence
      (fun w => θ * 2 ^ θ * (2 * B) * {w : Euc d | δ < ‖w‖}.indicator (fun w => ‖w‖ ^ (-((d : ℝ) + θ))) w)
      ?_ ?_ (hind_int.const_mul _) ?_
    · filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (1 : ℝ)) (a := 1)] with t ht
      exact ((sa16u_Dv_int hd hθ hδ ht v).const_mul (t - 1)⁻¹).aestronglyMeasurable
    · filter_upwards [Ioo_mem_nhdsGT (show (1 : ℝ) < 2 by norm_num)] with t ht
      refine Eventually.of_forall fun w => ?_
      obtain ⟨h0, h1⟩ := sa16u_D_bd hd hθ hδ ht.1 (norm_nonneg w)
      have htp : 0 < t - 1 := by linarith [ht.1]
      have h2 : |v w - v 0| ≤ 2 * B := by
        have := abs_sub (v w) (v 0)
        linarith [hB w, hB 0]
      have hI : 0 ≤ (if δ < ‖w‖ then ‖w‖ ^ (-((d : ℝ) + θ)) else 0) := by
        split_ifs
        · exact Real.rpow_nonneg (norm_nonneg _) _
        · exact le_rfl
      have hind : {w : Euc d | δ < ‖w‖}.indicator (fun w => ‖w‖ ^ (-((d : ℝ) + θ))) w =
          if δ < ‖w‖ then ‖w‖ ^ (-((d : ℝ) + θ)) else 0 := by
        by_cases h : δ < ‖w‖
        · rw [Set.indicator_of_mem (show w ∈ {w : Euc d | δ < ‖w‖} from h), if_pos h]
        · rw [Set.indicator_of_notMem (show w ∉ {w : Euc d | δ < ‖w‖} from h), if_neg h]
      rw [hind]
      have h3 := sa16u_rpow_sub_one_le hθ ht.1
      have h4 : t ^ θ ≤ 2 ^ θ := Real.rpow_le_rpow (by linarith [ht.1]) ht.2.le hθ.le
      have h5 : sa16u_D d θ δ t ‖w‖ ≤ θ * 2 ^ θ * (t - 1) * (if δ < ‖w‖ then ‖w‖ ^ (-((d : ℝ) + θ)) else 0) := by
        refine h1.trans (mul_le_mul_of_nonneg_right ?_ hI)
        calc t ^ θ - 1 ≤ θ * t ^ θ * (t - 1) := h3
          _ ≤ θ * 2 ^ θ * (t - 1) := by
            apply mul_le_mul_of_nonneg_right _ htp.le
            exact mul_le_mul_of_nonneg_left h4 hθ.le
      simp only [hq]
      rw [norm_mul, norm_mul, Real.norm_eq_abs, Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg h0,
        abs_inv, abs_of_pos htp]
      calc (t - 1)⁻¹ * (sa16u_D d θ δ t ‖w‖ * |v w - v 0|)
          ≤ (t - 1)⁻¹ * ((θ * 2 ^ θ * (t - 1) * (if δ < ‖w‖ then ‖w‖ ^ (-((d : ℝ) + θ)) else 0)) * (2 * B)) :=
            mul_le_mul_of_nonneg_left (mul_le_mul h5 h2 (abs_nonneg _) (by
              have : 0 ≤ θ * 2 ^ θ * (t - 1) := by positivity
              exact mul_nonneg this hI)) (inv_nonneg.2 htp.le)
        _ = _ := by field_simp
    · refine Eventually.of_forall fun w => ?_
      by_cases hw : δ < ‖w‖
      · have hev : ∀ᶠ t in 𝓝[>] (1 : ℝ), t * δ < ‖w‖ := by
          have : (1 : ℝ) < ‖w‖ / δ := by rw [lt_div_iff₀ hδ]; linarith
          filter_upwards [nhdsWithin_le_nhds (Iio_mem_nhds this),
            self_mem_nhdsWithin (s := Set.Ioi (1 : ℝ)) (a := 1)] with t ht1 ht2
          have : t < ‖w‖ / δ := ht1
          rwa [lt_div_iff₀ hδ] at this
        have hsl : Tendsto (slope (fun t : ℝ => t ^ θ) 1) (𝓝[>] (1 : ℝ)) (𝓝 θ) := by
          have := (Real.hasDerivAt_rpow_const (x := 1) (p := θ) (Or.inl one_ne_zero))
          simp only [Real.one_rpow, mul_one] at this
          exact (hasDerivAt_iff_tendsto_slope.1 this).mono_left (nhdsGT_le_nhdsNE (1 : ℝ))
        have hfw : f w = θ * (‖w‖ ^ (-((d : ℝ) + θ)) * (v w - v 0)) := by
          simp only [hf]
          rw [Set.indicator_of_mem (show w ∈ {w : Euc d | δ < ‖w‖} from hw)]
        rw [hfw]
        have := (hsl.mul_const (‖w‖ ^ (-((d : ℝ) + θ)) * (v w - v 0)))
        refine this.congr' ?_
        filter_upwards [hev, self_mem_nhdsWithin (s := Set.Ioi (1 : ℝ)) (a := 1)] with t h1 h2
        have h2' : 1 < t := h2
        simp only [hq]
        rw [sa16u_D_far hδ h2' h1, slope_def_field, Real.one_rpow, div_eq_inv_mul]
        ring
      · have hfw : f w = 0 := by
          simp only [hf]
          rw [Set.indicator_of_notMem (show w ∉ {w : Euc d | δ < ‖w‖} from hw), mul_zero]
        rw [hfw]
        refine tendsto_const_nhds.congr' ?_
        filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (1 : ℝ)) (a := 1)] with t h2
        have h2' : 1 < t := h2
        simp only [hq]
        rw [sa16u_D_in hd hδ h2' (norm_nonneg w) (not_lt.1 hw)]
        simp
  have hlim' : Tendsto (fun t => ∫ w, q t w) (𝓝[>] (1 : ℝ))
      (𝓝 (∫ z : Euc d, sa16u_kap d θ δ ‖z‖ * fderiv ℝ v z z)) := by
    refine hslope.congr' ?_
    filter_upwards [self_mem_nhdsWithin (s := Set.Ioi (1 : ℝ)) (a := 1)] with t ht
    exact hslope_eq t ht
  rw [tendsto_nhds_unique hlim' hlim]
  simp only [hf]
  rw [integral_const_mul]

/-! ### rotation in the `(i,j)`-plane -/

/-- `z ↦ z_i e_i + z_j e_j` -/
def sa16u_P (i j : Fin d) : Euc d →ₗ[ℝ] Euc d :=
  ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) : Euc d →ₗ[ℝ] ℝ).smulRight (EuclideanSpace.single i (1 : ℝ)) +
  ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) : Euc d →ₗ[ℝ] ℝ).smulRight (EuclideanSpace.single j (1 : ℝ))

/-- `z ↦ z_i e_j - z_j e_i` (infinitesimal rotation) -/
def sa16u_J (i j : Fin d) : Euc d →ₗ[ℝ] Euc d :=
  ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) : Euc d →ₗ[ℝ] ℝ).smulRight (EuclideanSpace.single j (1 : ℝ)) -
  ((EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) : Euc d →ₗ[ℝ] ℝ).smulRight (EuclideanSpace.single i (1 : ℝ))

def sa16u_rot (i j : Fin d) (t : ℝ) : Euc d →ₗ[ℝ] Euc d :=
  LinearMap.id + (Real.cos t - 1) • sa16u_P i j + Real.sin t • sa16u_J i j

lemma sa16u_rot_apply (i j : Fin d) (t : ℝ) (z : Euc d) (k : Fin d) :
    sa16u_rot i j t z k = z k + (Real.cos t - 1) * (z i * (if k = i then 1 else 0) + z j * (if k = j then 1 else 0))
      + Real.sin t * (z i * (if k = j then 1 else 0) - z j * (if k = i then 1 else 0)) := by
  simp [sa16u_rot, sa16u_P, sa16u_J, EuclideanSpace.single_apply]
  split_ifs <;> ring

lemma sa16u_rot_norm (i j : Fin d) (hij : i ≠ j) (t : ℝ) (z : Euc d) : ‖sa16u_rot i j t z‖ = ‖z‖ := by
  have key : ∑ k, (sa16u_rot i j t z k) ^ 2 = ∑ k, (z k) ^ 2 := by
    have h := Finset.sum_eq_add (s := Finset.univ) (f := fun k => (sa16u_rot i j t z k) ^ 2 - (z k) ^ 2) i j hij
      (fun k _ hk => by
        rw [sa16u_rot_apply]
        simp [hk.1, hk.2]) (fun h => absurd (Finset.mem_univ i) h) (fun h => absurd (Finset.mem_univ j) h)
    rw [Finset.sum_sub_distrib] at h
    have h2 : (sa16u_rot i j t z i) ^ 2 - (z i) ^ 2 + ((sa16u_rot i j t z j) ^ 2 - (z j) ^ 2) = 0 := by
      rw [sa16u_rot_apply, sa16u_rot_apply]
      simp only [if_true, hij, hij.symm, if_false]
      have := Real.sin_sq_add_cos_sq t
      nlinarith [this]
    linarith
  rw [EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  simpa [Real.norm_eq_abs, sq_abs] using key

lemma sa16u_P_norm (i j : Fin d) (z : Euc d) : ‖sa16u_P i j z‖ ≤ 2 * ‖z‖ := by
  have hi : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) z‖ ≤ ‖z‖ := PiLp.norm_apply_le z i
  have hj : ‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) z‖ ≤ ‖z‖ := PiLp.norm_apply_le z j
  simp only [sa16u_P, LinearMap.add_apply, LinearMap.smulRight_apply, ContinuousLinearMap.coe_coe]
  refine (norm_add_le _ _).trans ?_
  rw [norm_smul, norm_smul, PiLp.norm_single, PiLp.norm_single, norm_one, mul_one, mul_one]
  linarith

lemma sa16u_J_norm (i j : Fin d) (z : Euc d) : ‖sa16u_J i j z‖ ≤ 2 * ‖z‖ := by
  have hi : ‖(EuclideanSpace.proj i : Euc d →L[ℝ] ℝ) z‖ ≤ ‖z‖ := PiLp.norm_apply_le z i
  have hj : ‖(EuclideanSpace.proj j : Euc d →L[ℝ] ℝ) z‖ ≤ ‖z‖ := PiLp.norm_apply_le z j
  simp only [sa16u_J, LinearMap.sub_apply, LinearMap.smulRight_apply, ContinuousLinearMap.coe_coe]
  refine (norm_sub_le _ _).trans ?_
  rw [norm_smul, norm_smul, PiLp.norm_single, PiLp.norm_single, norm_one, mul_one, mul_one]
  linarith

lemma sa16u_rot_deriv (i j : Fin d) (z : Euc d) (t : ℝ) :
    HasDerivAt (fun t => sa16u_rot i j t z) (-(Real.sin t) • sa16u_P i j z + Real.cos t • sa16u_J i j z) t := by
  have : (fun t => sa16u_rot i j t z) =
      fun t => z + (Real.cos t - 1) • sa16u_P i j z + Real.sin t • sa16u_J i j z := by
    funext t; simp [sa16u_rot]
  rw [this]
  exact (((hasDerivAt_const t z).add (((Real.hasDerivAt_cos t).sub_const 1).smul_const (sa16u_P i j z))).add
    ((Real.hasDerivAt_sin t).smul_const (sa16u_J i j z))).congr_deriv (by simp)

lemma sa16u_rot_zero (i j : Fin d) (z : Euc d) : sa16u_rot i j 0 z = z := by
  simp [sa16u_rot]

/-- the rotation as a measure-preserving isometry -/
def sa16u_rotE (i j : Fin d) (hij : i ≠ j) (t : ℝ) : Euc d ≃ₗᵢ[ℝ] Euc d :=
  (⟨sa16u_rot i j t, sa16u_rot_norm i j hij t⟩ : Euc d →ₗᵢ[ℝ] Euc d).toLinearIsometryEquiv rfl

lemma sa16u_rot_inv (i j : Fin d) (hij : i ≠ j) (t : ℝ) (f : Euc d → ℝ) :
    ∫ z : Euc d, f (sa16u_rot i j t z) = ∫ z : Euc d, f z := by
  have := (sa16u_rotE i j hij t).measurePreserving.integral_comp
    (sa16u_rotE i j hij t).toHomeomorph.measurableEmbedding f
  simpa [sa16u_rotE] using this

lemma sa16u_piece_int (hd : 1 ≤ d) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (v : 𝓢(Euc d, ℝ))
    (k l : Fin d) : Integrable
      (fun z : Euc d => sa16u_kap d θ δ ‖z‖ * (z k * fderiv ℝ v z (EuclideanSpace.single l (1 : ℝ)))) := by
  obtain ⟨C, hC0, hC⟩ := sa16u_grad_bound v
  have hcoord : ∀ (k l : Fin d) (z : Euc d),
      ‖sa16u_kap d θ δ ‖z‖ * (z k * fderiv ℝ v z (EuclideanSpace.single l (1 : ℝ)))‖ ≤
        C * (sa16u_kap d θ δ ‖z‖ * ‖z‖ * ((1 + ‖z‖) ^ (d + 1))⁻¹) := by
    intro k l z
    have h1 : ‖z k‖ ≤ ‖z‖ := PiLp.norm_apply_le z k
    have h2 : ‖fderiv ℝ v z (EuclideanSpace.single l (1 : ℝ))‖ ≤ C * ((1 + ‖z‖) ^ (d + 1))⁻¹ := by
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      rw [PiLp.norm_single, norm_one, mul_one]
      exact hC z
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sa16u_kap_nonneg θ δ (norm_nonneg z) hδ), norm_mul]
    calc sa16u_kap d θ δ ‖z‖ * (‖z k‖ * ‖fderiv ℝ v z (EuclideanSpace.single l (1 : ℝ))‖)
        ≤ sa16u_kap d θ δ ‖z‖ * (‖z‖ * (C * ((1 + ‖z‖) ^ (d + 1))⁻¹)) :=
          mul_le_mul_of_nonneg_left (mul_le_mul h1 h2 (norm_nonneg _) (norm_nonneg _))
            (sa16u_kap_nonneg θ δ (norm_nonneg z) hδ)
      _ = _ := by ring
  refine Integrable.mono' ((sa16u_M_int hd hθ hδ).const_mul C) ?_ (Eventually.of_forall (hcoord k l))
  exact (((sa16u_kap_meas θ δ).comp measurable_norm).aestronglyMeasurable).mul
      ((((EuclideanSpace.proj k : Euc d →L[ℝ] ℝ).continuous).mul
        ((sa16u_fderiv_cont v).clm_apply continuous_const)).aestronglyMeasurable)

theorem sa16u_curl_formula (hd : 1 ≤ d) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (i j : Fin d)
    (v : 𝓢(Euc d, ℝ)) :
    ∫ z : Euc d, sa16u_kap d θ δ ‖z‖ * (z i * fderiv ℝ v z (EuclideanSpace.single j (1 : ℝ))) =
      ∫ z : Euc d, sa16u_kap d θ δ ‖z‖ * (z j * fderiv ℝ v z (EuclideanSpace.single i (1 : ℝ))) := by
  by_cases hij : i = j
  · rw [hij]
  obtain ⟨C, hC0, hC⟩ := sa16u_grad_bound v
  have hint := sa16u_piece_int hd hθ hδ v
  -- constant family
  set Φ : ℝ → ℝ := fun t => ∫ z : Euc d, sa16u_kap d θ δ ‖z‖ * (v (sa16u_rot i j t z) - v 0) with hΦ
  have hconst : Φ = fun _ => ∫ z : Euc d, sa16u_kap d θ δ ‖z‖ * (v z - v 0) := by
    funext t
    simp only [hΦ]
    rw [← sa16u_rot_inv i j hij t (fun w => sa16u_kap d θ δ ‖w‖ * (v w - v 0))]
    refine integral_congr_ae (Eventually.of_forall fun z => ?_)
    simp only [sa16u_rot_norm i j hij t z]
  have h0 : HasDerivAt Φ 0 0 := by rw [hconst]; exact hasDerivAt_const _ _
  have hm : ∀ t : ℝ, AEStronglyMeasurable
      (fun z : Euc d => sa16u_kap d θ δ ‖z‖ * (v (sa16u_rot i j t z) - v 0)) volume := fun t =>
    (((sa16u_kap_meas θ δ).comp measurable_norm).aestronglyMeasurable).mul
      ((v.continuous.comp (sa16u_rot i j t).toContinuousLinearMap.continuous).sub continuous_const).aestronglyMeasurable
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Euc d)))
    (F := fun (t : ℝ) (z : Euc d) => sa16u_kap d θ δ ‖z‖ * (v (sa16u_rot i j t z) - v 0))
    (F' := fun (t : ℝ) (z : Euc d) => sa16u_kap d θ δ ‖z‖ *
      fderiv ℝ v (sa16u_rot i j t z) (-(Real.sin t) • sa16u_P i j z + Real.cos t • sa16u_J i j z))
    (x₀ := 0) (bound := fun z => 4 * C * (sa16u_kap d θ δ ‖z‖ * ‖z‖ * ((1 + ‖z‖) ^ (d + 1))⁻¹))
    (s := Set.univ) Filter.univ_mem (Eventually.of_forall hm)
    (by
      have : (fun z : Euc d => sa16u_kap d θ δ ‖z‖ * (v (sa16u_rot i j 0 z) - v 0)) =
          fun z => sa16u_kap d θ δ ‖z‖ * (v z - v 0) := by funext z; rw [sa16u_rot_zero]
      rw [this]; exact sa16u_G_int hd hθ hδ v)
    (by
      have hc : Continuous fun z : Euc d => fderiv ℝ v (sa16u_rot i j 0 z)
          (-(Real.sin 0) • sa16u_P i j z + Real.cos 0 • sa16u_J i j z) :=
        ((sa16u_fderiv_cont v).comp (LinearMap.continuous_of_finiteDimensional (sa16u_rot i j 0))).clm_apply
          (((LinearMap.continuous_of_finiteDimensional (sa16u_P i j)).const_smul (-(Real.sin 0))).add
            ((LinearMap.continuous_of_finiteDimensional (sa16u_J i j)).const_smul (Real.cos 0)))
      exact (((sa16u_kap_meas θ δ).comp measurable_norm).aestronglyMeasurable).mul hc.aestronglyMeasurable)
    (Eventually.of_forall fun z t _ => ?_)
    (((sa16u_M_int hd hθ hδ).const_mul (4 * C)))
    (Eventually.of_forall fun z t _ => ?_)
  · have hu := h0.unique key.2
    have hF0 : ∀ z : Euc d, sa16u_kap d θ δ ‖z‖ * fderiv ℝ v (sa16u_rot i j 0 z)
        (-(Real.sin 0) • sa16u_P i j z + Real.cos 0 • sa16u_J i j z) =
        sa16u_kap d θ δ ‖z‖ * (z i * fderiv ℝ v z (EuclideanSpace.single j (1 : ℝ))) -
          sa16u_kap d θ δ ‖z‖ * (z j * fderiv ℝ v z (EuclideanSpace.single i (1 : ℝ))) := by
      intro z
      have hJ : sa16u_J i j z = z i • (EuclideanSpace.single j (1 : ℝ) : Euc d) -
          z j • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by simp [sa16u_J]
      rw [sa16u_rot_zero, Real.sin_zero, Real.cos_zero, neg_zero, zero_smul, zero_add, one_smul, hJ,
        map_sub, map_smul, map_smul]
      simp only [smul_eq_mul]
      ring
    simp only [hF0] at hu
    rw [integral_sub (hint i j) (hint j i)] at hu
    linarith
  · have h1 : ‖-(Real.sin t) • sa16u_P i j z + Real.cos t • sa16u_J i j z‖ ≤ 4 * ‖z‖ := by
      refine (norm_add_le _ _).trans ?_
      rw [norm_smul, norm_smul, norm_neg, Real.norm_eq_abs, Real.norm_eq_abs]
      have := Real.abs_sin_le_one t
      have := Real.abs_cos_le_one t
      have h2 := sa16u_P_norm i j z
      have h3 := sa16u_J_norm i j z
      nlinarith [abs_nonneg (Real.sin t), abs_nonneg (Real.cos t), norm_nonneg (sa16u_P i j z),
        norm_nonneg (sa16u_J i j z), norm_nonneg z]
    have h2 : ‖fderiv ℝ v (sa16u_rot i j t z)‖ ≤ C * ((1 + ‖z‖) ^ (d + 1))⁻¹ := by
      have := hC (sa16u_rot i j t z)
      rwa [sa16u_rot_norm i j hij t z] at this
    rw [norm_mul, Real.norm_eq_abs, abs_of_nonneg (sa16u_kap_nonneg θ δ (norm_nonneg z) hδ)]
    calc sa16u_kap d θ δ ‖z‖ * ‖fderiv ℝ v (sa16u_rot i j t z)
          (-(Real.sin t) • sa16u_P i j z + Real.cos t • sa16u_J i j z)‖
        ≤ sa16u_kap d θ δ ‖z‖ * ((C * ((1 + ‖z‖) ^ (d + 1))⁻¹) * (4 * ‖z‖)) :=
          mul_le_mul_of_nonneg_left ((ContinuousLinearMap.le_opNorm _ _).trans
            (mul_le_mul h2 h1 (norm_nonneg _) (by positivity))) (sa16u_kap_nonneg θ δ (norm_nonneg z) hδ)
      _ = _ := by ring
  · have h1 := (v.differentiableAt (x := sa16u_rot i j t z)).hasFDerivAt.comp_hasDerivAt t
      (sa16u_rot_deriv i j z t)
    exact (h1.sub_const (v 0)).const_mul _

/-! ### assembly -/

/-- `z ↦ u (x - z)` as a Schwartz function -/
def sa16u_shift (x : Euc d) (u : 𝓢(Euc d, ℝ)) : 𝓢(Euc d, ℝ) :=
  SchwartzMap.compCLM ℝ (g := fun z : Euc d => x - z) (by fun_prop)
    ⟨1, 1 + ‖x‖, fun z => by
      have : ‖z‖ ≤ ‖x - z‖ + ‖x‖ := by
        calc ‖z‖ = ‖x - (x - z)‖ := by rw [sub_sub_cancel]
          _ ≤ ‖x‖ + ‖x - z‖ := norm_sub_le _ _
          _ = _ := by ring
      nlinarith [norm_nonneg x, norm_nonneg (x - z)]⟩ u

lemma sa16u_shift_apply (x : Euc d) (u : 𝓢(Euc d, ℝ)) (z : Euc d) : sa16u_shift x u z = u (x - z) := rfl

lemma sa16u_shift_fderiv (x : Euc d) (u : 𝓢(Euc d, ℝ)) (z w : Euc d) :
    fderiv ℝ (sa16u_shift x u) z w = -(fderiv ℝ u (x - z) w) := by
  have h : ⇑(sa16u_shift x u) = fun z => u (x - z) := rfl
  rw [h]
  have := (u.differentiableAt (x := x - z)).hasFDerivAt.comp z ((hasFDerivAt_id z).const_sub x)
  have this' : HasFDerivAt (fun z => u (x - z))
      ((fderiv ℝ (⇑u) (x - z)).comp (-ContinuousLinearMap.id ℝ (Euc d))) z := this
  rw [this'.fderiv]
  simp

lemma sa16u_splice_eq (θ δ : ℝ) (u : 𝓢(Euc d, ℝ)) (x : Euc d) (i j : Fin d) :
    spliceOdd d θ δ i (partialDeriv (fun _ : Fin 1 => j) (⇑u)) x =
      -∫ z : Euc d, sa16u_kap d θ δ ‖z‖ *
        (z i * fderiv ℝ (sa16u_shift x u) z (EuclideanSpace.single j (1 : ℝ))) := by
  unfold spliceOdd
  rw [← integral_neg]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [sa16u_kernel, partialDeriv, iteratedFDeriv_one_apply, sa16u_shift_fderiv]
  ring

theorem sa16u_splice_div_curl (hd : 1 ≤ d) {θ δ : ℝ} (hθ : 0 < θ) (hδ : 0 < δ) (u : 𝓢(Euc d, ℝ)) :
    (∀ x, (∑ i : Fin d, spliceOdd d θ δ i
      (partialDeriv (fun _ : Fin 1 => i) (⇑u)) x) = θ * jumpCut d θ δ u x) ∧
    (∀ i j : Fin d, ∀ x, spliceOdd d θ δ i
      (partialDeriv (fun _ : Fin 1 => j) (⇑u)) x =
      spliceOdd d θ δ j (partialDeriv (fun _ : Fin 1 => i) (⇑u)) x) := by
  refine ⟨fun x => ?_, fun i j x => ?_⟩
  · set v := sa16u_shift x u with hv
    simp only [sa16u_splice_eq]
    rw [Finset.sum_neg_distrib, ← integral_finset_sum _ (fun i _ => sa16u_piece_int hd hθ hδ v i i)]
    have hsum : ∀ z : Euc d, ∑ i : Fin d, sa16u_kap d θ δ ‖z‖ *
        (z i * fderiv ℝ v z (EuclideanSpace.single i (1 : ℝ))) = sa16u_kap d θ δ ‖z‖ * fderiv ℝ v z z := by
      intro z
      rw [← Finset.mul_sum]
      congr 1
      have hz : z = ∑ i, z i • (EuclideanSpace.single i (1 : ℝ) : Euc d) := by
        ext k; simp [Finset.sum_apply, Pi.single_apply]
      calc ∑ i : Fin d, z i * fderiv ℝ v z (EuclideanSpace.single i (1 : ℝ))
          = fderiv ℝ v z (∑ i, z i • (EuclideanSpace.single i (1 : ℝ) : Euc d)) := by
            rw [map_sum]; simp [map_smul]
        _ = fderiv ℝ v z z := (congrArg (fderiv ℝ v z) hz).symm
    simp only [hsum]
    rw [sa16u_div_formula hd hθ hδ v]
    have hjc : jumpCut d θ δ u x = - ∫ w : Euc d, {w : Euc d | δ < ‖w‖}.indicator
        (fun w => ‖w‖ ^ (-((d : ℝ) + θ)) * (v w - v 0)) w := by
      unfold jumpCut
      rw [integral_indicator (measurableSet_lt measurable_const measurable_norm), ← integral_neg]
      refine integral_congr_ae (Eventually.of_forall fun z => ?_)
      simp only [hv, sa16u_shift_apply, sub_zero, Real.rpow_neg (norm_nonneg _)]
      ring
    rw [hjc]
    ring
  · simp only [sa16u_splice_eq]
    rw [sa16u_curl_formula hd hθ hδ i j (sa16u_shift x u)]

end K1

/-- K1: the exact divergence and curl identities. The atom at zero
produces the jump mass; normal-flux matching removes a sphere measure. -/
theorem splice_div_curl (d : ℕ) (hd : 1 ≤ d) (θ δ : ℝ)
    (hθ : 0 < θ) (hδ : 0 < δ) (u : SchwartzMap (Euc d) ℝ) :
    (∀ x, (∑ i : Fin d, spliceOdd d θ δ i
      (partialDeriv (fun _ : Fin 1 => i) u) x)=θ*jumpCut d θ δ u x) ∧
    (∀ i j : Fin d, ∀ x, spliceOdd d θ δ i
      (partialDeriv (fun _ : Fin 1 => j) u) x =
      spliceOdd d θ δ j (partialDeriv (fun _ : Fin 1 => i) u) x) :=
  sa16u_splice_div_curl hd hθ hδ u

end HRS.Whole.AppendixA.Phase2SA16Cutoff
