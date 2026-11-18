import HRS.MS.CzElemAux1

/-!
# ELEM-A, part 2: (ii-a) the commutator `[𝒯_θ, a]W`, `1 < θ < 2`

Packet ELEM-A (CZ development), namespace `HRS.CZ.ElemA`.

`elema_kk` is the `L¹` majorant `B·(L_a|z|^{2-d-θ}1_{|z|≤1} + 2B_a|z|^{1-d-θ}1_{|z|>1})` of the commutator kernel
`|K(z)|·|a(x-z)-a(x)|`; it is integrable because `θ < 2` (near `0`) and `θ > 1` (near `∞`).
By `pvOdd_comm_kernel` (PV-API) `𝒯_θ(aW) - a𝒯_θW = ∫K(z)(a(x-z)-a(x))W(x-z)dz` and Young gives the `L^p` bound.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.ElemA

open HRS.CZ.Pv

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

lemma elema_lipschitzWith {f : 𝔼 → ℝ} {L : ℝ} (hL : 0 ≤ L) (h : ∀ x y, |f x - f y| ≤ L * ‖x - y‖) :
    LipschitzWith ⟨L, hL⟩ f :=
  LipschitzWith.of_dist_le_mul fun a b => by
    rw [Real.dist_eq, dist_eq_norm]
    exact h a b

/-- the majorant kernel of the commutator -/
def elema_kk (d : ℕ) (θ B La Ba : ℝ) (z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  if ‖z‖ ≤ 1 then B * La * ‖z‖ ^ (2 - ((d : ℝ) + θ)) else B * (2 * Ba) * ‖z‖ ^ (1 - ((d : ℝ) + θ))

lemma elema_kk_measurable (θ B La Ba : ℝ) : Measurable (elema_kk d θ B La Ba) := by
  unfold elema_kk
  exact Measurable.ite (measurableSet_le measurable_norm measurable_const)
    (measurable_const.mul (measurable_norm.pow_const _)) (measurable_const.mul (measurable_norm.pow_const _))

lemma elema_kk_nonneg (θ B La Ba : ℝ) (hB : 0 ≤ B) (hLa : 0 ≤ La) (hBa : 0 ≤ Ba) (z : 𝔼) :
    0 ≤ elema_kk d θ B La Ba z := by
  unfold elema_kk
  split_ifs
  · exact mul_nonneg (mul_nonneg hB hLa) (Real.rpow_nonneg (norm_nonneg _) _)
  · exact mul_nonneg (mul_nonneg hB (by linarith)) (Real.rpow_nonneg (norm_nonneg _) _)

/-- the `L¹` norm of the majorant kernel is `≤ C₀ (B_a + L_a)` -/
lemma elema_kk_lintegral (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) {B : ℝ} (hB : 0 ≤ B) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ La Ba : ℝ, 0 ≤ La → 0 ≤ Ba →
      ∫⁻ z : 𝔼, ENNReal.ofReal (elema_kk d θ B La Ba z) ≤ ENNReal.ofReal (C0 * (Ba + La)) := by
  have hi1 : Integrable (fun z : 𝔼 => ‖z‖ ^ (-((d : ℝ) + θ - 2))) (volume.restrict (closedBall 0 1)) := by
    have : IntegrableOn (fun z : 𝔼 => ‖z‖ ^ (-((d : ℝ) + θ - 2))) (ball 0 2) :=
      pvapi_integrableOn_ball_rpow hd (α := (d : ℝ) + θ - 2) (by linarith) 2
    exact this.mono_set (closedBall_subset_ball (by norm_num))
  have hi2 : Integrable (fun z : 𝔼 => ‖z‖ ^ (-((d : ℝ) + θ - 1))) (volume.restrict {z : 𝔼 | 1 < ‖z‖}) :=
    pvapi_integrableOn_tail_rpow hd (s := (d : ℝ) + θ - 1) (by linarith)
  set I1 := ∫⁻ z in closedBall (0 : 𝔼) 1, ENNReal.ofReal (‖z‖ ^ (-((d : ℝ) + θ - 2))) with hI1
  set I2 := ∫⁻ z in {z : 𝔼 | 1 < ‖z‖}, ENNReal.ofReal (‖z‖ ^ (-((d : ℝ) + θ - 1))) with hI2
  have hI1t : I1 ≠ ⊤ := hi1.lintegral_lt_top.ne
  have hI2t : I2 ≠ ⊤ := hi2.lintegral_lt_top.ne
  refine ⟨B * (I1.toReal + 2 * I2.toReal), mul_nonneg hB (by positivity), fun La Ba hLa hBa => ?_⟩
  have hsplit : ∫⁻ z : 𝔼, ENNReal.ofReal (elema_kk d θ B La Ba z) =
      (∫⁻ z in closedBall (0 : 𝔼) 1, ENNReal.ofReal (elema_kk d θ B La Ba z)) +
        ∫⁻ z in {z : 𝔼 | 1 < ‖z‖}, ENNReal.ofReal (elema_kk d θ B La Ba z) := by
    rw [← lintegral_union pvapi_tail_meas pvapi_ball_tail_disjoint, pvapi_ball_union_tail, setLIntegral_univ]
  have hball : ∫⁻ z in closedBall (0 : 𝔼) 1, ENNReal.ofReal (elema_kk d θ B La Ba z) =
      ENNReal.ofReal (B * La) * I1 := by
    rw [← pvapi_ofReal_B_mul _ (mul_nonneg hB hLa)]
    refine setLIntegral_congr_fun measurableSet_closedBall (fun z hz => ?_)
    have hz' : ‖z‖ ≤ 1 := by simpa using hz
    simp only [elema_kk, if_pos hz']
    congr 2
    congr 1
    ring
  have htail : ∫⁻ z in {z : 𝔼 | 1 < ‖z‖}, ENNReal.ofReal (elema_kk d θ B La Ba z) =
      ENNReal.ofReal (B * (2 * Ba)) * I2 := by
    rw [← pvapi_ofReal_B_mul _ (mul_nonneg hB (by linarith))]
    refine setLIntegral_congr_fun pvapi_tail_meas (fun z hz => ?_)
    have hz' : ¬ ‖z‖ ≤ 1 := not_le.2 hz
    simp only [elema_kk, if_neg hz']
    congr 2
    congr 1
    ring
  rw [hsplit, hball, htail]
  conv_lhs => rw [← ENNReal.ofReal_toReal hI1t, ← ENNReal.ofReal_toReal hI2t]
  rw [← ENNReal.ofReal_mul (mul_nonneg hB hLa), ← ENNReal.ofReal_mul (mul_nonneg hB (by linarith)),
    ← ENNReal.ofReal_add (mul_nonneg (mul_nonneg hB hLa) ENNReal.toReal_nonneg)
      (mul_nonneg (mul_nonneg hB (by linarith)) ENNReal.toReal_nonneg)]
  refine ENNReal.ofReal_le_ofReal ?_
  have h1 := ENNReal.toReal_nonneg (a := I1)
  have h2 := ENNReal.toReal_nonneg (a := I2)
  nlinarith [mul_nonneg hB (mul_nonneg hLa h1), mul_nonneg hB (mul_nonneg hLa h2),
    mul_nonneg hB (mul_nonneg hBa h1), mul_nonneg hB (mul_nonneg hBa h2)]


/-- the pointwise bound of the commutator kernel by `elema_kk` -/
lemma elema_comm_kernel_le (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) {Ω : 𝔼 → ℝ} {B : ℝ} (hK : IsPvKernel Ω B)
    {a : 𝔼 → ℝ} {Ba La : ℝ} (hBa : 0 ≤ Ba) (hLa : 0 ≤ La) (hab : ∀ y, |a y| ≤ Ba)
    (hal : ∀ x y, |a x - a y| ≤ La * ‖x - y‖) (x z : 𝔼) (w : ℝ) :
    ‖pvK d θ Ω z * ((a (x - z) - a x) * w)‖ₑ ≤ ENNReal.ofReal (elema_kk d θ B La Ba z) * ‖w‖ₑ := by
  have hθ0 : 0 < θ := by linarith
  rw [← ofReal_norm (w), ← ENNReal.ofReal_mul (elema_kk_nonneg θ B La Ba hK.nonneg hLa hBa z),
    ← ofReal_norm]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, abs_mul]
  by_cases hz : z = 0
  · subst hz
    simp [pvK_zero hd hθ0]
    exact mul_nonneg (elema_kk_nonneg θ B La Ba hK.nonneg hLa hBa 0) (abs_nonneg _)
  · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
    have hK1 := pvK_abs_le hd hθ0 hK z
    have hd1 : |a (x - z) - a x| ≤ La * ‖z‖ := by
      have := hal (x - z) x
      simpa using this
    have hd2 : |a (x - z) - a x| ≤ 2 * Ba := by
      have h1 := hab (x - z)
      have h2 := hab x
      calc |a (x - z) - a x| ≤ |a (x - z)| + |a x| := abs_sub _ _
        _ ≤ 2 * Ba := by linarith
    have hKB : 0 ≤ B * ‖z‖ ^ (1 - ((d : ℝ) + θ)) := mul_nonneg hK.nonneg (Real.rpow_nonneg hn.le _)
    have hW := abs_nonneg w
    have hmul : |pvK d θ Ω z| * |a (x - z) - a x| ≤ elema_kk d θ B La Ba z := by
      unfold elema_kk
      split_ifs with h
      · calc |pvK d θ Ω z| * |a (x - z) - a x| ≤ (B * ‖z‖ ^ (1 - ((d : ℝ) + θ))) * (La * ‖z‖) :=
              mul_le_mul hK1 hd1 (abs_nonneg _) hKB
          _ = B * La * ‖z‖ ^ (2 - ((d : ℝ) + θ)) := by
              have : (2 - ((d : ℝ) + θ)) = (1 - ((d : ℝ) + θ)) + 1 := by ring
              rw [this, Real.rpow_add hn, Real.rpow_one]
              ring
      · calc |pvK d θ Ω z| * |a (x - z) - a x| ≤ (B * ‖z‖ ^ (1 - ((d : ℝ) + θ))) * (2 * Ba) :=
              mul_le_mul hK1 hd2 (abs_nonneg _) hKB
          _ = B * (2 * Ba) * ‖z‖ ^ (1 - ((d : ℝ) + θ)) := by ring
    calc |pvK d θ Ω z| * (|a (x - z) - a x| * |w|) = (|pvK d θ Ω z| * |a (x - z) - a x|) * |w| := by ring
      _ ≤ elema_kk d θ B La Ba z * |w| := mul_le_mul_of_nonneg_right hmul hW

/-- (ii-a), pointwise form for Schwartz `W` and Lipschitz bounded `a` -/
lemma elema_comm_pointwise (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) {a : 𝔼 → ℝ} {Ba La : ℝ} (hBa : 0 ≤ Ba) (hLa : 0 ≤ La) (hab : ∀ y, |a y| ≤ Ba)
    (hal : ∀ x y, |a x - a y| ≤ La * ‖x - y‖) (W : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    HRS.Whole.AppendixA.pvOdd d θ Ω (fun y => a y * W y) x - a x * HRS.Whole.AppendixA.pvOdd d θ Ω W x =
      ∫ z, pvK d θ Ω z * ((a (x - z) - a x) * W (x - z)) := by
  have hθ0 : 0 < θ := by linarith
  obtain ⟨BW, LW, MW, hW⟩ := PvC2.of_schwartz W
  exact (pvOdd_comm_kernel hd hθ0 hθ2 hK (elema_lipschitzWith hLa hal) hab hW.lipschitzWith W.integrable
    hW.bdd x).2

lemma elema_comm_aesm {θ : ℝ} {Ω : 𝔼 → ℝ} {B : ℝ} (hK : IsPvKernel Ω B) {a : 𝔼 → ℝ} (ha : Continuous a)
    (W : 𝓢(𝔼, ℝ)) :
    AEStronglyMeasurable (fun x : 𝔼 => ∫ z, pvK d θ Ω z * ((a (x - z) - a x) * W (x - z))) volume := by
  have hF : Measurable (fun p : 𝔼 × 𝔼 => pvK d θ Ω p.2 * ((a (p.1 - p.2) - a p.1) * W (p.1 - p.2))) :=
    ((pvK_measurable hK θ).comp measurable_snd).mul
      (((ha.measurable.comp (measurable_fst.sub measurable_snd)).sub (ha.measurable.comp measurable_fst)).mul
        (W.continuous.measurable.comp (measurable_fst.sub measurable_snd)))
  exact (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable

/-- (ii-a), the `L^p` bound with explicit data -/
theorem elema_positive_order_bound (hd : 1 ≤ d) {θ : ℝ} (hθ1 : 1 < θ) (hθ2 : θ < 2) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) :
    ∃ C0 : ℝ, 0 ≤ C0 ∧ ∀ (p : ℝ), 1 ≤ p → ∀ (a : 𝔼 → ℝ) (Ba La : ℝ), 0 ≤ Ba → 0 ≤ La → Continuous a →
      (∀ y, |a y| ≤ Ba) → (∀ x y, |a x - a y| ≤ La * ‖x - y‖) → ∀ W : 𝓢(𝔼, ℝ),
      eLpNorm (fun x => HRS.Whole.AppendixA.pvOdd d θ Ω (fun y => a y * W y) x -
          a x * HRS.Whole.AppendixA.pvOdd d θ Ω W x) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C0 * (Ba + La)) * eLpNorm W (ENNReal.ofReal p) volume := by
  obtain ⟨C0, hC0, hkk⟩ := elema_kk_lintegral hd hθ1 hθ2 hK.nonneg
  refine ⟨C0, hC0, fun p hp a Ba La hBa hLa hac hab hal W => ?_⟩
  have hfun : (fun x => HRS.Whole.AppendixA.pvOdd d θ Ω (fun y => a y * W y) x -
      a x * HRS.Whole.AppendixA.pvOdd d θ Ω W x) =
      fun x : 𝔼 => ∫ z, pvK d θ Ω z * ((a (x - z) - a x) * W (x - z)) :=
    funext fun x => elema_comm_pointwise hd hθ1 hθ2 hK hBa hLa hab hal W x
  rw [hfun]
  refine (elema_young (elema_kk_measurable θ B La Ba) W.continuous.measurable
    (elema_comm_aesm hK hac W) hp (fun x => ?_)).trans (mul_le_mul_left (hkk La Ba hLa hBa) _)
  refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
  exact elema_comm_kernel_le hd hθ1 hK hBa hLa hab hal x z (W (x - z))

/-- **(ii-a)**: the first conjunct of the frozen `lp_positive_order_product` (`AppendixAAdjoint.lean:913`), with the
frozen hypotheses (`2 ≤ p` only needs `1 ≤ p`; `IsOddSmooth Ω` only boundedness/oddness on the sphere). -/
theorem lp_positive_order_product_first_conjunct (hd : 1 ≤ d) (θ p : ℝ) (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hp : 2 ≤ p) (Ω : Euc d → ℝ) (hΩ : HRS.Whole.AppendixA.IsOddSmooth Ω) :
    ∃ C : ℝ, ∀ a : Euc d → ℝ, HRS.MemCb 1 a →
      ∀ W : SchwartzMap (Euc d) ℝ,
        eLpNorm (fun x => HRS.Whole.AppendixA.pvOdd d θ Ω (fun y => a y * W y) x -
            a x * HRS.Whole.AppendixA.pvOdd d θ Ω W x)
            (ENNReal.ofReal p) volume ≤
          ENNReal.ofReal (C * HRS.cbNorm 1 a) * eLpNorm W (ENNReal.ofReal p) volume := by
  obtain ⟨B, hK⟩ := isPvKernel_of_oddSmooth hΩ
  obtain ⟨C0, hC0, hb⟩ := elema_positive_order_bound hd hθ1 hθ2 hK
  refine ⟨C0, fun a ha W => ?_⟩
  obtain ⟨Ba, La, hBa, hLa, hcb, hab, hal⟩ := elema_cb1_data ha
  rw [hcb]
  exact hb p (by linarith) a Ba La hBa hLa (ha.1.continuous) hab hal W

end HRS.CZ.ElemA
