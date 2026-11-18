import HRS.Torus.Basic
import HRS.MS.WhoAux3

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal

namespace HRS.Fp81.S21

open HRS HRS.MS.Ul HRS.MS.Who HRS.Whole

local notation "J" => iteratedFDeriv ℝ

theorem fp81s21_b3_near_integrable_of_continuous {d : ℕ} (hd : 1 ≤ d)
    {κ : Euc d → ℝ} {s : ℝ} (hK : UlKer κ s) (hs : s + 1 < d)
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : Euc d → F} (hg : Continuous g) (x : Euc d) :
    Integrable (fun z => ultKN κ z • (g (x - z) - g x)) volume := by
  have hmass := who_nearMass_lt_top hd hK hs
  have hκ : Integrable (ultKN κ) volume := by
    refine ⟨(ultKN_meas hK.meas).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have heq : (∫⁻ z, ‖ultKN κ z‖ₑ ∂volume) = nearMass κ := by
      simp [nearMass, Real.enorm_eq_ofReal_abs]
    rw [heq]
    exact hmass
  have hclosed : IsCompact (closedBall x (1 / 4 : ℝ)) := isCompact_closedBall x _
  obtain ⟨C₀, hC₀⟩ := hclosed.exists_bound_of_continuousOn (s := closedBall x (1 / 4 : ℝ)) (f := g) hg.continuousOn
  let C : ℝ := max C₀ 0
  have hC : 0 ≤ C := le_max_right _ _
  have hCbnd : ∀ y ∈ closedBall x (1 / 4 : ℝ), ‖g y‖ ≤ C := by
    intro y hy
    exact (hC₀ y hy).trans (le_max_left _ _)
  have hdom : Integrable (fun z => (2 * C) * |ultKN κ z|) volume := by
    simpa [mul_comm] using hκ.norm.const_mul (2 * C)
  refine hdom.mono' (ult_near_meas hK.meas hg x) ?_
  filter_upwards [] with z
  by_cases hz : ‖z‖ ≤ 1 / 4
  · have hxz : x - z ∈ closedBall x (1 / 4 : ℝ) := by
      simpa [mem_closedBall, dist_eq_norm] using hz
    have hxx : x ∈ closedBall x (1 / 4 : ℝ) := by simp
    have hdiff : ‖g (x - z) - g x‖ ≤ 2 * C := by
      calc
        ‖g (x - z) - g x‖ ≤ ‖g (x - z)‖ + ‖g x‖ := norm_sub_le _ _
        _ ≤ C + C := add_le_add (hCbnd _ hxz) (hCbnd _ hxx)
        _ = 2 * C := by ring
    calc
      ‖ultKN κ z • (g (x - z) - g x)‖
          = ‖ultKN κ z‖ * ‖g (x - z) - g x‖ := norm_smul _ _
      _ ≤ ‖ultKN κ z‖ * (2 * C) := mul_le_mul_of_nonneg_left hdiff (norm_nonneg _)
      _ = (2 * C) * |ultKN κ z| := by rw [Real.norm_eq_abs]; ring
  · have hz' : ¬ ‖z‖ ≤ (4 : ℝ)⁻¹ := by simpa using hz
    simp [ultKN, hz']

theorem fp81s21_b3_far_integrable {d : ℕ} {κ : Euc d → ℝ} {s C₀ : ℝ}
    (hK : UlKer κ s) (hC₀ : 0 ≤ C₀)
    (hκb : ∀ z : Euc d, z ≠ 0 → ‖κ z‖ ≤ C₀ * ‖z‖ ^ (-(s + 1)))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : Euc d → F} (hg : Continuous g) (hgi : Integrable g) (x : Euc d) :
    Integrable (fun z => ultKF κ z • g (x - z)) volume := by
  let Bf : ℝ := C₀ * (1 / 4 : ℝ) ^ (-(s + 1))
  have hBf : 0 ≤ Bf := by positivity
  have hshift : Integrable (fun z => ‖g (x - z)‖) volume := hgi.norm.comp_sub_left x
  have hdom : Integrable (fun z => Bf * ‖g (x - z)‖) volume := by
    simpa [Bf, mul_comm] using hshift.const_mul Bf
  refine hdom.mono' ((ultKF_meas hK.meas).aestronglyMeasurable.smul
    ((hg.comp (continuous_const.sub continuous_id)).aestronglyMeasurable)) ?_
  filter_upwards [] with z
  rw [norm_smul]
  exact mul_le_mul_of_nonneg_right
    (ult_far_bound hC₀ hκb hK.hs0 z) (norm_nonneg _)

theorem fp81s21_b3_far_l1_bound {d : ℕ} {κ : Euc d → ℝ} {s C₀ : ℝ}
    (hK : UlKer κ s) (hC₀ : 0 ≤ C₀)
    (hκb : ∀ z : Euc d, z ≠ 0 → ‖κ z‖ ≤ C₀ * ‖z‖ ^ (-(s + 1)))
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {g : Euc d → F} (hgi : Integrable g) (x : Euc d) :
    ‖u2Conv (ultKF κ) g x‖ ≤ C₀ * (1 / 4 : ℝ) ^ (-(s + 1)) *
      (eLpNorm g 1 volume).toReal := by
  let Bf : ℝ := C₀ * (1 / 4 : ℝ) ^ (-(s + 1))
  have hBf : 0 ≤ Bf := by positivity
  have hshift : Integrable (fun z => ‖g (x - z)‖) volume := hgi.norm.comp_sub_left x
  have hdom : Integrable (fun z => Bf * ‖g (x - z)‖) volume := by
    simpa [Bf, mul_comm] using hshift.const_mul Bf
  have hpt : ∀ z, ‖ultKF κ z • g (x - z)‖ ≤ Bf * ‖g (x - z)‖ := by
    intro z
    rw [norm_smul]
    exact mul_le_mul_of_nonneg_right
      (ult_far_bound hC₀ hκb hK.hs0 z) (norm_nonneg _)
  have hshiftLp : ∫ z, ‖g (x - z)‖ = (eLpNorm g 1 volume).toReal := by
    calc
      ∫ z, ‖g (x - z)‖ = (∫⁻ z, ENNReal.ofReal ‖g (x - z)‖ ∂volume).toReal := by
        simpa only [norm_norm, Real.enorm_of_nonneg (norm_nonneg _)] using
          (integral_norm_eq_lintegral_enorm hshift.aestronglyMeasurable)
      _ = (∫⁻ y, ENNReal.ofReal ‖g y‖ ∂volume).toReal := by
        congr 1
        exact lintegral_sub_left_eq_self (fun y => ENNReal.ofReal ‖g y‖) x
      _ = (eLpNorm g 1 volume).toReal := by
        congr 1
        simp_rw [ofReal_norm]
        rw [← eLpNorm_one_eq_lintegral_enorm hgi.aestronglyMeasurable]
  have hLp : ∫ y, ‖g y‖ = (eLpNorm g 1 volume).toReal := by
    calc
      ∫ y, ‖g y‖ = (∫⁻ y, ‖g y‖ₑ ∂volume).toReal :=
        integral_norm_eq_lintegral_enorm hgi.aestronglyMeasurable
      _ = (eLpNorm g 1 volume).toReal := by
        rw [← eLpNorm_one_eq_lintegral_enorm hgi.aestronglyMeasurable]
  calc
    ‖u2Conv (ultKF κ) g x‖ ≤ ∫ z, Bf * ‖g (x - z)‖ :=
      norm_integral_le_of_norm_le hdom (ae_of_all _ hpt)
    _ = Bf * ∫ z, ‖g (x - z)‖ := by rw [integral_const_mul]
    _ = Bf * (eLpNorm g 1 volume).toReal := by rw [hshiftLp]
    _ = C₀ * (1 / 4 : ℝ) ^ (-(s + 1)) * (eLpNorm g 1 volume).toReal := by rfl

theorem fp81s21_b3_ultK_tendsto_local {d : ℕ}
    {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    [CompleteSpace F]
    (hd : 1 ≤ d) {κ : Euc d → ℝ} {s : ℝ}
    (hκ : UlKer κ s) (hs : s + 1 < d)
    {gn : ℕ → Euc d → F} {g : Euc d → F}
    (hcn : ∀ n, Continuous (gn n)) (hc : Continuous g)
    (hin : ∀ n, Integrable (gn n)) (hi : Integrable g)
    (ht : TendstoLocallyUniformly gn g atTop)
    (hL1 : Tendsto
      (fun n => eLpNorm (gn n - g) 1 volume) atTop (𝓝 0)) :
    TendstoLocallyUniformly
      (fun n => ultK κ (gn n)) (ultK κ g) atTop := by
  obtain ⟨C₀, hC₀, hκb⟩ := ult_ker_bound hκ
  let Bf : ℝ := C₀ * (1 / 4 : ℝ) ^ (-(s + 1))
  have hBf : 0 ≤ Bf := by positivity
  have hnearMass := who_nearMass_lt_top hd hκ hs
  have hnearKernel : Integrable (ultKN κ) volume := by
    refine ⟨(ultKN_meas hκ.meas).aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_enorm]
    have heq : (∫⁻ z, ‖ultKN κ z‖ₑ ∂volume) = nearMass κ := by
      simp [nearMass, Real.enorm_eq_ofReal_abs]
    rw [heq]
    exact hnearMass
  have hnearMassReal : ∫ z, ‖ultKN κ z‖ = (nearMass κ).toReal := by
    rw [integral_norm_eq_lintegral_enorm hnearKernel.aestronglyMeasurable]
    simp [nearMass, Real.enorm_eq_ofReal_abs]
  rw [tendstoLocallyUniformly_iff_forall_isCompact]
  intro K hKcompact
  rw [Metric.tendstoUniformlyOn_iff]
  intro ε hε
  let E : Set (Euc d) :=
    (fun p : Euc d × Euc d => p.1 - p.2) '' (K ×ˢ closedBall (0 : Euc d) (1 / 4 : ℝ))
  have hE : IsCompact E := by
    dsimp [E]
    exact (hKcompact.prod (isCompact_closedBall (0 : Euc d) (1 / 4 : ℝ))).image (continuous_fst.sub continuous_snd)
  have hsource : TendstoUniformlyOn gn g atTop E :=
    (tendstoLocallyUniformly_iff_forall_isCompact.mp ht) E hE
  have hsourceEvent : ∀ᶠ n in atTop, ∀ y ∈ E, ‖gn n y - g y‖ < ε / (8 * ((nearMass κ).toReal + 1)) := by
    rw [Metric.tendstoUniformlyOn_iff] at hsource
    have hη : 0 < ε / (8 * ((nearMass κ).toReal + 1)) := by positivity
    filter_upwards [hsource (ε / (8 * ((nearMass κ).toReal + 1))) hη] with n hn
    intro y hy
    have hdist := hn y hy
    simpa [dist_eq_norm, norm_sub_rev] using hdist
  have hτ : 0 < ε / (8 * (Bf + 1)) := by positivity
  have hL1Event : ∀ᶠ n in atTop,
      eLpNorm (gn n - g) 1 volume < ENNReal.ofReal (ε / (8 * (Bf + 1))) := by
    filter_upwards [hL1.eventually (Iio_mem_nhds
      (ENNReal.ofReal_pos.mpr hτ))] with n hn
    simpa using hn
  have hnearSmall : 2 * (ε / (8 * ((nearMass κ).toReal + 1))) * (nearMass κ).toReal ≤ ε / 4 := by
    have ha' : (nearMass κ).toReal ≤ (nearMass κ).toReal + 1 := by linarith
    have he : 0 ≤ ε := hε.le
    have hprod := mul_le_mul_of_nonneg_left ha' he
    have hden : 0 < (nearMass κ).toReal + 1 := by positivity
    field_simp
    nlinarith
  have hfarSmall : Bf * (ε / (8 * (Bf + 1))) ≤ ε / 8 := by
    have hb' : Bf ≤ Bf + 1 := by linarith
    have he : 0 ≤ ε := hε.le
    have hprod := mul_le_mul_of_nonneg_left hb' he
    calc
      Bf * (ε / (8 * (Bf + 1))) = ε * Bf / (8 * (Bf + 1)) := by ring
      _ ≤ ε / 8 := by
        apply (div_le_iff₀ (by positivity)).2
        nlinarith
  filter_upwards [hsourceEvent, hL1Event] with n hsrc hln
  intro x hx
  have hδint : Integrable (fun y => gn n y - g y) volume := (hin n).sub hi
  have hnearIntN := fp81s21_b3_near_integrable_of_continuous hd hκ hs (hcn n) x
  have hnearIntG := fp81s21_b3_near_integrable_of_continuous hd hκ hs hc x
  have hfarIntN := fp81s21_b3_far_integrable hκ hC₀ hκb (hcn n) (hin n) x
  have hfarIntG := fp81s21_b3_far_integrable hκ hC₀ hκb hc hi x
  have hnearSub : ultNear κ (gn n) x - ultNear κ g x =
      ultNear κ (fun y => gn n y - g y) x := by
    unfold ultNear
    rw [← integral_sub hnearIntN hnearIntG]
    congr 1
    funext z
    rw [← smul_sub]
    congr 1
    module
  have hfarSub : u2Conv (ultKF κ) (gn n) x - u2Conv (ultKF κ) g x =
      u2Conv (ultKF κ) (fun y => gn n y - g y) x := by
    unfold u2Conv
    rw [← integral_sub hfarIntN hfarIntG]
    congr 1
    funext z
    rw [← smul_sub]
  have hKSub : ultK κ (gn n) x - ultK κ g x =
      ultK κ (fun y => gn n y - g y) x := by
    calc
      ultK κ (gn n) x - ultK κ g x =
          (ultNear κ (gn n) x - ultNear κ g x) +
            (u2Conv (ultKF κ) (gn n) x - u2Conv (ultKF κ) g x) := by
          unfold ultK
          abel
      _ = ultNear κ (fun y => gn n y - g y) x +
            u2Conv (ultKF κ) (fun y => gn n y - g y) x := by rw [hnearSub, hfarSub]
      _ = ultK κ (fun y => gn n y - g y) x := rfl
  have hdeltaNear : ‖ultNear κ (fun y => gn n y - g y) x‖ ≤
      2 * (ε / (8 * ((nearMass κ).toReal + 1))) * (nearMass κ).toReal := by
    have hdom : Integrable (fun z =>
        (2 * (ε / (8 * ((nearMass κ).toReal + 1)))) * ‖ultKN κ z‖) volume := by
      simpa [mul_comm] using hnearKernel.norm.const_mul
        (2 * (ε / (8 * ((nearMass κ).toReal + 1))))
    have hpt : ∀ z, ‖ultKN κ z •
        ((gn n (x - z) - g (x - z)) - (gn n x - g x))‖ ≤
        (2 * (ε / (8 * ((nearMass κ).toReal + 1)))) * ‖ultKN κ z‖ := by
      intro z
      by_cases hz : ‖z‖ ≤ 1 / 4
      · have hxE : x ∈ E := by
          dsimp [E]
          refine ⟨(x, 0), ⟨hx, ?_⟩, ?_⟩ <;> simp [mem_closedBall]
        have hxzE : x - z ∈ E := by
          dsimp [E]
          refine ⟨(x, z), ⟨hx, ?_⟩, rfl⟩
          simpa [mem_closedBall, dist_eq_norm] using hz
        have hdiff : ‖(gn n (x - z) - g (x - z)) - (gn n x - g x)‖ ≤
            2 * (ε / (8 * ((nearMass κ).toReal + 1))) := by
          calc
            _ ≤ ‖gn n (x - z) - g (x - z)‖ + ‖gn n x - g x‖ := norm_sub_le _ _
            _ ≤ ε / (8 * ((nearMass κ).toReal + 1)) +
                ε / (8 * ((nearMass κ).toReal + 1)) :=
              add_le_add (le_of_lt (hsrc _ hxzE)) (le_of_lt (hsrc _ hxE))
            _ = _ := by ring
        calc
          ‖ultKN κ z •
              ((gn n (x - z) - g (x - z)) - (gn n x - g x))‖
              = ‖ultKN κ z‖ *
                  ‖(gn n (x - z) - g (x - z)) - (gn n x - g x)‖ := norm_smul _ _
          _ ≤ (2 * (ε / (8 * ((nearMass κ).toReal + 1)))) * ‖ultKN κ z‖ := by
              rw [mul_comm]
              exact mul_le_mul_of_nonneg_right hdiff (norm_nonneg _)
      · have hz' : ¬ ‖z‖ ≤ (4 : ℝ)⁻¹ := by simpa using hz
        simp [ultKN, hz']
    calc
      _ ≤ ∫ z, (2 * (ε / (8 * ((nearMass κ).toReal + 1)))) * ‖ultKN κ z‖ :=
        norm_integral_le_of_norm_le hdom (ae_of_all _ hpt)
      _ = 2 * (ε / (8 * ((nearMass κ).toReal + 1))) *
          (nearMass κ).toReal := by rw [integral_const_mul, hnearMassReal]
  have hdeltaFar : ‖u2Conv (ultKF κ) (fun y => gn n y - g y) x‖ ≤
      Bf * (eLpNorm (gn n - g) 1 volume).toReal := by
    exact fp81s21_b3_far_l1_bound hκ hC₀ hκb hδint x
  have htoReal : (eLpNorm (gn n - g) 1 volume).toReal < ε / (8 * (Bf + 1)) :=
    ENNReal.toReal_lt_of_lt_ofReal hln
  have hfarEstimate : ‖u2Conv (ultKF κ) (fun y => gn n y - g y) x‖ ≤ ε / 8 := by
    calc
      ‖u2Conv (ultKF κ) (fun y => gn n y - g y) x‖ ≤
          Bf * (eLpNorm (gn n - g) 1 volume).toReal := hdeltaFar
      _ ≤ Bf * (ε / (8 * (Bf + 1))) :=
        mul_le_mul_of_nonneg_left htoReal.le hBf
      _ ≤ ε / 8 := hfarSmall
  have hnearEstimate : ‖ultNear κ (fun y => gn n y - g y) x‖ ≤ ε / 4 :=
    hdeltaNear.trans hnearSmall
  have hpoint : dist (ultK κ g x) (ultK κ (gn n) x) < ε := by
    have htriangle : ‖ultK κ (gn n) x - ultK κ g x‖ ≤
        ‖ultNear κ (fun y => gn n y - g y) x‖ +
          ‖u2Conv (ultKF κ) (fun y => gn n y - g y) x‖ := by
      rw [hKSub]
      simpa [ultK] using norm_add_le
        (ultNear κ (fun y => gn n y - g y) x)
        (u2Conv (ultKF κ) (fun y => gn n y - g y) x)
    have hsum : ‖ultNear κ (fun y => gn n y - g y) x‖ +
        ‖u2Conv (ultKF κ) (fun y => gn n y - g y) x‖ ≤ ε / 4 + ε / 8 :=
      add_le_add hnearEstimate hfarEstimate
    have : ‖ultK κ (gn n) x - ultK κ g x‖ ≤ ε / 4 + ε / 8 := htriangle.trans hsum
    have hε' : ε / 4 + ε / 8 < ε := by linarith
    have hdistance : dist (ultK κ g x) (ultK κ (gn n) x) ≤ ε / 4 + ε / 8 := by
      simpa [dist_eq_norm, norm_sub_rev] using this
    exact hdistance.trans_lt hε'
  exact hpoint

#print axioms HRS.Fp81.S21.fp81s21_b3_ultK_tendsto_local

end HRS.Fp81.S21
