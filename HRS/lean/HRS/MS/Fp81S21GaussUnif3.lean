import HRS.MS.Fp81S21GaussUnif2
import HRS.MS.ProClosureS111PathMoments
import HRS.MP.KolmChentsov

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS (Euc)
open HRS.Whole HRS.MS.R26T3 HRS.MS.ProClosureS111

private theorem fp81s21_gauss_unif_enorm_fourth_real {E : Type*} [NormedAddCommGroup E] (x : E) :
    ENNReal.ofReal (‖x‖ ^ 4) = ‖x‖ₑ ^ (4 : ℝ) := by
  rw [← ofReal_norm]
  exact (ENNReal.ofReal_pow (norm_nonneg x) 4).trans
    (ENNReal.rpow_natCast (ENNReal.ofReal ‖x‖) 4).symm

/-- Uniform fourth-moment bound for every supplied Gaussian realization's
shifted window. The bound is chosen before the shift and realization. -/
theorem fp81s21_gauss_unif_window_fourth (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∀ H : ℝ, 0 < H →
          ∃ B4 : ℝ, 0 ≤ B4 ∧
            ∀ a : ℝ, 0 ≤ a → ∀ G : GaussianRealization R,
              Integrable (fun ω =>
                ‖processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω‖ ^ 4) G.P ∧
              (∫ ω,
                ‖processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω‖ ^ 4 ∂G.P) ≤ B4 := by
  obtain ⟨δT, hδT, hδThalf, hTrace⟩ := fp81s21_gauss_unif_trace p
  obtain ⟨δI, hδI, hδIhalf, hInc⟩ :=
    fp81s21_gauss_unif_increment_fourth p
  let δ0 : ℝ := min δT δI
  have hδ0 : 0 < δ0 := lt_min hδT hδI
  have hδ0half : δ0 ≤ 1 / 2 :=
    (min_le_left _ _).trans hδThalf
  refine ⟨δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R H hH
  have hδT' : δ ≤ δT := hδle.trans (min_le_left _ _)
  have hδI' : δ ≤ δI := hδle.trans (min_le_right _ _)
  obtain ⟨V, hV, hTraceR⟩ := hTrace δ hδ hδT' R
  obtain ⟨L, hL0, hLsum, hIncR⟩ := hInc δ hδ hδI' R H hH
  let C : ℝ := 3 * (∑' α : MultiIndex p.d, L α) ^ 2
  have hsumL0 : 0 ≤ ∑' α : MultiIndex p.d, L α := tsum_nonneg hL0
  have hC0 : 0 ≤ C := by dsimp [C]; positivity
  let r : ℝ := 9 / 10
  let q : ℝ := 9 / 10
  have hr0 : 0 < r := by norm_num [r]
  have hr1 : r < 1 := by norm_num [r]
  have hq0 : 0 < q := by norm_num [q]
  have hq1 : q < 1 := by norm_num [q]
  have hrKC : 1 < 2 * r ^ 4 := by norm_num [r]
  have hqr : 1 ≤ q * 2 ^ (1 : ℝ) * r ^ (4 : ℝ) := by norm_num [q, r]
  have hden : 0 < 1 - 1 / (2 * r ^ 4) := by
    have hfrac : 1 / (2 * r ^ 4) < 1 := (div_lt_one (by positivity)).2 hrKC
    linarith
  let B4 : ℝ := 8 * (3 * V ^ 2 + (HRS.MP.KC.mkc_c r) ^ 4 *
    (C * H ^ 2 / (1 - 1 / (2 * r ^ 4))))
  have hkc0 : 0 ≤ HRS.MP.KC.mkc_c r := by
    unfold HRS.MP.KC.mkc_c
    positivity
  have hB40 : 0 ≤ B4 := by
    dsimp [B4]
    apply mul_nonneg (by norm_num)
    apply add_nonneg
    · positivity
    · exact mul_nonneg (pow_nonneg hkc0 4)
        (div_nonneg (mul_nonneg hC0 (sq_nonneg H)) hden.le)
  refine ⟨B4, hB40, ?_⟩
  intro a ha G
  let X : ℝ → G.Ω → OscDual p.d (wholeSpaceIndex p.d : ℝ) :=
    fun t ω => G.Z (max (a + t) 0) ω
  have hX : ∀ t, Measurable (X t) := by
    intro t
    let u : ℝ := max (a + t) 0
    have hu : 0 ≤ u := by dsimp [u]; exact le_max_right _ _
    simpa [X, u] using (G.evolution (u + 1)).meas u
  have hInitEnn :
      ∫⁻ ω, ‖X 0 ω‖ₑ ^ (4 : ℝ) ∂G.P ≤ ENNReal.ofReal (3 * V ^ 2) := by
    simpa [X, max_eq_left ha] using
      fp81s21_gauss_unif_one_time_fourth p R V ⟨hV, hTraceR⟩ a ha G
  have hInitOfReal :
      (∫⁻ ω, ENNReal.ofReal (‖X 0 ω‖ ^ 4) ∂G.P) ≤ ENNReal.ofReal (3 * V ^ 2) := by
    calc
      _ = ∫⁻ ω, ‖X 0 ω‖ₑ ^ (4 : ℝ) ∂G.P := by
        apply lintegral_congr
        intro ω
        exact fp81s21_gauss_unif_enorm_fourth_real (X 0 ω)
      _ ≤ ENNReal.ofReal (3 * V ^ 2) := hInitEnn
  have hX04 : MemLp (X 0) 4 G.P := by
    change eLpNorm (X 0) 4 G.P < ⊤
    exact (eLpNorm_lt_top_iff_lintegral_rpow_enorm_lt_top
      (by norm_num : (4 : ℝ≥0∞) ≠ 0)
      (by norm_num : (4 : ℝ≥0∞) ≠ ⊤)
      (hX 0).aestronglyMeasurable).2
      (by simpa only [ENNReal.toReal_ofNat] using
        hInitEnn.trans_lt ENNReal.ofReal_lt_top)
  have hX0int : (∫ ω, ‖X 0 ω‖ ^ 4 ∂G.P) ≤ 3 * V ^ 2 := by
    have hXi : Integrable (fun ω => ‖X 0 ω‖ ^ 4) G.P :=
      hX04.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0)
    have he := ofReal_integral_eq_lintegral_ofReal hXi
      (ae_of_all _ fun ω => by positivity)
    have hbound : ENNReal.ofReal (∫ ω, ‖X 0 ω‖ ^ 4 ∂G.P) ≤
        ENNReal.ofReal (3 * V ^ 2) := by
      rw [he]
      exact hInitOfReal
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hbound
  have hmomEnn : ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
      ∫⁻ ω, ‖X t ω - X s ω‖ₑ ^ (4 : ℝ) ∂G.P ≤
        ENNReal.ofReal (C * |t - s| ^ 2) := by
    intro s hs t ht
    have hs0 : 0 ≤ a + s := by linarith [ha, hs.1]
    have ht0 : 0 ≤ a + t := by linarith [ha, ht.1]
    have hraw := hIncR a ha G s hs t ht
    calc
      _ = ∫⁻ ω, ‖G.Z (a + t) ω - G.Z (a + s) ω‖ₑ ^ (4 : ℝ) ∂G.P := by
        apply lintegral_congr
        intro ω
        simp [X, max_eq_left ht0, max_eq_left hs0]
      _ ≤ ENNReal.ofReal
          (3 * (∑' α : MultiIndex p.d, L α) ^ 2 * |t - s| ^ 2) := hraw
      _ = ENNReal.ofReal (C * |t - s| ^ 2) := by rfl
  have hmomReal : ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
      ∫⁻ ω, ENNReal.ofReal (‖X t ω - X s ω‖ ^ 4) ∂G.P ≤
        ENNReal.ofReal (C * |t - s| ^ 2) := by
    intro s hs t ht
    calc
      _ = ∫⁻ ω, ‖X t ω - X s ω‖ₑ ^ (4 : ℝ) ∂G.P := by
        apply lintegral_congr
        exact fun ω => fp81s21_gauss_unif_enorm_fourth_real (X t ω - X s ω)
      _ ≤ ENNReal.ofReal (C * |t - s| ^ 2) := hmomEnn s hs t ht
  have hpow (x : ℝ) (hx : 0 ≤ x) : x ^ (1 + (1 : ℝ)) = x ^ (2 : ℕ) := by
    rw [show (1 : ℝ) + 1 = 2 by norm_num]
    exact Real.rpow_natCast x 2
  have hmomKC : ∀ s ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc (0 : ℝ) H,
      ∫⁻ ω, ‖X t ω - X s ω‖ₑ ^ (4 : ℝ) ∂G.P ≤
        ENNReal.ofReal (C * |t - s| ^ (1 + (1 : ℝ))) := by
    intro s hs t ht
    rw [hpow |t - s| (abs_nonneg _)]
    exact hmomEnn s hs t ht
  have hYmem :=
    continuous_modification_memLp_four_of_fourth_increments G.P X hH hr0 hr1 hrKC
      hX hX04 hC0 hmomReal
  have hYbound :=
    continuous_modification_fourth_moment_bound G.P X hH hr0 hr1 hrKC
      hX hX04 hC0 hmomReal
  let W : G.Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H := fun ω =>
    processWindow (wholeSpaceIndex p.d : ℝ) H a G.Z ω
  let Y : G.Ω → OscPath p.d (wholeSpaceIndex p.d : ℝ) H := fun ω =>
    HRS.Whole.AppendixALemmas.contPathOf H
      (fun t => HRS.MP.KC.mkc_Zc X H r t ω)
  have hTbig : 0 < a + H := by linarith [ha, hH]
  have hcontAe :
      ∀ᵐ ω ∂G.P, ContinuousOn (fun t => G.Z t ω) (Icc (0 : ℝ) (a + H)) :=
    (G.evolution (a + H)).cont
  have hwindowCont :
      ∀ᵐ ω ∂G.P, ContinuousOn (fun t : ℝ => G.Z (a + t) ω) (Icc (0 : ℝ) H) := by
    filter_upwards [hcontAe] with ω hω
    have hshift : ContinuousOn (fun t : ℝ => a + t) (Icc (0 : ℝ) H) :=
      (continuous_const.add continuous_id).continuousOn
    have hmaps : MapsTo (fun t : ℝ => a + t) (Icc (0 : ℝ) H)
        (Icc (0 : ℝ) (a + H)) := by
      intro t ht
      constructor <;> dsimp <;> linarith [ha, ht.1, ht.2]
    exact hω.comp hshift hmaps
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Icc (0 : ℝ) H)
  haveI : Countable D := hDc.to_subtype
  have hWae : W =ᵐ[G.P] Y := by
    have hall : ∀ᵐ ω ∂G.P, ∀ t : D,
        HRS.MP.KC.mkc_Zc X H r t.1 ω = X t.1 ω := by
      apply ae_all_iff.2
      intro t
      exact HRS.MP.KC.mkc_Zc_ae_eq X H r G.P hX
        (p := 4) (β := 1) (C := C) (q := q)
        hH (by norm_num : 0 < (4 : ℝ)) one_pos hmomKC
        hr0 hr1 hq0 hq1 hqr t.1.2
    filter_upwards [hwindowCont, hall] with ω hωcont hw
    have hPathCont :
        Continuous (fun t : Set.Icc (0 : ℝ) H => G.Z (a + t.1) ω) :=
      continuousOn_iff_continuous_restrict.mp hωcont
    have hfun :
        (fun t : Set.Icc (0 : ℝ) H => OscPath.at' (W ω) t) =
          (fun t => OscPath.at' (Y ω) t) := by
      apply Continuous.ext_on hDd
        (show Continuous (fun t : Set.Icc (0 : ℝ) H => OscPath.at' (W ω) t) from
          (W ω).continuous)
        (show Continuous (fun t : Set.Icc (0 : ℝ) H => OscPath.at' (Y ω) t) from
          (Y ω).continuous)
      intro t ht
      have hwmod := hw ⟨t, ht⟩
      have hWAt : OscPath.at' (W ω) t = X t.1 ω := by
        simp [W, HRS.Whole.processWindow, HRS.Whole.windowPathOf, OscPath.at',
          hPathCont]
        change G.Z (a + t.1) ω = G.Z (max (a + t.1) 0) ω
        rw [max_eq_left (add_nonneg ha t.2.1)]
      have hYAt : OscPath.at' (Y ω) t = HRS.MP.KC.mkc_Zc X H r t.1 ω :=
        HRS.MP.KC.mkc_contPathOf_apply X hH hr0.le hr1 ω t
      change OscPath.at' (W ω) t = OscPath.at' (Y ω) t
      rw [hWAt, hYAt]
      exact hwmod.symm
    exact ContinuousMap.ext fun t => congrFun hfun t
  have hWmem : MemLp W 4 G.P := (memLp_congr_ae hWae).2 hYmem
  have hWint : (∫ ω, ‖W ω‖ ^ 4 ∂G.P) ≤ B4 := by
    have hnormAE : (fun ω => ‖W ω‖ ^ 4) =ᵐ[G.P] fun ω => ‖Y ω‖ ^ 4 :=
      hWae.mono fun ω h => by change ‖W ω‖ ^ 4 = ‖Y ω‖ ^ 4; rw [h]
    rw [integral_congr_ae hnormAE]
    calc
      _ ≤ 8 * ((∫ ω, ‖X 0 ω‖ ^ 4 ∂G.P) +
          (HRS.MP.KC.mkc_c r) ^ 4 *
            (C * H ^ 2 / (1 - 1 / (2 * r ^ 4)))) := hYbound
      _ ≤ B4 := by
        dsimp [B4]
        exact mul_le_mul_of_nonneg_left (add_le_add hX0int le_rfl) (by norm_num)
  refine ⟨hWmem.integrable_norm_pow (by norm_num : (4 : ℕ) ≠ 0), hWint⟩

#print axioms fp81s21_gauss_unif_window_fourth

end HRS.Fp81.S21

end
