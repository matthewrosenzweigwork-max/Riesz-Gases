import HRS.MC.S7FCBKer

/-!
# FC-B, part 5: the envelope inequality `(K ⊗ K) * W ≤ C W`

Abstract form: for a nonnegative density `K` with `K ≤ Γ` outside the ball `‖a‖ ≤ t/4` and a nonnegative
radial weight `W` with `W ≤ Φh` outside the ball `‖v‖ < t/2` and `∫_{‖v‖<t/2} W ≤ J`, the double average of `W`
at `x - y` (with `‖x - y‖ = t`) is at most `Φh + 2 Γ J`.
-/

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.Sec7.FCB

open HRS HRS.KernelAux

variable {d : ℕ}

theorem fcb_env_abstract (K W : Torus d → ℝ) (hK0 : ∀ x, 0 ≤ K x) (hKm : Measurable K)
    (hW0 : ∀ v, 0 ≤ W v) (hWm : Measurable W)
    (hK1 : ∫⁻ a, ENNReal.ofReal (K a) = 1) {t Γ J Φh : ℝ} (hΦh0 : 0 ≤ Φh) (hJ0 : 0 ≤ J) (ht : 0 < t) (hΓ0 : 0 ≤ Γ)
    (hΓ : ∀ a : Torus d, t / 4 < ‖a‖ → K a ≤ Γ)
    (hΦh : ∀ v : Torus d, t / 2 ≤ ‖v‖ → W v ≤ Φh)
    (hJ : ∫⁻ v, {v : Torus d | ‖v‖ < t / 2}.indicator (fun v => ENNReal.ofReal (W v)) v ≤ ENNReal.ofReal J)
    (x y : Torus d) (hxy : ‖x - y‖ = t) :
    ∫⁻ q : Torus d × Torus d, ENNReal.ofReal (K (x - q.1)) * ENNReal.ofReal (K (y - q.2)) *
        ENNReal.ofReal (W (q.1 - q.2)) ∂(volume.prod volume)
      ≤ ENNReal.ofReal (Φh + 2 * Γ * J) := by
  set z : Torus d := x - y with hz
  -- change of variables
  have hmp : MeasurePreserving (fun q : Torus d × Torus d => (x - q.1, y - q.2))
      (volume.prod volume) (volume.prod volume) :=
    (Measure.measurePreserving_sub_left volume x).prod (Measure.measurePreserving_sub_left volume y)
  set F : Torus d × Torus d → ℝ≥0∞ := fun p =>
    ENNReal.ofReal (K p.1) * ENNReal.ofReal (K p.2) * ENNReal.ofReal (W (z - p.1 + p.2)) with hF
  have hFm : Measurable F := by
    refine ((ENNReal.measurable_ofReal.comp (hKm.comp measurable_fst)).mul
      (ENNReal.measurable_ofReal.comp (hKm.comp measurable_snd))).mul
      (ENNReal.measurable_ofReal.comp (hWm.comp ((measurable_const.sub measurable_fst).add measurable_snd)))
  have hchange : ∫⁻ q : Torus d × Torus d, ENNReal.ofReal (K (x - q.1)) * ENNReal.ofReal (K (y - q.2)) *
        ENNReal.ofReal (W (q.1 - q.2)) ∂(volume.prod volume) = ∫⁻ p, F p ∂(volume.prod volume) := by
    rw [← hmp.lintegral_comp hFm]
    refine lintegral_congr fun q => ?_
    simp only [hF]
    congr 3
    rw [hz]; abel
  rw [hchange]
  -- pointwise decomposition
  set S : Torus d × Torus d → ℝ≥0∞ := fun p =>
    {v : Torus d | ‖v‖ < t / 2}.indicator (fun v => ENNReal.ofReal (W v)) (z - p.1 + p.2) with hS
  have hSm : Measurable S := by
    refine Measurable.comp (g := {v : Torus d | ‖v‖ < t / 2}.indicator (fun v => ENNReal.ofReal (W v)))
      ?_ ((measurable_const.sub measurable_fst).add measurable_snd)
    exact (ENNReal.measurable_ofReal.comp hWm).indicator (measurableSet_lt measurable_norm measurable_const)
  set A : Torus d × Torus d → ℝ≥0∞ := fun p =>
    ENNReal.ofReal Φh * (ENNReal.ofReal (K p.1) * ENNReal.ofReal (K p.2)) with hA
  set B1 : Torus d × Torus d → ℝ≥0∞ := fun p => ENNReal.ofReal Γ * (ENNReal.ofReal (K p.2) * S p) with hB1
  set B2 : Torus d × Torus d → ℝ≥0∞ := fun p => ENNReal.ofReal Γ * (ENNReal.ofReal (K p.1) * S p) with hB2
  have hpt : ∀ p : Torus d × Torus d, F p ≤ A p + (B1 p + B2 p) := by
    intro p
    obtain ⟨a, b⟩ := p
    by_cases hbig : t / 2 ≤ ‖z - a + b‖
    · have : ENNReal.ofReal (W (z - a + b)) ≤ ENNReal.ofReal Φh :=
        ENNReal.ofReal_le_ofReal (hΦh _ hbig)
      calc F (a, b) = ENNReal.ofReal (K a) * ENNReal.ofReal (K b) * ENNReal.ofReal (W (z - a + b)) := rfl
        _ ≤ ENNReal.ofReal (K a) * ENNReal.ofReal (K b) * ENNReal.ofReal Φh := by gcongr
        _ = A (a, b) := by simp only [hA]; ring
        _ ≤ _ := le_self_add
    · push Not at hbig
      have hSv : S (a, b) = ENNReal.ofReal (W (z - a + b)) := by
        simp [hS, Set.indicator, hbig]
      have hab : t / 2 < ‖a‖ + ‖b‖ := by
        have h1 : ‖z‖ ≤ ‖z - (a - b)‖ + ‖a - b‖ := by
          calc ‖z‖ = ‖(z - (a - b)) + (a - b)‖ := by congr 1; abel
            _ ≤ _ := norm_add_le _ _
        have h2 : ‖a - b‖ ≤ ‖a‖ + ‖b‖ := norm_sub_le _ _
        have h3 : z - (a - b) = z - a + b := by abel
        rw [h3] at h1
        have : ‖z‖ = t := hxy
        linarith
      rcases lt_or_ge (t / 4) ‖a‖ with ha | ha
      · have hKa : ENNReal.ofReal (K a) ≤ ENNReal.ofReal Γ := ENNReal.ofReal_le_ofReal (hΓ a ha)
        calc F (a, b) = ENNReal.ofReal (K a) * ENNReal.ofReal (K b) * ENNReal.ofReal (W (z - a + b)) := rfl
          _ ≤ ENNReal.ofReal Γ * ENNReal.ofReal (K b) * ENNReal.ofReal (W (z - a + b)) := by gcongr
          _ = B1 (a, b) := by simp only [hB1, hSv]; ring
          _ ≤ A (a, b) + (B1 (a, b) + B2 (a, b)) := (le_self_add : B1 (a, b) ≤ B1 (a, b) + B2 (a, b)).trans le_add_self
      · have hb : t / 4 < ‖b‖ := by linarith
        have hKb : ENNReal.ofReal (K b) ≤ ENNReal.ofReal Γ := ENNReal.ofReal_le_ofReal (hΓ b hb)
        calc F (a, b) = ENNReal.ofReal (K a) * ENNReal.ofReal (K b) * ENNReal.ofReal (W (z - a + b)) := rfl
          _ ≤ ENNReal.ofReal (K a) * ENNReal.ofReal Γ * ENNReal.ofReal (W (z - a + b)) := by gcongr
          _ = B2 (a, b) := by simp only [hB2, hSv]; ring
          _ ≤ A (a, b) + (B1 (a, b) + B2 (a, b)) := (le_add_self : B2 (a, b) ≤ B1 (a, b) + B2 (a, b)).trans le_add_self
  -- measurability
  have hKe : Measurable fun a => ENNReal.ofReal (K a) := ENNReal.measurable_ofReal.comp hKm
  have hAin : Measurable fun p : Torus d × Torus d => ENNReal.ofReal (K p.1) * ENNReal.ofReal (K p.2) :=
    (hKe.comp measurable_fst).mul (hKe.comp measurable_snd)
  have hB1in : Measurable fun p : Torus d × Torus d => ENNReal.ofReal (K p.2) * S p :=
    (hKe.comp measurable_snd).mul hSm
  have hB2in : Measurable fun p : Torus d × Torus d => ENNReal.ofReal (K p.1) * S p :=
    (hKe.comp measurable_fst).mul hSm
  have hAm : Measurable A := measurable_const.mul ((hKe.comp measurable_fst).mul (hKe.comp measurable_snd))
  have hB1m : Measurable B1 := measurable_const.mul ((hKe.comp measurable_snd).mul hSm)
  have hB2m : Measurable B2 := measurable_const.mul ((hKe.comp measurable_fst).mul hSm)
  set Sf : Torus d → ℝ≥0∞ := {v : Torus d | ‖v‖ < t / 2}.indicator (fun v => ENNReal.ofReal (W v)) with hSf
  have hSfm : Measurable Sf :=
    (ENNReal.measurable_ofReal.comp hWm).indicator (measurableSet_lt measurable_norm measurable_const)
  -- the three integrals
  have iA : ∫⁻ p, A p ∂(volume.prod volume) = ENNReal.ofReal Φh := by
    simp only [hA]
    rw [lintegral_const_mul _ hAin,
      lintegral_prod_mul hKe.aemeasurable hKe.aemeasurable, hK1, one_mul, mul_one]
  have iB1 : ∫⁻ p, B1 p ∂(volume.prod volume) ≤ ENNReal.ofReal Γ * ENNReal.ofReal J := by
    simp only [hB1]
    rw [lintegral_const_mul _ hB1in, lintegral_prod_symm _ hB1in.aemeasurable]
    gcongr
    calc ∫⁻ b, ∫⁻ a, ENNReal.ofReal (K (a, b).2) * S (a, b) ≤ ∫⁻ b, ENNReal.ofReal (K b) * ENNReal.ofReal J := by
          refine lintegral_mono fun b => ?_
          simp only
          have hm : Measurable fun a => S (a, b) := hSm.comp (measurable_id.prodMk measurable_const)
          rw [lintegral_const_mul _ hm]
          gcongr
          have : ∫⁻ a, S (a, b) = ∫⁻ a, Sf ((z + b) - a) := by
            refine lintegral_congr fun a => ?_
            simp only [hS, hSf]; congr 2; abel
          rw [this, (Measure.measurePreserving_sub_left volume (z + b)).lintegral_comp hSfm]
          exact hJ
      _ = ENNReal.ofReal J := by rw [lintegral_mul_const _ hKe, hK1, one_mul]
  have iB2 : ∫⁻ p, B2 p ∂(volume.prod volume) ≤ ENNReal.ofReal Γ * ENNReal.ofReal J := by
    simp only [hB2]
    rw [lintegral_const_mul _ hB2in, lintegral_prod _ hB2in.aemeasurable]
    gcongr
    calc ∫⁻ a, ∫⁻ b, ENNReal.ofReal (K (a, b).1) * S (a, b) ≤ ∫⁻ a, ENNReal.ofReal (K a) * ENNReal.ofReal J := by
          refine lintegral_mono fun a => ?_
          simp only
          have hm : Measurable fun b => S (a, b) := hSm.comp (measurable_const.prodMk measurable_id)
          rw [lintegral_const_mul _ hm]
          gcongr
          have : ∫⁻ b, S (a, b) = ∫⁻ b, Sf ((z - a) + b) := by
            refine lintegral_congr fun b => ?_
            simp only [hS, hSf]
          rw [this, (measurePreserving_add_left volume (z - a)).lintegral_comp hSfm]
          exact hJ
      _ = ENNReal.ofReal J := by rw [lintegral_mul_const _ hKe, hK1, one_mul]
  calc ∫⁻ p, F p ∂(volume.prod volume) ≤ ∫⁻ p, (A p + (B1 p + B2 p)) ∂(volume.prod volume) := lintegral_mono hpt
    _ = ∫⁻ p, A p ∂(volume.prod volume) + (∫⁻ p, B1 p ∂(volume.prod volume) + ∫⁻ p, B2 p ∂(volume.prod volume)) := by
        rw [lintegral_add_left hAm, lintegral_add_left hB1m]
    _ ≤ ENNReal.ofReal Φh + (ENNReal.ofReal Γ * ENNReal.ofReal J + ENNReal.ofReal Γ * ENNReal.ofReal J) := by
        rw [iA]; gcongr
    _ = ENNReal.ofReal (Φh + 2 * Γ * J) := by
        rw [← ENNReal.ofReal_mul hΓ0, ← ENNReal.ofReal_add (mul_nonneg hΓ0 hJ0) (mul_nonneg hΓ0 hJ0),
          ← ENNReal.ofReal_add hΦh0 (add_nonneg (mul_nonneg hΓ0 hJ0) (mul_nonneg hΓ0 hJ0))]
        congr 1; ring

theorem fcb_pow_exp_le (d : ℕ) : ∃ M : ℝ, 0 < M ∧ ∀ u : ℝ, 0 ≤ u → u ^ d * Real.exp (-(u ^ 2 / 4)) ≤ M := by
  refine ⟨1 + 4 ^ d * (d.factorial : ℝ), by positivity, fun u hu => ?_⟩
  have hfac : (0 : ℝ) < d.factorial := by exact_mod_cast d.factorial_pos
  by_cases hu1 : u ≤ 1
  · have h1 : u ^ d ≤ 1 := pow_le_one₀ hu hu1
    have h2 : Real.exp (-(u ^ 2 / 4)) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [sq_nonneg u]
    have h3 : 0 ≤ Real.exp (-(u ^ 2 / 4)) := (Real.exp_pos _).le
    calc u ^ d * Real.exp (-(u ^ 2 / 4)) ≤ 1 * 1 := mul_le_mul h1 h2 h3 zero_le_one
      _ ≤ _ := by nlinarith [show (0 : ℝ) ≤ 4 ^ d * d.factorial by positivity]
  · push Not at hu1
    have h1 : u ^ d ≤ (u ^ 2) ^ d := by
      rw [← pow_mul]
      exact pow_le_pow_right₀ hu1.le (by nlinarith [Nat.zero_le d] : d ≤ 2 * d)
    have h2 := Real.pow_div_factorial_le_exp (u ^ 2 / 4) (by positivity) d
    have h3 : (u ^ 2) ^ d = 4 ^ d * (u ^ 2 / 4) ^ d := by
      rw [div_pow, mul_div_cancel₀ _ (by positivity)]
    have h4 : (u ^ 2 / 4) ^ d ≤ d.factorial * Real.exp (u ^ 2 / 4) := by
      rwa [div_le_iff₀ hfac, mul_comm] at h2
    have hexp : Real.exp (-(u ^ 2 / 4)) * Real.exp (u ^ 2 / 4) = 1 := by
      rw [← Real.exp_add]; simp
    calc u ^ d * Real.exp (-(u ^ 2 / 4)) ≤ (4 ^ d * (u ^ 2 / 4) ^ d) * Real.exp (-(u ^ 2 / 4)) := by
          rw [← h3]; gcongr
      _ ≤ (4 ^ d * (d.factorial * Real.exp (u ^ 2 / 4))) * Real.exp (-(u ^ 2 / 4)) := by gcongr
      _ = 4 ^ d * d.factorial * (Real.exp (-(u ^ 2 / 4)) * Real.exp (u ^ 2 / 4)) := by ring
      _ ≤ _ := by rw [hexp]; linarith

theorem fcb_Phi_nonneg {s : ℝ} (hs0 : 0 ≤ s) {t : ℝ} (ht : 0 ≤ t) : 0 ≤ fcbPhi s t := by
  rcases ht.eq_or_lt with h | h
  · subst h
    unfold fcbPhi singEnvelope
    rw [min_eq_left (by norm_num)]
    by_cases h0 : s = 0
    · simp [h0]
    · simp [h0, Real.zero_rpow (neg_ne_zero.mpr h0)]
  · exact (fcb_Phi_pos hs0 h).le

theorem fcb_envelope (hd : 0 < d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < d) :
    ∃ Cenv : ℝ, 0 < Cenv ∧ ∀ (n : ℕ), 1 ≤ n → ∀ x y : Torus d, x ≠ y →
      ∫⁻ q : Torus d × Torus d, ENNReal.ofReal (fcbK d n (x - q.1)) * ENNReal.ofReal (fcbK d n (y - q.2)) *
        ENNReal.ofReal (fcbPhi s ‖q.1 - q.2‖) ∂(volume.prod volume)
        ≤ ENNReal.ofReal (Cenv * fcbPhi s ‖x - y‖) := by
  obtain ⟨Jc, hJc, hJ⟩ := fcb_ball_lintegral hd hs0 hs
  obtain ⟨M, hM, hMle⟩ := fcb_pow_exp_le d
  have hP12 := fcb_Phi_ge_one hs0 (show (0 : ℝ) < 1 / 2 by norm_num)
  refine ⟨fcbPhi s (1 / 2) * (1 + 2 * Jc * 3 ^ d * M), by positivity, fun n hn x y hxy => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hsq : 0 < Real.sqrt n := Real.sqrt_pos.2 (by linarith)
  have ht0 : 0 < ‖x - y‖ := norm_pos_iff.mpr (sub_ne_zero.mpr hxy)
  have ht2 : ‖x - y‖ ≤ 1 / 2 := fcb_norm_le_half _
  generalize ht : ‖x - y‖ = t at ht0 ht2
  set Γ : ℝ := (6 * Real.sqrt n) ^ d * Real.exp (-(4 * n * (t / 4) ^ 2)) with hΓdef
  have hΓ0 : 0 ≤ Γ := by positivity
  have hK1 : ∫⁻ a, ENNReal.ofReal (fcbK d n a) = 1 := by
    rw [← ofReal_integral_eq_lintegral_ofReal (fcbK_integrable n)
      (Eventually.of_forall fun a => fcbK_nonneg hd hn a), fcbK_integral hd hn]
    simp
  have hPh : 0 < fcbPhi s (t / 2) := fcb_Phi_pos hs0 (by positivity)
  have hW0 : ∀ v : Torus d, 0 ≤ fcbPhi s ‖v‖ := fun v => fcb_Phi_nonneg hs0 (norm_nonneg v)
  have hΓ : ∀ a : Torus d, t / 4 < ‖a‖ → fcbK d n a ≤ Γ := by
    intro a ha
    refine (fcbK_le hd hn a).trans ?_
    rw [hΓdef]
    refine mul_le_mul_of_nonneg_left (Real.exp_le_exp.mpr ?_) (by positivity)
    have h1 : (t / 4) ^ 2 ≤ ‖a‖ ^ 2 := by
      apply pow_le_pow_left₀ (by positivity) ha.le
    nlinarith
  have hΦh : ∀ v : Torus d, t / 2 ≤ ‖v‖ → fcbPhi s ‖v‖ ≤ fcbPhi s (t / 2) :=
    fun v hv => fcb_Phi_anti hs0 (by positivity) hv
  have hJb : ∫⁻ v : Torus d, {v : Torus d | ‖v‖ < t / 2}.indicator
      (fun v => ENNReal.ofReal (fcbPhi s ‖v‖)) v ≤ ENNReal.ofReal (Jc * (t / 2) ^ d * fcbPhi s (t / 2)) :=
    hJ (t / 2) (by positivity) (by linarith)
  have hbound := fcb_env_abstract (fcbK d n) (fun v => fcbPhi s ‖v‖) (fcbK_nonneg hd hn)
    (fcbK_continuous n).measurable hW0 (fcb_measurable_Phi_norm s) hK1
    hPh.le (by positivity) ht0 hΓ0 hΓ hΦh hJb x y ht
  refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
  -- the real inequality
  have hu := hMle (Real.sqrt n * t) (by positivity)
  have hG : Γ * (t / 2) ^ d ≤ 3 ^ d * M := by
    have e3 : (Real.sqrt n * t) ^ 2 = n * t ^ 2 := by
      rw [mul_pow, Real.sq_sqrt (by linarith)]
    have e1 : Γ * (t / 2) ^ d = 3 ^ d * ((Real.sqrt n * t) ^ d * Real.exp (-((Real.sqrt n * t) ^ 2 / 4))) := by
      calc Γ * (t / 2) ^ d = ((6 * Real.sqrt n) * (t / 2)) ^ d * Real.exp (-(4 * n * (t / 4) ^ 2)) := by
            rw [hΓdef, mul_pow (6 * Real.sqrt n) (t / 2) d]; ring
        _ = (3 * (Real.sqrt n * t)) ^ d * Real.exp (-((Real.sqrt n * t) ^ 2 / 4)) := by
            congr 2
            · ring
            · rw [e3]; ring
        _ = _ := by rw [mul_pow]; ring
    rw [e1]; gcongr
  have hPhalf := fcb_Phi_half hs0 ht0
  have hPt := fcb_Phi_ge_one hs0 ht0
  calc fcbPhi s (t / 2) + 2 * Γ * (Jc * (t / 2) ^ d * fcbPhi s (t / 2))
      = fcbPhi s (t / 2) * (1 + 2 * Jc * (Γ * (t / 2) ^ d)) := by ring
    _ ≤ fcbPhi s (t / 2) * (1 + 2 * Jc * (3 ^ d * M)) := by gcongr
    _ ≤ (fcbPhi s (1 / 2) * fcbPhi s t) * (1 + 2 * Jc * (3 ^ d * M)) := by gcongr
    _ = _ := by ring

end HRS.MC.Sec7.FCB
