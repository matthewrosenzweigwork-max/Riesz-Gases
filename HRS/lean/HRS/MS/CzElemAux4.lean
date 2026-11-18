import HRS.MS.CzElemAux3

/-!
# ELEM-A, part 4: (iii-c) and (iii-a)

Packet ELEM-A (CZ development), namespace `HRS.CZ.ElemA`.

* `lp_Lambda_commutator_expansion_proof` (iii-c): the frozen `lp_Lambda_commutator_expansion`
  (`AppendixAAdjoint.lean:939`) with the existential `c_θ` instantiated by `1` (the normalisation of `fracLap`
  omits the constant, so `c_θ = 1`: `𝒯^{(i)}_θ` with `Ω(u) = u_i` has kernel `z_i |z|^{-d-θ}`, exactly the linear part
  of `μ(x) - μ(x-z)`).  The remainder is the absolutely convergent integral of `R(x,z) W(x-z)|z|^{-d-θ}` with
  `|R| ≤ min((‖D²μ‖/2)|z|², 2‖μ‖_∞ + ‖Dμ‖_∞|z|)` (`elema_expansion_repr`); the kernel is in `L¹` for `1 < θ < 2`
  (`elema_kk`), so Young's inequality gives the `L^p` bound.
* `lp_Lambda_commutator_low_lt_one_proof` (iii-a, `0 < θ < 1`): the frozen `lp_Lambda_commutator_low` for `θ < 1`
  with the frozen bound `cbNorm 1 μ` (`min(‖Dμ‖|z|, 2‖μ‖_∞)|z|^{-d-θ} ∈ L¹`, Young).
* `lp_Lambda_commutator_low_cb2` (iii-a/iii-b with `cbNorm 2`, `0 < θ ≤ 1`): for `θ = 1` the commutator contains
  `∑_i ∂_iμ 𝒯^{(i)}_1 W`, the Riesz transforms, so it is NOT elementary: the change `cbNorm 1 → cbNorm 2`
  does not remove the Calderón–Zygmund input.  The theorem is therefore stated with the hypothesis
  `ElemTruncBound d p CR` (uniform `L^p` bound of the truncations `pvTrunc d 1 (u_i) ε`, `ε > 0`, on Schwartz `W`,
  the deliverable of PV-ASM) for `θ = 1`; everything else (Taylor remainder, far kernel, Fatou passage from the
  uniform truncation bound to the principal value `elema_pvOdd_Lp_of_trunc`, decomposition
  `elema_lamComm_decomp`) is proved here.
-/

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal ContDiff SchwartzMap

noncomputable section

namespace HRS.CZ.ElemA

open HRS.CZ.Pv

variable {d : ℕ}
local notation "𝔼" => EuclideanSpace ℝ (Fin d)

/-- **(iii-c)**: the frozen `lp_Lambda_commutator_expansion` (`c_θ = 1`) -/
theorem lp_Lambda_commutator_expansion_proof (hd : 1 ≤ d) (θ p : ℝ) (hθ1 : 1 < θ) (hθ2 : θ < 2)
    (hp : 2 ≤ p) :
    ∃ cθ C : ℝ, ∀ μ : Euc d → ℝ, HRS.MemCb 2 μ → ∀ W : SchwartzMap (Euc d) ℝ,
      eLpNorm (fun x => HRS.Whole.AppendixA.lamComm d θ μ W x - cθ * ∑ i : Fin d,
          gradient μ x i * HRS.Whole.AppendixA.pvOdd d θ (fun u : Euc d => u i) W x)
          (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * HRS.cbNorm 2 μ) * eLpNorm W (ENNReal.ofReal p) volume := by
  obtain ⟨C0, hC0, hkk⟩ := elema_kk_lintegral hd hθ1 hθ2 (B := 1) zero_le_one
  refine ⟨1, C0, fun μ hμ W => ?_⟩
  have hμ2 : ContDiff ℝ 2 μ := by simpa using hμ.1
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hcb, -, h0, h1, h2⟩ := elema_cb2_data hμ
  have hfun : (fun x => HRS.Whole.AppendixA.lamComm d θ μ W x - 1 * ∑ i : Fin d,
      gradient μ x i * HRS.Whole.AppendixA.pvOdd d θ (fun u : Euc d => u i) W x) =
      fun x : 𝔼 => ∫ z, elema_G d θ μ W x z := by
    funext x
    rw [one_mul]
    exact (elema_expansion_repr hd hθ1 hθ2 hμ W x).2
  rw [hfun]
  have hFm : AEStronglyMeasurable (fun x : 𝔼 => ∫ z, elema_G d θ μ W x z) volume :=
    ((elema_G_measurable_prod (θ := θ) hμ2.continuous (hμ2.continuous_fderiv (by norm_num))
      W.continuous).stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
  have hbound := hkk (B2 / 2) (B0 + B1 / 2) (by linarith) (by linarith)
  refine (elema_young (elema_kk_measurable θ 1 (B2 / 2) (B0 + B1 / 2)) W.continuous.measurable hFm
    (by linarith) (fun x => ?_)).trans (mul_le_mul_left ?_ _)
  · refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
    exact elema_G_le hμ2 hB0 hB1 hB2 h0 h1 h2 x z
  · refine hbound.trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hcb]
    exact mul_le_mul_of_nonneg_left (by linarith) hC0

/-! ### (iii-a) `0 < θ < 1`: the commutator kernel is absolutely integrable -/

/-- the commutator integrand `(μ(x)-μ(x-z)) W(x-z) |z|^{-(d+θ)}` -/
def elema_H (d : ℕ) (θ : ℝ) (μ W : EuclideanSpace ℝ (Fin d) → ℝ) (x z : EuclideanSpace ℝ (Fin d)) : ℝ :=
  (μ x - μ (x - z)) * W (x - z) / ‖z‖ ^ ((d : ℝ) + θ)

lemma elema_H_measurable {θ : ℝ} {μ W : 𝔼 → ℝ} (hμ : Continuous μ) (hW : Continuous W) (x : 𝔼) :
    Measurable (elema_H d θ μ W x) := by
  unfold elema_H
  exact ((measurable_const.sub (hμ.measurable.comp (measurable_const.sub measurable_id))).mul
    (hW.measurable.comp (measurable_const.sub measurable_id))).div (measurable_norm.pow_const _)

lemma elema_H_measurable_prod {θ : ℝ} {μ W : 𝔼 → ℝ} (hμ : Continuous μ) (hW : Continuous W) :
    Measurable (fun p : 𝔼 × 𝔼 => elema_H d θ μ W p.1 p.2) := by
  unfold elema_H
  exact ((((hμ.comp continuous_fst).sub (hμ.comp (continuous_fst.sub continuous_snd))).mul
    (hW.comp (continuous_fst.sub continuous_snd))).measurable).div
    ((measurable_norm.comp measurable_snd).pow_const _)

/-- for `0 < θ < 1` the integrand is dominated by `elema_kk` with `θ + 1` -/
lemma elema_H_le {θ : ℝ} {μ W : 𝔼 → ℝ} {B0 B1 : ℝ} (hB0 : 0 ≤ B0) (hB1 : 0 ≤ B1) (h0 : ∀ y, |μ y| ≤ B0)
    (hl : ∀ a b, |μ a - μ b| ≤ B1 * ‖a - b‖) (x z : 𝔼) :
    ‖elema_H d θ μ W x z‖ₑ ≤
      ENNReal.ofReal (elema_kk d (θ + 1) 1 B1 B0 z) * ‖W (x - z)‖ₑ := by
  have hk0 := elema_kk_nonneg (d := d) (θ + 1) 1 B1 B0 zero_le_one hB1 hB0 z
  have hk : |μ x - μ (x - z)| / ‖z‖ ^ ((d : ℝ) + θ) ≤ elema_kk d (θ + 1) 1 B1 B0 z := by
    by_cases hz : z = 0
    · subst hz
      simpa using hk0
    · have hn : 0 < ‖z‖ := norm_pos_iff.2 hz
      have hD : 0 < ‖z‖ ^ ((d : ℝ) + θ) := Real.rpow_pos_of_pos hn _
      rw [div_le_iff₀ hD]
      unfold elema_kk
      split_ifs with h
      · have h1 : |μ x - μ (x - z)| ≤ B1 * ‖z‖ := by simpa using hl x (x - z)
        calc |μ x - μ (x - z)| ≤ B1 * ‖z‖ := h1
          _ = 1 * B1 * ‖z‖ ^ (2 - ((d : ℝ) + (θ + 1))) * ‖z‖ ^ ((d : ℝ) + θ) := by
              rw [mul_assoc (1 * B1), ← Real.rpow_add hn]
              have : (2 - ((d : ℝ) + (θ + 1)) + ((d : ℝ) + θ)) = 1 := by ring
              rw [this, Real.rpow_one]
              ring
      · have h1 : |μ x - μ (x - z)| ≤ 2 * B0 := by
          have e1 := h0 x
          have e2 := h0 (x - z)
          calc |μ x - μ (x - z)| ≤ |μ x| + |μ (x - z)| := abs_sub _ _
            _ ≤ 2 * B0 := by linarith
        calc |μ x - μ (x - z)| ≤ 2 * B0 := h1
          _ = 1 * (2 * B0) * ‖z‖ ^ (1 - ((d : ℝ) + (θ + 1))) * ‖z‖ ^ ((d : ℝ) + θ) := by
              rw [mul_assoc (1 * (2 * B0)), ← Real.rpow_add hn]
              have : (1 - ((d : ℝ) + (θ + 1)) + ((d : ℝ) + θ)) = 0 := by ring
              rw [this, Real.rpow_zero]
              ring
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hk0]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs]
  unfold elema_H
  rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  calc |μ x - μ (x - z)| * |W (x - z)| / ‖z‖ ^ ((d : ℝ) + θ) =
      (|μ x - μ (x - z)| / ‖z‖ ^ ((d : ℝ) + θ)) * |W (x - z)| := by ring
    _ ≤ elema_kk d (θ + 1) 1 B1 B0 z * |W (x - z)| := mul_le_mul_of_nonneg_right hk (abs_nonneg _)

/-- for `0 < θ < 1`, `[Λ^θ,μ]W(x)` is the absolutely convergent integral of `elema_H` -/
theorem elema_lamComm_eq_integral_lt_one (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ < 1) {μ : 𝔼 → ℝ}
    (hμ : HRS.MemCb 2 μ) (W : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    Integrable (elema_H d θ μ W x) ∧
      HRS.Whole.AppendixA.lamComm d θ μ W x = ∫ z, elema_H d θ μ W x z := by
  have hμ2 : ContDiff ℝ 2 μ := by simpa using hμ.1
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, -, -, h0, h1, h2⟩ := elema_cb2_data hμ
  obtain ⟨BW, LW, MW, hW⟩ := PvC2.of_schwartz W
  have hl : ∀ a b, |μ a - μ b| ≤ B1 * ‖a - b‖ :=
    pvapi_lip_of_fderiv (hμ2.differentiable (by norm_num)) h1
  have hint : Integrable (elema_H d θ μ W x) :=
    elema_integrable_of_kk hd (θ := θ + 1) (by linarith) (by linarith) (B := 1) (La := B1) (Ba := B0)
      zero_le_one hB1 hB0 (elema_H_measurable hμ2.continuous W.continuous x).aestronglyMeasurable
      hW.bdd x (fun z => elema_H_le hB0 hB1 h0 hl x z)
  refine ⟨hint, ?_⟩
  have hH0 : elema_H d θ μ W x 0 = 0 := by simp [elema_H]
  have T1 := lamComm_kernel_tendsto hd hθ0 (by linarith) hμ W x
  have T2 := pvapi_tendsto_trunc hint hH0
  exact tendsto_nhds_unique T1 T2

/-- **(iii-a), `0 < θ < 1`**: the frozen `lp_Lambda_commutator_low` (with `cbNorm 1`) for `θ < 1` -/
theorem lp_Lambda_commutator_low_lt_one_proof (hd : 1 ≤ d) (θ p : ℝ) (hθ0 : 0 < θ) (hθ1 : θ < 1)
    (hp : 2 ≤ p) :
    ∃ C : ℝ, ∀ μ : Euc d → ℝ, HRS.MemCb 2 μ → ∀ W : SchwartzMap (Euc d) ℝ,
      eLpNorm (HRS.Whole.AppendixA.lamComm d θ μ W) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * HRS.cbNorm 1 μ) * eLpNorm W (ENNReal.ofReal p) volume := by
  obtain ⟨C0, hC0, hkk⟩ := elema_kk_lintegral hd (θ := θ + 1) (by linarith) (by linarith) (B := 1) zero_le_one
  refine ⟨C0, fun μ hμ W => ?_⟩
  have hμ2 : ContDiff ℝ 2 μ := by simpa using hμ.1
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, -, hcb, h0, h1, h2⟩ := elema_cb2_data hμ
  have hl : ∀ a b, |μ a - μ b| ≤ B1 * ‖a - b‖ :=
    pvapi_lip_of_fderiv (hμ2.differentiable (by norm_num)) h1
  have hfun : HRS.Whole.AppendixA.lamComm d θ μ W = fun x : 𝔼 => ∫ z, elema_H d θ μ W x z :=
    funext fun x => (elema_lamComm_eq_integral_lt_one hd hθ0 hθ1 hμ W x).2
  rw [hfun]
  have hFm : AEStronglyMeasurable (fun x : 𝔼 => ∫ z, elema_H d θ μ W x z) volume :=
    ((elema_H_measurable_prod (θ := θ) hμ2.continuous W.continuous).stronglyMeasurable.integral_prod_right'
      (ν := volume)).aestronglyMeasurable
  refine (elema_young (elema_kk_measurable (θ + 1) 1 B1 B0) W.continuous.measurable hFm
    (by linarith) (fun x => ?_)).trans (mul_le_mul_left ?_ _)
  · refine (enorm_integral_le_lintegral_enorm _).trans (lintegral_mono fun z => ?_)
    exact elema_H_le hB0 hB1 h0 hl x z
  · refine (hkk B1 B0 hB1 hB0).trans (ENNReal.ofReal_le_ofReal ?_)
    rw [hcb]

/-! ### (iii-b) `θ = 1` with `cbNorm 2`, conditional on the uniform truncation bound of the Riesz transforms

For `θ = 1` the commutator is `[Λ,μ]W = ∑_i ∂_iμ (𝒯^{(i)}_1 W - 𝒯^{(i)}_{1,>1} W) + (absolutely convergent
local and far remainders)`, where `𝒯^{(i)}_{1,>1} = pvTrunc d 1 (u_i) 1` is the truncation at radius `1`.  The remainder
estimates are elementary (Young); the two Riesz-type terms need the `L^p` bound of the truncated Riesz transforms
(Calderón–Zygmund), here the hypothesis `ElemTruncBound` (uniform in the truncation radius: the deliverable of
packet PV-ASM). -/

/-- the local kernel `L |z|^{2-(d+θ)} 1_{|z|≤1}` -/
def elema_kloc (d : ℕ) (θ La : ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  (closedBall (0 : EuclideanSpace ℝ (Fin d)) 1).indicator fun z => La * ‖z‖ ^ (2 - ((d : ℝ) + θ))

/-- the far kernel `B |z|^{-s} 1_{|z|>1}` -/
def elema_kfar (d : ℕ) (s Ba : ℝ) : EuclideanSpace ℝ (Fin d) → ℝ :=
  {z : EuclideanSpace ℝ (Fin d) | 1 < ‖z‖}.indicator fun z => Ba * ‖z‖ ^ (-s)

lemma elema_kloc_measurable (θ La : ℝ) : Measurable (elema_kloc d θ La) :=
  (measurable_const.mul (measurable_norm.pow_const _)).indicator measurableSet_closedBall

lemma elema_kfar_measurable (s Ba : ℝ) : Measurable (elema_kfar d s Ba) :=
  (measurable_const.mul (measurable_norm.pow_const _)).indicator pvapi_tail_meas

lemma elema_kloc_nonneg (θ : ℝ) {La : ℝ} (hLa : 0 ≤ La) (z : 𝔼) : 0 ≤ elema_kloc d θ La z := by
  unfold elema_kloc
  exact Set.indicator_nonneg (fun z _ => mul_nonneg hLa (Real.rpow_nonneg (norm_nonneg _) _)) z

lemma elema_kfar_nonneg (s : ℝ) {Ba : ℝ} (hBa : 0 ≤ Ba) (z : 𝔼) : 0 ≤ elema_kfar d s Ba z := by
  unfold elema_kfar
  exact Set.indicator_nonneg (fun z _ => mul_nonneg hBa (Real.rpow_nonneg (norm_nonneg _) _)) z

/-- `∫⁻ kloc ≤ C La` -/
lemma elema_kloc_lintegral (hd : 1 ≤ d) {θ : ℝ} (hθ2 : θ < 2) (hθ0 : 0 < θ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ La : ℝ, 0 ≤ La → ∫⁻ z : 𝔼, ENNReal.ofReal (elema_kloc d θ La z) ≤
      ENNReal.ofReal (C * La) := by
  have hi : Integrable (fun z : 𝔼 => ‖z‖ ^ (-((d : ℝ) + θ - 2))) (volume.restrict (closedBall 0 1)) := by
    have : IntegrableOn (fun z : 𝔼 => ‖z‖ ^ (-((d : ℝ) + θ - 2))) (ball 0 2) :=
      pvapi_integrableOn_ball_rpow hd (α := (d : ℝ) + θ - 2) (by linarith) 2
    exact this.mono_set (closedBall_subset_ball (by norm_num))
  set I := ∫⁻ z in closedBall (0 : 𝔼) 1, ENNReal.ofReal (‖z‖ ^ (-((d : ℝ) + θ - 2))) with hI
  have hIt : I ≠ ⊤ := hi.lintegral_lt_top.ne
  refine ⟨I.toReal, ENNReal.toReal_nonneg, fun La hLa => ?_⟩
  have h1 : ∫⁻ z : 𝔼, ENNReal.ofReal (elema_kloc d θ La z) =
      ∫⁻ z in closedBall (0 : 𝔼) 1, ENNReal.ofReal (La * ‖z‖ ^ (2 - ((d : ℝ) + θ))) := by
    rw [← lintegral_indicator measurableSet_closedBall]
    refine lintegral_congr fun z => ?_
    unfold elema_kloc
    by_cases hz : z ∈ closedBall (0 : 𝔼) 1
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  rw [h1, pvapi_ofReal_B_mul _ hLa]
  have e : ∀ z : 𝔼, ‖z‖ ^ (2 - ((d : ℝ) + θ)) = ‖z‖ ^ (-((d : ℝ) + θ - 2)) := fun z => by
    congr 1; ring
  simp_rw [e]
  rw [← hI]
  conv_lhs => rw [← ENNReal.ofReal_toReal hIt]
  rw [← ENNReal.ofReal_mul hLa, mul_comm]

/-- `∫⁻ kfar ≤ C Ba` -/
lemma elema_kfar_lintegral (hd : 1 ≤ d) {s : ℝ} (hs : (d : ℝ) < s) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ Ba : ℝ, 0 ≤ Ba → ∫⁻ z : 𝔼, ENNReal.ofReal (elema_kfar d s Ba z) ≤
      ENNReal.ofReal (C * Ba) := by
  have hi : Integrable (fun z : 𝔼 => ‖z‖ ^ (-s)) (volume.restrict {z : 𝔼 | 1 < ‖z‖}) :=
    pvapi_integrableOn_tail_rpow hd hs
  set I := ∫⁻ z in {z : 𝔼 | 1 < ‖z‖}, ENNReal.ofReal (‖z‖ ^ (-s)) with hI
  have hIt : I ≠ ⊤ := hi.lintegral_lt_top.ne
  refine ⟨I.toReal, ENNReal.toReal_nonneg, fun Ba hBa => ?_⟩
  have h1 : ∫⁻ z : 𝔼, ENNReal.ofReal (elema_kfar d s Ba z) =
      ∫⁻ z in {z : 𝔼 | 1 < ‖z‖}, ENNReal.ofReal (Ba * ‖z‖ ^ (-s)) := by
    rw [← lintegral_indicator pvapi_tail_meas]
    refine lintegral_congr fun z => ?_
    unfold elema_kfar
    by_cases hz : z ∈ {z : 𝔼 | 1 < ‖z‖}
    · simp [Set.indicator_of_mem hz]
    · simp [Set.indicator_of_notMem hz]
  rw [h1, pvapi_ofReal_B_mul _ hBa, ← hI]
  conv_lhs => rw [← ENNReal.ofReal_toReal hIt]
  rw [← ENNReal.ofReal_mul hBa, mul_comm]

lemma elema_G_abs {θ : ℝ} (μ W : 𝔼 → ℝ) (x z : 𝔼) :
    |elema_G d θ μ W x z| = |elema_R μ x z| / ‖z‖ ^ ((d : ℝ) + θ) * |W (x - z)| := by
  unfold elema_G
  rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _)]
  ring

/-- for `0 < θ < 2` the remainder integrand is integrable (the far part only through `W ∈ L¹`) -/
theorem elema_G_integrable (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {μ : 𝔼 → ℝ}
    (hμ : HRS.MemCb 2 μ) (W : 𝓢(𝔼, ℝ)) (x : 𝔼) : Integrable (elema_G d θ μ W x) := by
  have hμ2 : ContDiff ℝ 2 μ := by simpa using hμ.1
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, -, -, h0, h1, h2⟩ := elema_cb2_data hμ
  obtain ⟨BW, LW, MW, hW⟩ := PvC2.of_schwartz W
  have hBW : 0 ≤ BW := hW.Bf_nonneg
  have hGm : AEStronglyMeasurable (elema_G d θ μ W x) volume :=
    (elema_G_measurable hμ2.continuous W.continuous x).aestronglyMeasurable
  have hk := fun z => elema_remainder_le (d := d) (θ := θ) hμ2 hB0 hB1 hB2 h0 h1 h2 x z
  have hball : IntegrableOn (elema_G d θ μ W x) (closedBall 0 1) := by
    have hi : IntegrableOn (fun z : 𝔼 => (B2 / 2 * BW) * ‖z‖ ^ (-((d : ℝ) + θ - 2))) (closedBall 0 1) := by
      have : IntegrableOn (fun z : 𝔼 => ‖z‖ ^ (-((d : ℝ) + θ - 2))) (ball 0 2) :=
        pvapi_integrableOn_ball_rpow hd (α := (d : ℝ) + θ - 2) (by linarith) 2
      exact (this.mono_set (closedBall_subset_ball (by norm_num))).const_mul _
    refine Integrable.mono' hi hGm.restrict ((ae_restrict_iff' measurableSet_closedBall).2
      (ae_of_all _ fun z hz => ?_))
    have hz' : ‖z‖ ≤ 1 := by simpa using hz
    rw [Real.norm_eq_abs, elema_G_abs]
    have hkz := hk z
    unfold elema_kk at hkz
    rw [if_pos hz'] at hkz
    have e : ‖z‖ ^ (-((d : ℝ) + θ - 2)) = ‖z‖ ^ (2 - ((d : ℝ) + θ)) := by congr 1; ring
    rw [e]
    calc |elema_R μ x z| / ‖z‖ ^ ((d : ℝ) + θ) * |W (x - z)| ≤
        (1 * (B2 / 2) * ‖z‖ ^ (2 - ((d : ℝ) + θ))) * BW :=
          mul_le_mul hkz (hW.bdd _) (abs_nonneg _) (by
            have := Real.rpow_nonneg (norm_nonneg z) (2 - ((d : ℝ) + θ))
            positivity)
      _ = _ := by ring
  have htail : IntegrableOn (elema_G d θ μ W x) {z : 𝔼 | 1 < ‖z‖} := by
    have hi : IntegrableOn (fun z : 𝔼 => (2 * (B0 + B1 / 2)) * |W (x - z)|) {z : 𝔼 | 1 < ‖z‖} :=
      ((W.integrable.comp_sub_left x).norm.const_mul _).integrableOn
    refine Integrable.mono' hi hGm.restrict ((ae_restrict_iff' pvapi_tail_meas).2
      (ae_of_all _ fun z hz => ?_))
    have hz' : 1 < ‖z‖ := hz
    rw [Real.norm_eq_abs, elema_G_abs]
    have hkz := hk z
    unfold elema_kk at hkz
    rw [if_neg (not_le.2 hz')] at hkz
    have hpow : ‖z‖ ^ (1 - ((d : ℝ) + θ)) ≤ 1 :=
      Real.rpow_le_one_of_one_le_of_nonpos hz'.le (by
        have : (1 : ℝ) ≤ d := by exact_mod_cast hd
        linarith)
    have hc : 1 * (2 * (B0 + B1 / 2)) * ‖z‖ ^ (1 - ((d : ℝ) + θ)) ≤ 2 * (B0 + B1 / 2) := by
      calc 1 * (2 * (B0 + B1 / 2)) * ‖z‖ ^ (1 - ((d : ℝ) + θ)) ≤ 1 * (2 * (B0 + B1 / 2)) * 1 :=
            mul_le_mul_of_nonneg_left hpow (by linarith)
        _ = _ := by ring
    exact mul_le_mul_of_nonneg_right (hkz.trans hc) (abs_nonneg _)
  rw [← integrableOn_univ, ← pvapi_ball_union_tail]
  exact hball.union htail

/-- pointwise: `H = G + ∑_i ∂_iμ(x) K_i(z) W(x-z)` -/
lemma elema_H_split (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (μ W : 𝔼 → ℝ) (x z : 𝔼) :
    elema_H d θ μ W x z = elema_G d θ μ W x z +
      ∑ i : Fin d, gradient μ x i * (pvK d θ (fun u : 𝔼 => u i) z * W (x - z)) := by
  have e1 : ∑ i : Fin d, gradient μ x i * (pvK d θ (fun u : 𝔼 => u i) z * W (x - z)) =
      fderiv ℝ μ x z * W (x - z) / ‖z‖ ^ ((d : ℝ) + θ) := by
    rw [← elema_grad_sum, Finset.sum_mul, Finset.sum_div]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [elema_pvK_coord hd hθ0]
    ring
  rw [e1]
  unfold elema_H elema_G elema_R
  ring

/-- the decomposition of the commutator into the local remainder, the far commutator integral and the
truncated odd integrals (`0 < θ < 2`):
`[Λ^θ,μ]W = ∫_{|z|≤1} G + ∫_{|z|>1} H + ∑_i ∂_iμ (𝒯^{(i)}_θ W - 𝒯^{(i)}_{θ,>1} W)` -/
theorem elema_lamComm_decomp (hd : 1 ≤ d) {θ : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {μ : 𝔼 → ℝ}
    (hμ : HRS.MemCb 2 μ) (W : 𝓢(𝔼, ℝ)) (x : 𝔼) :
    HRS.Whole.AppendixA.lamComm d θ μ W x =
      (∫ z in closedBall (0 : 𝔼) 1, elema_G d θ μ W x z) +
        (∫ z in {z : 𝔼 | 1 < ‖z‖}, elema_H d θ μ W x z) +
        ∑ i : Fin d, gradient μ x i * (HRS.Whole.AppendixA.pvOdd d θ (fun u : 𝔼 => u i) W x -
          pvTrunc d θ (fun u : 𝔼 => u i) W 1 x) := by
  have hGint := elema_G_integrable hd hθ0 hθ2 hμ W x
  have hrepr := elema_expansion_repr_of hd hθ0 hθ2 hμ W x hGint
  have hsplit := setIntegral_union (f := elema_G d θ μ W x) pvapi_ball_tail_disjoint pvapi_tail_meas
    hGint.integrableOn hGint.integrableOn
  rw [pvapi_ball_union_tail, setIntegral_univ] at hsplit
  have hi : ∀ i : Fin d, IntegrableOn (fun z => gradient μ x i * (pvK d θ (fun u : 𝔼 => u i) z * W (x - z)))
      {z : 𝔼 | 1 < ‖z‖} := fun i =>
    (pvK_far_integrable_of_integrable hd hθ0 (isPvKernel_coord i) W.integrable x).const_mul _
  have hHtail : ∫ z in {z : 𝔼 | 1 < ‖z‖}, elema_H d θ μ W x z =
      (∫ z in {z : 𝔼 | 1 < ‖z‖}, elema_G d θ μ W x z) +
        ∑ i : Fin d, gradient μ x i * pvTrunc d θ (fun u : 𝔼 => u i) W 1 x := by
    rw [setIntegral_congr_fun pvapi_tail_meas (fun z _ => elema_H_split hd hθ0 μ W x z),
      integral_add hGint.integrableOn (integrable_finsetSum _ (fun i _ => hi i)),
      integral_finsetSum _ (fun i _ => hi i)]
    congr 1
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul]
    rfl
  simp_rw [mul_sub, Finset.sum_sub_distrib]
  rw [hHtail]
  linarith

/-- the uniform truncation bound for the Riesz-type transforms `𝒯^{(i)}_1` (hypothesis, the deliverable of PV-ASM) -/
def ElemTruncBound (d : ℕ) (p CR : ℝ) : Prop :=
  ∀ (i : Fin d) (W : 𝓢(EuclideanSpace ℝ (Fin d), ℝ)) (ε : ℝ), 0 < ε →
    eLpNorm (fun x => pvTrunc d 1 (fun u : EuclideanSpace ℝ (Fin d) => u i) W ε x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal CR * eLpNorm W (ENNReal.ofReal p) volume

/-- Fatou: a uniform `L^p` bound for the truncations passes to the principal value -/
lemma elema_pvOdd_Lp_of_trunc (hd : 1 ≤ d) {θ p : ℝ} (hθ0 : 0 < θ) (hθ2 : θ < 2) {Ω : 𝔼 → ℝ} {B : ℝ}
    (hK : IsPvKernel Ω B) (W : 𝓢(𝔼, ℝ)) {C : ℝ≥0∞}
    (hT : ∀ ε : ℝ, 0 < ε → eLpNorm (fun x => pvTrunc d θ Ω W ε x) (ENNReal.ofReal p) volume ≤ C) :
    eLpNorm (HRS.Whole.AppendixA.pvOdd d θ Ω W) (ENNReal.ofReal p) volume ≤ C := by
  obtain ⟨B1, L1, M1, h1⟩ := PvC2.of_schwartz W
  have hseq : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] (0 : ℝ)) :=
    tendsto_nhdsWithin_iff.2 ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [Set.mem_Ioi]; positivity⟩
  refine Lp.eLpNorm_le_of_ae_tendsto (u := atTop) (f := fun (n : ℕ) x => pvTrunc d θ Ω W (1 / ((n : ℝ) + 1)) x)
    (Eventually.of_forall fun n => hT (1 / ((n : ℝ) + 1)) (by positivity))
    (fun n => (pvTrunc_measurable hK W.continuous _).aestronglyMeasurable)
    (pvOdd_aesm hd hθ0 hθ2 hK W) (ae_of_all _ fun x => ?_)
  have hfar := pvK_far_integrable_of_integrable hd hθ0 hK W.integrable x
  have hlim := pvTrunc_tendsto hd hθ0 hθ2 hK h1.lipschitzWith x hfar
  have hv := pvOdd_eq_of_lip hd hθ0 hθ2 hK h1.lipschitzWith x hfar
  rw [hv]
  exact hlim.comp hseq

lemma elema_floc_aesm {θ : ℝ} {μ W : 𝔼 → ℝ} (hμ : Continuous μ) (hμ1 : Continuous (fderiv ℝ μ))
    (hW : Continuous W) :
    AEStronglyMeasurable (fun x : 𝔼 => ∫ z in closedBall (0 : 𝔼) 1, elema_G d θ μ W x z) volume := by
  classical
  have hF : Measurable (fun p : 𝔼 × 𝔼 =>
      if p.2 ∈ closedBall (0 : 𝔼) 1 then elema_G d θ μ W p.1 p.2 else 0) :=
    Measurable.ite (measurable_snd measurableSet_closedBall) (elema_G_measurable_prod hμ hμ1 hW)
      measurable_const
  have h : AEStronglyMeasurable (fun x : 𝔼 => ∫ z, (if z ∈ closedBall (0 : 𝔼) 1 then
      elema_G d θ μ W x z else 0)) volume :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
  refine h.congr (Eventually.of_forall fun x => ?_)
  show (∫ z, if z ∈ closedBall (0 : 𝔼) 1 then elema_G d θ μ W x z else 0) =
    ∫ z in closedBall (0 : 𝔼) 1, elema_G d θ μ W x z
  rw [← integral_indicator measurableSet_closedBall]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp [Set.indicator_apply]

lemma elema_ffar_aesm {θ : ℝ} {μ W : 𝔼 → ℝ} (hμ : Continuous μ) (hW : Continuous W) :
    AEStronglyMeasurable (fun x : 𝔼 => ∫ z in {z : 𝔼 | 1 < ‖z‖}, elema_H d θ μ W x z) volume := by
  classical
  have hF : Measurable (fun p : 𝔼 × 𝔼 =>
      if 1 < ‖p.2‖ then elema_H d θ μ W p.1 p.2 else 0) :=
    Measurable.ite (measurableSet_lt measurable_const (measurable_norm.comp measurable_snd))
      (elema_H_measurable_prod hμ hW) measurable_const
  have h : AEStronglyMeasurable (fun x : 𝔼 => ∫ z, (if 1 < ‖z‖ then elema_H d θ μ W x z else 0)) volume :=
    (hF.stronglyMeasurable.integral_prod_right' (ν := volume)).aestronglyMeasurable
  refine h.congr (Eventually.of_forall fun x => ?_)
  show (∫ z, if 1 < ‖z‖ then elema_H d θ μ W x z else 0) =
    ∫ z in {z : 𝔼 | 1 < ‖z‖}, elema_H d θ μ W x z
  rw [← integral_indicator pvapi_tail_meas]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp [Set.indicator_apply]

/-- the far commutator integrand is dominated by `kfar` -/
lemma elema_H_tail_le {θ : ℝ} {μ W : 𝔼 → ℝ} {B0 : ℝ} (hB0 : 0 ≤ B0) (h0 : ∀ y, |μ y| ≤ B0) (x z : 𝔼)
    (hz : 1 < ‖z‖) :
    ‖elema_H d θ μ W x z‖ₑ ≤ ENNReal.ofReal (elema_kfar d ((d : ℝ) + θ) (2 * B0) z) * ‖W (x - z)‖ₑ := by
  have hn : 0 < ‖z‖ := by linarith
  have hkz : elema_kfar d ((d : ℝ) + θ) (2 * B0) z = 2 * B0 * ‖z‖ ^ (-((d : ℝ) + θ)) := by
    unfold elema_kfar
    rw [Set.indicator_of_mem (show z ∈ {z : 𝔼 | 1 < ‖z‖} from hz)]
  have hk0 : 0 ≤ elema_kfar d ((d : ℝ) + θ) (2 * B0) z := elema_kfar_nonneg _ (by linarith) z
  rw [← ofReal_norm, ← ofReal_norm, ← ENNReal.ofReal_mul hk0]
  refine ENNReal.ofReal_le_ofReal ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs, hkz]
  unfold elema_H
  rw [abs_div, abs_mul, abs_of_nonneg (Real.rpow_nonneg (norm_nonneg z) _), Real.rpow_neg hn.le]
  have h1 : |μ x - μ (x - z)| ≤ 2 * B0 := by
    have e1 := h0 x
    have e2 := h0 (x - z)
    calc |μ x - μ (x - z)| ≤ |μ x| + |μ (x - z)| := abs_sub _ _
      _ ≤ 2 * B0 := by linarith
  have hD : 0 < ‖z‖ ^ ((d : ℝ) + θ) := Real.rpow_pos_of_pos hn _
  calc |μ x - μ (x - z)| * |W (x - z)| / ‖z‖ ^ ((d : ℝ) + θ) =
      (|μ x - μ (x - z)| * |W (x - z)|) * (‖z‖ ^ ((d : ℝ) + θ))⁻¹ := by rw [div_eq_mul_inv]
    _ ≤ (2 * B0 * |W (x - z)|) * (‖z‖ ^ ((d : ℝ) + θ))⁻¹ := by
        gcongr
    _ = 2 * B0 * (‖z‖ ^ ((d : ℝ) + θ))⁻¹ * |W (x - z)| := by ring

/-- the local remainder integrand is dominated by `kloc` -/
lemma elema_G_ball_le {θ : ℝ} {μ W : 𝔼 → ℝ} (hμ : ContDiff ℝ 2 μ) {B0 B1 B2 : ℝ} (hB0 : 0 ≤ B0)
    (hB1 : 0 ≤ B1) (hB2 : 0 ≤ B2) (h0 : ∀ y, |μ y| ≤ B0) (h1 : ∀ y, ‖fderiv ℝ μ y‖ ≤ B1)
    (h2 : ∀ y, ‖iteratedFDeriv ℝ 2 μ y‖ ≤ B2) (x z : 𝔼) (hz : ‖z‖ ≤ 1) :
    ‖elema_G d θ μ W x z‖ₑ ≤ ENNReal.ofReal (elema_kloc d θ (B2 / 2) z) * ‖W (x - z)‖ₑ := by
  have h := elema_G_le (d := d) (θ := θ) (W := W) hμ hB0 hB1 hB2 h0 h1 h2 x z
  unfold elema_kk at h
  rw [if_pos hz] at h
  have hkl : elema_kloc d θ (B2 / 2) z = 1 * (B2 / 2) * ‖z‖ ^ (2 - ((d : ℝ) + θ)) := by
    unfold elema_kloc
    rw [Set.indicator_of_mem (show z ∈ closedBall (0 : 𝔼) 1 by simpa using hz)]
    ring
  rw [hkl]
  exact h

lemma elema_grad_coord_le {μ : 𝔼 → ℝ} {B1 : ℝ} (h1 : ∀ y, ‖fderiv ℝ μ y‖ ≤ B1) (x : 𝔼) (i : Fin d) :
    |gradient μ x i| ≤ B1 := by
  have h := PiLp.norm_apply_le (gradient μ x) i
  have e : ‖gradient μ x‖ = ‖fderiv ℝ μ x‖ := by
    unfold gradient
    exact (InnerProductSpace.toDual ℝ 𝔼).symm.norm_map _
  rw [Real.norm_eq_abs] at h
  exact h.trans (e ▸ h1 x)

/-- one friction term: `‖∂_iμ (𝒯^{(i)}_1 W - 𝒯^{(i)}_{1,>1} W)‖_p ≤ B₁ · 2 C_R ‖W‖_p` -/
lemma elema_fric_term (hd : 1 ≤ d) {p CR : ℝ} (hp : 2 ≤ p) (hT : ElemTruncBound d p CR) {μ : 𝔼 → ℝ}
    (hμ2 : ContDiff ℝ 2 μ) {B1 : ℝ} (hB1 : 0 ≤ B1) (h1 : ∀ y, ‖fderiv ℝ μ y‖ ≤ B1) (W : 𝓢(𝔼, ℝ)) (i : Fin d) :
    eLpNorm (fun x => gradient μ x i * (HRS.Whole.AppendixA.pvOdd d 1 (fun u : 𝔼 => u i) W x -
        pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal B1 * (ENNReal.ofReal CR * eLpNorm W (ENNReal.ofReal p) volume +
        ENNReal.ofReal CR * eLpNorm W (ENNReal.ofReal p) volume) := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 (by linarith)
  have hK := isPvKernel_coord (d := d) i
  have hpv : eLpNorm (HRS.Whole.AppendixA.pvOdd d 1 (fun u : 𝔼 => u i) W) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal CR * eLpNorm W (ENNReal.ofReal p) volume :=
    elema_pvOdd_Lp_of_trunc hd one_pos one_lt_two hK W (fun ε hε => hT i W ε hε)
  have htr : eLpNorm (fun x => pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal CR * eLpNorm W (ENNReal.ofReal p) volume := hT i W 1 one_pos
  have hgc : Continuous (fun x : 𝔼 => gradient μ x i) := by
    have h1c : Continuous (fderiv ℝ μ) := hμ2.continuous_fderiv (by norm_num)
    have : Continuous (fun x : 𝔼 => gradient μ x) := by
      unfold gradient
      exact (InnerProductSpace.toDual ℝ 𝔼).symm.continuous.comp h1c
    exact (continuous_apply i).comp (PiLp.continuous_ofLp 2 _) |>.comp this
  have hmeas : AEStronglyMeasurable (fun x => gradient μ x i * (HRS.Whole.AppendixA.pvOdd d 1
      (fun u : 𝔼 => u i) W x - pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x)) volume :=
    hgc.aestronglyMeasurable.mul ((pvOdd_aesm hd one_pos one_lt_two hK W).sub
      (pvTrunc_measurable hK W.continuous 1).aestronglyMeasurable)
  have hmono : eLpNorm (fun x => gradient μ x i * (HRS.Whole.AppendixA.pvOdd d 1 (fun u : 𝔼 => u i) W x -
        pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x)) (ENNReal.ofReal p) volume ≤
      eLpNorm (fun x => B1 • (HRS.Whole.AppendixA.pvOdd d 1 (fun u : 𝔼 => u i) W x -
        pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x)) (ENNReal.ofReal p) volume := by
    refine eLpNorm_mono_enorm hmeas (fun x => ?_)
    rw [← ofReal_norm, ← ofReal_norm, Real.norm_eq_abs, Real.norm_eq_abs, abs_mul, smul_eq_mul, abs_mul,
      abs_of_nonneg hB1]
    exact ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_right (elema_grad_coord_le h1 x i) (abs_nonneg _))
  refine hmono.trans ?_
  have hc := eLpNorm_const_smul B1 (fun x => HRS.Whole.AppendixA.pvOdd d 1 (fun u : 𝔼 => u i) W x -
        pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x) (ENNReal.ofReal p) volume
  refine hc.le.trans ?_
  rw [Real.enorm_eq_ofReal hB1]
  refine mul_le_mul_right ?_ _
  exact (eLpNorm_sub_le hp1).trans (add_le_add hpv htr)

/-- **(iii-b), `θ = 1`, with `cbNorm 2`**, conditional on the uniform truncation bound `ElemTruncBound` of the
Riesz-type transforms (Calderón–Zygmund).  All other ingredients are elementary. -/
theorem elema_lamComm_theta_one (hd : 1 ≤ d) (p CR : ℝ) (hp : 2 ≤ p) (hT : ElemTruncBound d p CR) :
    ∃ C : ℝ, ∀ μ : 𝔼 → ℝ, HRS.MemCb 2 μ → ∀ W : 𝓢(𝔼, ℝ),
      eLpNorm (HRS.Whole.AppendixA.lamComm d 1 μ W) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * HRS.cbNorm 2 μ) * eLpNorm W (ENNReal.ofReal p) volume := by
  have hp1 : (1 : ℝ≥0∞) ≤ ENNReal.ofReal p := ENNReal.one_le_ofReal.2 (by linarith)
  have hp1r : (1 : ℝ) ≤ p := by linarith
  obtain ⟨Cl, hCl0, hCl⟩ := elema_kloc_lintegral hd (θ := 1) one_lt_two one_pos
  obtain ⟨Cf, hCf0, hCf⟩ := elema_kfar_lintegral hd (s := (d : ℝ) + 1) (by linarith)
  set CR' : ℝ := max CR 0 with hCR'
  have hCR'0 : 0 ≤ CR' := le_max_right _ _
  refine ⟨Cl / 2 + 2 * Cf + 2 * d * CR', fun μ hμ W => ?_⟩
  have hμ2 : ContDiff ℝ 2 μ := by simpa using hμ.1
  obtain ⟨B0, B1, B2, hB0, hB1, hB2, hcb, -, h0, h1, h2⟩ := elema_cb2_data hμ
  have hμc : Continuous μ := hμ2.continuous
  have hμ1c : Continuous (fderiv ℝ μ) := hμ2.continuous_fderiv (by norm_num)
  set N := eLpNorm W (ENNReal.ofReal p) volume with hN
  -- the decomposition
  have hfun : HRS.Whole.AppendixA.lamComm d 1 μ W = fun x : 𝔼 =>
      ((∫ z in closedBall (0 : 𝔼) 1, elema_G d 1 μ W x z) +
        (∫ z in {z : 𝔼 | 1 < ‖z‖}, elema_H d 1 μ W x z)) +
        ∑ i : Fin d, gradient μ x i * (HRS.Whole.AppendixA.pvOdd d 1 (fun u : 𝔼 => u i) W x -
          pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x) :=
    funext fun x => elema_lamComm_decomp hd one_pos one_lt_two hμ W x
  rw [hfun]
  -- local part
  have P1 : eLpNorm (fun x : 𝔼 => ∫ z in closedBall (0 : 𝔼) 1, elema_G d 1 μ W x z) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (Cl * (B2 / 2)) * N := by
    refine (elema_young (elema_kloc_measurable 1 (B2 / 2)) W.continuous.measurable
      (elema_floc_aesm hμc hμ1c W.continuous) hp1r (fun x => ?_)).trans
      (mul_le_mul_left (hCl (B2 / 2) (by linarith)) _)
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine (setLIntegral_mono' measurableSet_closedBall (fun z hz => ?_)).trans
      (setLIntegral_le_lintegral _ _)
    exact elema_G_ball_le hμ2 hB0 hB1 hB2 h0 h1 h2 x z (by simpa using hz)
  -- far part
  have P2 : eLpNorm (fun x : 𝔼 => ∫ z in {z : 𝔼 | 1 < ‖z‖}, elema_H d 1 μ W x z) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (Cf * (2 * B0)) * N := by
    refine (elema_young (elema_kfar_measurable ((d : ℝ) + 1) (2 * B0)) W.continuous.measurable
      (elema_ffar_aesm hμc W.continuous) hp1r (fun x => ?_)).trans
      (mul_le_mul_left (hCf (2 * B0) (by linarith)) _)
    refine (enorm_integral_le_lintegral_enorm _).trans ?_
    refine (setLIntegral_mono' pvapi_tail_meas (fun z hz => ?_)).trans (setLIntegral_le_lintegral _ _)
    exact elema_H_tail_le hB0 h0 x z hz
  -- friction part
  have P3 : eLpNorm (fun x : 𝔼 => ∑ i : Fin d, gradient μ x i * (HRS.Whole.AppendixA.pvOdd d 1
        (fun u : 𝔼 => u i) W x - pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x)) (ENNReal.ofReal p) volume ≤
      ENNReal.ofReal (d * (B1 * (2 * CR'))) * N := by
    have hsum := eLpNorm_sum_le (μ := volume) (p := ENNReal.ofReal p) (s := (Finset.univ : Finset (Fin d)))
      (f := fun (i : Fin d) (x : 𝔼) => gradient μ x i * (HRS.Whole.AppendixA.pvOdd d 1
        (fun u : 𝔼 => u i) W x - pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x)) hp1
    have e : (fun x : 𝔼 => ∑ i : Fin d, gradient μ x i * (HRS.Whole.AppendixA.pvOdd d 1
        (fun u : 𝔼 => u i) W x - pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x)) =
        ∑ i : Fin d, (fun x : 𝔼 => gradient μ x i * (HRS.Whole.AppendixA.pvOdd d 1
        (fun u : 𝔼 => u i) W x - pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x)) := by
      funext x
      simp
    rw [e]
    refine hsum.trans ?_
    have hterm : ∀ i : Fin d, eLpNorm (fun x => gradient μ x i * (HRS.Whole.AppendixA.pvOdd d 1
        (fun u : 𝔼 => u i) W x - pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x)) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (B1 * (2 * CR')) * N := by
      intro i
      refine (elema_fric_term hd hp hT hμ2 hB1 h1 W i).trans ?_
      have hc : ENNReal.ofReal CR ≤ ENNReal.ofReal CR' := ENNReal.ofReal_le_ofReal (le_max_left _ _)
      rw [ENNReal.ofReal_mul hB1, ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 2),
        ENNReal.ofReal_ofNat, mul_assoc]
      refine mul_le_mul_right ?_ _
      calc ENNReal.ofReal CR * N + ENNReal.ofReal CR * N ≤ ENNReal.ofReal CR' * N + ENNReal.ofReal CR' * N :=
            add_le_add (mul_le_mul_left hc _) (mul_le_mul_left hc _)
        _ = 2 * ENNReal.ofReal CR' * N := by ring
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul, ENNReal.ofReal_mul (Nat.cast_nonneg d),
      ENNReal.ofReal_natCast, mul_assoc]
  -- assembly
  have hfin : eLpNorm (fun x : 𝔼 => ((∫ z in closedBall (0 : 𝔼) 1, elema_G d 1 μ W x z) +
        (∫ z in {z : 𝔼 | 1 < ‖z‖}, elema_H d 1 μ W x z)) +
        ∑ i : Fin d, gradient μ x i * (HRS.Whole.AppendixA.pvOdd d 1 (fun u : 𝔼 => u i) W x -
          pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x)) (ENNReal.ofReal p) volume ≤
      eLpNorm (fun x : 𝔼 => ∫ z in closedBall (0 : 𝔼) 1, elema_G d 1 μ W x z) (ENNReal.ofReal p) volume +
        eLpNorm (fun x : 𝔼 => ∫ z in {z : 𝔼 | 1 < ‖z‖}, elema_H d 1 μ W x z) (ENNReal.ofReal p) volume +
        eLpNorm (fun x : 𝔼 => ∑ i : Fin d, gradient μ x i * (HRS.Whole.AppendixA.pvOdd d 1
          (fun u : 𝔼 => u i) W x - pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x)) (ENNReal.ofReal p) volume := by
    refine (eLpNorm_add_le (f := fun x : 𝔼 => (∫ z in closedBall (0 : 𝔼) 1, elema_G d 1 μ W x z) +
        (∫ z in {z : 𝔼 | 1 < ‖z‖}, elema_H d 1 μ W x z)) (g := fun x : 𝔼 => ∑ i : Fin d, gradient μ x i *
        (HRS.Whole.AppendixA.pvOdd d 1 (fun u : 𝔼 => u i) W x - pvTrunc d 1 (fun u : 𝔼 => u i) W 1 x))
        hp1).trans ?_
    gcongr
    exact eLpNorm_add_le hp1
  refine hfin.trans ?_
  have hsum3 : ENNReal.ofReal (Cl * (B2 / 2)) * N + ENNReal.ofReal (Cf * (2 * B0)) * N +
      ENNReal.ofReal (d * (B1 * (2 * CR'))) * N =
      ENNReal.ofReal (Cl * (B2 / 2) + Cf * (2 * B0) + d * (B1 * (2 * CR'))) * N := by
    rw [← add_mul, ← add_mul, ← ENNReal.ofReal_add (mul_nonneg hCl0 (by linarith))
      (mul_nonneg hCf0 (by linarith)),
      ← ENNReal.ofReal_add (add_nonneg (mul_nonneg hCl0 (by linarith)) (mul_nonneg hCf0 (by linarith)))
        (mul_nonneg (Nat.cast_nonneg d) (mul_nonneg hB1 (by linarith)))]
  calc _ ≤ ENNReal.ofReal (Cl * (B2 / 2)) * N + ENNReal.ofReal (Cf * (2 * B0)) * N +
      ENNReal.ofReal (d * (B1 * (2 * CR'))) * N := add_le_add (add_le_add P1 P2) P3
    _ = _ := hsum3
    _ ≤ ENNReal.ofReal ((Cl / 2 + 2 * Cf + 2 * d * CR') * HRS.cbNorm 2 μ) * N := by
        refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
        rw [hcb]
        have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
        nlinarith [mul_nonneg hCl0 hB2, mul_nonneg hCf0 hB0, mul_nonneg hd0 (mul_nonneg hCR'0 hB1),
          mul_nonneg hCl0 hB0, mul_nonneg hCl0 hB1, mul_nonneg hCf0 hB1, mul_nonneg hCf0 hB2,
          mul_nonneg hd0 (mul_nonneg hCR'0 hB0), mul_nonneg hd0 (mul_nonneg hCR'0 hB2)]

/-- **(iii-a) with `cbNorm 2`, all `0 < θ ≤ 1`** (`lp_Lambda_commutator_low_cb2`): unconditional for `θ < 1`; for
`θ = 1` conditional on the uniform truncation bound `ElemTruncBound` of the Riesz-type transforms (the Calderón–Zygmund
input of PV-ASM), which is not elementary. -/
theorem lp_Lambda_commutator_low_cb2 (hd : 1 ≤ d) (θ p : ℝ) (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hp : 2 ≤ p)
    (hT : θ = 1 → ∃ CR : ℝ, ElemTruncBound d p CR) :
    ∃ C : ℝ, ∀ μ : Euc d → ℝ, HRS.MemCb 2 μ → ∀ W : SchwartzMap (Euc d) ℝ,
      eLpNorm (HRS.Whole.AppendixA.lamComm d θ μ W) (ENNReal.ofReal p) volume ≤
        ENNReal.ofReal (C * HRS.cbNorm 2 μ) * eLpNorm W (ENNReal.ofReal p) volume := by
  rcases hθ1.lt_or_eq with hlt | heq
  · obtain ⟨C, hC⟩ := lp_Lambda_commutator_low_lt_one_proof hd θ p hθ0 hlt hp
    refine ⟨max C 0, fun μ hμ W => (hC μ hμ W).trans ?_⟩
    obtain ⟨B0, B1, B2, hB0, hB1, hB2, hcb2, hcb1, -, -, -⟩ := elema_cb2_data hμ
    refine mul_le_mul_left (ENNReal.ofReal_le_ofReal ?_) _
    rw [hcb1, hcb2]
    nlinarith [le_max_left C 0, le_max_right C 0, mul_nonneg (le_max_right C 0) hB2,
      mul_nonneg (le_max_right C 0) (add_nonneg hB0 hB1)]
  · subst heq
    obtain ⟨CR, hCR⟩ := hT rfl
    exact elema_lamComm_theta_one hd p CR hp hCR

end HRS.CZ.ElemA
