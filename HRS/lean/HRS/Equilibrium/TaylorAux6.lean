/-
# HRS.Equilibrium.TaylorAux6 — the truncated-remainder term `∫ φ v_{Y,H}² dμ` in `L^{2q}(μ^{⊗n})`
and the pointwise reduction of the Taylor remainder (Lemma 4.7, packet TAYLOR)

* `taylor_B1_bound`: `‖∫ φ(y) e^K v_{Y,H}(y)² dμ(y)‖_{L^{2q}(μ^{⊗n})} ≤ C Θ(N,H)` with
  `Θ = log H/N + H²/N² + 1/H² + 1/N²` (Jensen/Hölder in `y`, then `taylor_field_moment`).
* `taylor_pointwise`: for every `Y`,
  `∫ φ H(v_Y) dμ ≤ ∫ φ e^K v_{Y,H}² dμ + λ ∑_{j≠i} T_{H,x}(y_j)` (source lines 4318-4319, 4346).
-/
import HRS.Equilibrium.PoleCavity
import HRS.Equilibrium.TaylorAux5

open MeasureTheory
open scoped ENNReal

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS.TaylorAux

variable {d : ℕ} {s : ℝ}

section Field

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β) (ρ : Torus d → ℝ)
  (hρ : SmoothPosDensity ρ) (c : ℝ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit in
theorem taylor_measurable_h : Measurable (convMeasure (gPlus d s c) (withDensityReal ρ)) := by
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  have hμ : SFinite (withDensityReal ρ) := by unfold withDensityReal; infer_instance
  exact PoleCavityAux.measurable_convMeasure (PoleCavityAux.measurable_gPlus hd hs0 hsd c (s := s)) _

include hd hcrit in
theorem taylor_measurable_fieldH (N : ℕ) (n : ℕ) (i : Fin n) (H : ℝ) :
    Measurable (fun p : Config d n × Torus d => taylorFieldH d s c β ρ N i H p.1 p.2) := by
  unfold taylorFieldH
  refine Measurable.sub ?_ ?_
  · refine Measurable.const_mul (Finset.measurable_sum _ fun j _ => ?_) _
    exact (taylor_measurable_gTrunc hd hcrit c H).comp
      (measurable_snd.sub ((measurable_pi_apply j).comp measurable_fst))
  · exact ((taylor_measurable_h hd hcrit ρ c).comp measurable_snd).const_mul _

include hd hcrit hβ hρ hc in
/-- The truncated field is bounded below by `-K` (`g_H ≥ 0` and `h ≤ C_h`). -/
theorem taylor_field_lower : ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (n : ℕ) (i : Fin n) (H : ℝ), 0 ≤ H →
    ∀ (Y : Config d n) (y : Torus d), -K ≤ taylorFieldH d s c β ρ N i H Y y := by
  obtain ⟨Ch, hCh0, hCh⟩ := taylor_h_bound hd hcrit c hc ρ hρ
  refine ⟨β * Ch, by positivity, fun N n i H hH Y y => ?_⟩
  unfold taylorFieldH
  have h1 : 0 ≤ (β / N) * ∑ j ∈ Finset.univ.erase i, gTrunc d s c H (y - Y j) :=
    mul_nonneg (by positivity) (Finset.sum_nonneg fun j _ => le_min (hc _) hH)
  have h2 : β * convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ β * Ch :=
    mul_le_mul_of_nonneg_left (hCh y).2.2 hβ.le
  linarith

include hd hcrit hβ hρ hc in
theorem taylor_field_bdd (N : ℕ) (n : ℕ) (i : Fin n) (H : ℝ) (hH : 0 ≤ H) (y : Torus d) :
    ∃ B : ℝ, ∀ Y : Config d n, |taylorFieldH d s c β ρ N i H Y y| ≤ B := by
  obtain ⟨Ch, hCh0, hCh⟩ := taylor_h_bound hd hcrit c hc ρ hρ
  refine ⟨(β / N) * (n * H) + β * Ch, fun Y => ?_⟩
  unfold taylorFieldH
  have hg0 : ∀ j, 0 ≤ gTrunc d s c H (y - Y j) := fun j => le_min (hc _) hH
  have hgH : ∀ j, gTrunc d s c H (y - Y j) ≤ H := fun j => min_le_right _ _
  have hsum : ∑ j ∈ Finset.univ.erase i, gTrunc d s c H (y - Y j) ≤ n * H := by
    calc _ ≤ ∑ _j ∈ Finset.univ.erase i, H := Finset.sum_le_sum fun j _ => hgH j
      _ = ((Finset.univ.erase i).card : ℝ) * H := by simp
      _ ≤ n * H := by
        have : ((Finset.univ.erase i).card : ℝ) ≤ n := by
          exact_mod_cast (Finset.card_erase_le).trans (by simp)
        exact mul_le_mul_of_nonneg_right this hH
  have hs0 : 0 ≤ ∑ j ∈ Finset.univ.erase i, gTrunc d s c H (y - Y j) := Finset.sum_nonneg fun j _ => hg0 j
  have hh := hCh y
  have hb : 0 ≤ β / N := by positivity
  rw [abs_le]; constructor
  · nlinarith [mul_nonneg hb hs0, mul_le_mul_of_nonneg_left hh.2.2 hβ.le, mul_nonneg hb (mul_nonneg (Nat.cast_nonneg n) hH)]
  · nlinarith [mul_le_mul_of_nonneg_left hsum hb, mul_nonneg hβ.le hh.2.1, mul_nonneg hβ.le hCh0]

include hd hcrit hβ hρ hc in
/-- The truncated-remainder term in `L^{2q}(μ^{⊗n})`: Jensen in `y`, then `taylor_field_moment`. -/
theorem taylor_B1_bound (q : ℕ) (hq : 1 ≤ q) {K : ℝ} (hK : 0 ≤ K) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ N : ℕ, 2 ≤ N → ∀ H : ℝ, 2 ≤ H → ∀ i : Fin (N - 1), ∀ x : Torus d,
      ∀ φ ∈ ({fun _ => 1, fun y => gPlus d s c (x - y)} : Set (Torus d → ℝ)),
        taylorLp (Measure.pi fun _ : Fin (N - 1) => withDensityReal ρ) ((2 * q : ℕ) : ℝ)
          (fun Y => ∫⁻ y, ENNReal.ofReal (φ y) *
              ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2)
            ∂(withDensityReal ρ)) ≤
        ENNReal.ofReal (Cb * (Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 +
          1 / (N : ℝ) ^ 2)) := by
  have hμ := PoleCavityAux.isProbabilityMeasure_mu hρ
  obtain ⟨hs0, hsd⟩ := PoleCavityAux.hs_aux hd hcrit
  obtain ⟨Cf, hCf0, hCf⟩ := taylor_field_moment hd hcrit β hβ ρ hρ c hc q hq
  obtain ⟨Cp, hCp0, hCp⟩ := taylor_tail_bounds hd hcrit β hβ ρ hρ c hc 2 le_rfl
  refine ⟨Cp * Real.exp K * max Cf 1, by positivity, fun N hN H hH i x φ hφ => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hH0 : 0 < H := by linarith
  have hp0 : (0 : ℝ) < ((2 * q : ℕ) : ℝ) := by exact_mod_cast (by omega : 0 < 2 * q)
  set μ : Measure (Torus d) := withDensityReal ρ with hμdef
  set Pm : Measure (Config d (N - 1)) := Measure.pi fun _ : Fin (N - 1) => μ with hPm
  set Θ : ℝ := Real.log H / N + H ^ 2 / (N : ℝ) ^ 2 + 1 / H ^ 2 + 1 / (N : ℝ) ^ 2 with hΘ
  have hlog : 0 ≤ Real.log H := Real.log_nonneg (by linarith)
  have hΘ0 : 0 ≤ Θ := by positivity
  have hφm : Measurable φ := by
    rcases hφ with rfl | rfl
    · exact measurable_const
    · exact (PoleCavityAux.measurable_gPlus hd hs0 hsd c (s := s)).comp
        (measurable_const.sub measurable_id)
  have hmass : ∫⁻ y, ENNReal.ofReal (φ y) ∂μ ≤ ENNReal.ofReal Cp := (hCp H hH x φ hφ).1
  set Fm : Torus d → ℝ≥0∞ := fun y => ENNReal.ofReal (φ y) with hFm
  have hFmm : Measurable Fm := hφm.ennreal_ofReal
  have hvm := taylor_measurable_fieldH hd hcrit β ρ c (N := N) (N - 1) i H
  set Gf : Config d (N - 1) → Torus d → ℝ≥0∞ :=
    fun Y y => ENNReal.ofReal (Real.exp K * taylorFieldH d s c β ρ N i H Y y ^ 2) with hGf
  have hGfm : Measurable (Function.uncurry Gf) := by
    refine Measurable.ennreal_ofReal ?_
    exact measurable_const.mul (hvm.pow_const 2)
  have hGfy : ∀ Y, Measurable (Gf Y) := fun Y =>
    (hGfm.comp (measurable_const.prodMk measurable_id) : Measurable fun y => Function.uncurry Gf (Y, y))
  have hGfY : ∀ y, Measurable (fun Y => Gf Y y) := fun y =>
    (hGfm.comp (measurable_id.prodMk measurable_const) : Measurable fun Y => Function.uncurry Gf (Y, y))
  -- Jensen in `y`
  have hjen : ∀ Y, (∫⁻ y, Fm y * Gf Y y ∂μ) ^ (2 * q) ≤
      (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ y, Fm y * Gf Y y ^ (2 * q) ∂μ :=
    fun Y => taylor_jensen hFmm (hGfy Y) (2 * q) (by omega)
  -- the `L^{4q}` moment of the field, as a bound on `∫⁻ (G)^{2q}`
  set bd : ℝ := Real.exp K ^ (2 * q) * (Cf * Θ ^ (2 * q)) with hbd
  have hbd0 : 0 ≤ bd := by positivity
  have hY : ∀ y : Torus d, ∫⁻ Y, Gf Y y ^ (2 * q) ∂Pm ≤ ENNReal.ofReal bd := by
    intro y
    obtain ⟨B, hB⟩ := taylor_field_bdd hd hcrit β hβ ρ hρ c hc N (N - 1) i H hH0.le y
    set vv : Config d (N - 1) → ℝ := fun Y => taylorFieldH d s c β ρ N i H Y y with hvv
    have hvvm : Measurable vv :=
      Measurable.of_uncurry_right (f := fun (Y : Config d (N - 1)) (y : Torus d) =>
        taylorFieldH d s c β ρ N i H Y y) hvm
    have hev : Even (4 * q) := ⟨2 * q, by ring⟩
    have e0 : ∀ Y, (Real.exp K * vv Y ^ 2) ^ (2 * q) = Real.exp K ^ (2 * q) * vv Y ^ (4 * q) := by
      intro Y; ring
    have e1 : ∀ Y, Gf Y y ^ (2 * q) = ENNReal.ofReal (Real.exp K ^ (2 * q) * vv Y ^ (4 * q)) := by
      intro Y
      have : Gf Y y = ENNReal.ofReal (Real.exp K * vv Y ^ 2) := rfl
      rw [this, ← ENNReal.ofReal_pow (by positivity), e0]
    simp_rw [e1]
    have hgint : Integrable (fun Y => Real.exp K ^ (2 * q) * vv Y ^ (4 * q)) Pm :=
      taylor_integrable_of_bdd ((hvvm.pow_const _).const_mul _)
        (B := Real.exp K ^ (2 * q) * B ^ (4 * q)) fun Y => by
          rw [abs_mul, abs_pow, abs_pow, abs_of_pos (Real.exp_pos K)]
          gcongr
          exact hB Y
    rw [← ofReal_integral_eq_lintegral_ofReal hgint (Filter.Eventually.of_forall fun Y => by
      have := hev.pow_nonneg (vv Y); positivity)]
    refine ENNReal.ofReal_le_ofReal ?_
    rw [integral_const_mul]
    exact mul_le_mul_of_nonneg_left (hCf N hN H hH i y) (by positivity)
  -- integrate the Jensen bound over `Y`
  have hswap : ∫⁻ Y, ∫⁻ y, Fm y * Gf Y y ^ (2 * q) ∂μ ∂Pm =
      ∫⁻ y, ∫⁻ Y, Fm y * Gf Y y ^ (2 * q) ∂Pm ∂μ := by
    refine lintegral_lintegral_swap ?_
    exact ((hFmm.comp measurable_snd).mul (hGfm.pow_const (2 * q))).aemeasurable
  have hFmfin : (∫⁻ y, Fm y ∂μ) ≠ ∞ := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hmass
  have hmid : ∫⁻ Y, (∫⁻ y, Fm y * Gf Y y ∂μ) ^ (2 * q) ∂Pm ≤
      ENNReal.ofReal Cp ^ (2 * q) * ENNReal.ofReal bd := by
    calc ∫⁻ Y, (∫⁻ y, Fm y * Gf Y y ∂μ) ^ (2 * q) ∂Pm
        ≤ ∫⁻ Y, (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ y, Fm y * Gf Y y ^ (2 * q) ∂μ ∂Pm :=
          lintegral_mono hjen
      _ = (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ Y, ∫⁻ y, Fm y * Gf Y y ^ (2 * q) ∂μ ∂Pm :=
          lintegral_const_mul' _ _ (ENNReal.pow_ne_top hFmfin)
      _ = (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ y, ∫⁻ Y, Fm y * Gf Y y ^ (2 * q) ∂Pm ∂μ := by
          rw [hswap]
      _ ≤ (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ∫⁻ y, Fm y * ENNReal.ofReal bd ∂μ := by
          refine mul_le_mul' le_rfl (lintegral_mono fun y => ?_)
          rw [lintegral_const_mul _ ((hGfY y).pow_const _)]
          exact mul_le_mul' le_rfl (hY y)
      _ = (∫⁻ y, Fm y ∂μ) ^ (2 * q - 1) * ((∫⁻ y, Fm y ∂μ) * ENNReal.ofReal bd) := by
          rw [lintegral_mul_const _ hFmm]
      _ = (∫⁻ y, Fm y ∂μ) ^ (2 * q) * ENNReal.ofReal bd := by
          rw [← mul_assoc, ← pow_succ]
          congr 2; omega
      _ ≤ ENNReal.ofReal Cp ^ (2 * q) * ENNReal.ofReal bd := by gcongr
  refine taylorLp_le_of_lintegral_le hp0 _ ?_
  simp_rw [ENNReal.rpow_natCast]
  refine hmid.trans ?_
  rw [← ENNReal.ofReal_pow hCp0, ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_pow (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  have hmx : Cf ≤ max Cf 1 ^ (2 * q) := by
    calc Cf ≤ max Cf 1 := le_max_left _ _
      _ = max Cf 1 ^ 1 := (pow_one _).symm
      _ ≤ max Cf 1 ^ (2 * q) := pow_le_pow_right₀ (le_max_right _ _) (by omega)
  calc Cp ^ (2 * q) * bd = Cp ^ (2 * q) * Real.exp K ^ (2 * q) * (Cf * Θ ^ (2 * q)) := by
        rw [hbd]; ring
    _ ≤ Cp ^ (2 * q) * Real.exp K ^ (2 * q) * (max Cf 1 ^ (2 * q) * Θ ^ (2 * q)) := by
        gcongr
    _ = (Cp * Real.exp K * max Cf 1 * Θ) ^ (2 * q) := by
        rw [mul_pow, mul_pow, mul_pow]; ring

end Field

end HRS.TaylorAux
