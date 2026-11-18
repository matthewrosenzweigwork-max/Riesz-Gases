/-
# HRS.Equilibrium.L48Aux3 — Proposition 4.8, part 3: the linear term `∫ ψ v_Y dμ` in `L²(P)`

For a test `ψ` with `‖ψ‖₁ ≤ A` and `‖∫ |ψ(y)| g₊(y - ·) dμ(y)‖_{L²(μ)}² ≤ K`:
`‖∫ ψ v_Y dμ‖_{L²(P)} ≤ C (√K + A) N^{-1/2}`  (TeX `R:eq:L-linear-bound`).
Proof: `∫ ψ v_Y dμ = λ ∑_{j≠i} Φ(y_j) - β μ(Φ)`, `Φ(z) = ∫ ψ(y) g₊(y - z) dμ(y)` (Fubini and the
exact identity `∫ ψ h dμ = μ(Φ)`), the pole variance estimate for `∑_j Φ(y_j)` and
`l48_mean_shift` for the mean.
-/
import HRS.Equilibrium.L48Aux2

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace L48

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

/-- `Φ(z) = ∫ ψ(y) g₊(y - z) dμ(y)`. -/
def l48_Phi (d : ℕ) (s c : ℝ) (ρ : Torus d → ℝ) (ψ : Torus d → ℝ) (z : Torus d) : ℝ :=
  ∫ y, ψ y * gPlus d s c (y - z) ∂(withDensityReal ρ)

/-- `Φ_abs(z) = ∫ |ψ(y)| g₊(y - z) dμ(y)` (an extended nonnegative number). -/
def l48_Phiabs (d : ℕ) (s c : ℝ) (ρ : Torus d → ℝ) (ψ : Torus d → ℝ) (z : Torus d) : ℝ≥0∞ :=
  ∫⁻ y, ENNReal.ofReal (|ψ y| * gPlus d s c (y - z)) ∂(withDensityReal ρ)

section PhiFacts

variable (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) {β : ℝ} (hβ : 0 < β) {ρ : Torus d → ℝ}
  (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)

include hd hcrit hβ hρ hc

theorem l48_meas_Phi {ψ : Torus d → ℝ} (hψ : Measurable ψ) :
    Measurable (l48_Phi d s c ρ ψ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  unfold l48_Phi
  have h : StronglyMeasurable fun q : Torus d × Torus d => ψ q.2 * gPlus d s c (q.2 - q.1) :=
    ((hψ.comp measurable_snd).mul (hgm.comp (measurable_snd.sub measurable_fst))).stronglyMeasurable
  exact (h.integral_prod_right' (ν := withDensityReal ρ)).measurable

theorem l48_meas_Phiabs {ψ : Torus d → ℝ} (hψ : Measurable ψ) :
    Measurable (l48_Phiabs d s c ρ ψ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  unfold l48_Phiabs
  have h : Measurable fun q : Torus d × Torus d =>
      ENNReal.ofReal (|ψ q.2| * gPlus d s c (q.2 - q.1)) :=
    ENNReal.measurable_ofReal.comp
      ((hψ.comp measurable_snd).abs.mul (hgm.comp (measurable_snd.sub measurable_fst)))
  exact h.lintegral_prod_right' (ν := withDensityReal ρ)

theorem l48_Phi_enorm_le {ψ : Torus d → ℝ} (hψ : Measurable ψ) (z : Torus d) :
    ‖l48_Phi d s c ρ ψ z‖ₑ ≤ l48_Phiabs d s c ρ ψ z := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  unfold l48_Phi l48_Phiabs
  refine (enorm_integral_le_lintegral_enorm _).trans (le_of_eq ?_)
  refine lintegral_congr fun y => ?_
  have hG0 : 0 ≤ gPlus d s c (y - z) := hc _
  rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg hG0]

/-- `L²` bound for `Φ` and a.e. finiteness of `Φ_abs`. -/
theorem l48_Phi_sq_le {ψ : Torus d → ℝ} (hψ : Measurable ψ) {K : ℝ}
    (hK : ∫⁻ z, l48_Phiabs d s c ρ ψ z ^ 2 ∂(withDensityReal ρ) ≤ ENNReal.ofReal K) :
    ∫⁻ z, ENNReal.ofReal (l48_Phi d s c ρ ψ z ^ 2) ∂(withDensityReal ρ) ≤ ENNReal.ofReal K := by
  refine le_trans (lintegral_mono fun z => ?_) hK
  have h1 := l48_Phi_enorm_le hd hcrit hβ hρ hc hψ z
  have h2 : ENNReal.ofReal (l48_Phi d s c ρ ψ z ^ 2) = ‖l48_Phi d s c ρ ψ z‖ₑ ^ 2 := by
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  rw [h2]
  exact pow_le_pow_left' h1 2

theorem l48_Phiabs_ae_lt_top {ψ : Torus d → ℝ} (hψ : Measurable ψ) {K : ℝ}
    (hK : ∫⁻ z, l48_Phiabs d s c ρ ψ z ^ 2 ∂(withDensityReal ρ) ≤ ENNReal.ofReal K) :
    ∀ᵐ z ∂(withDensityReal ρ), l48_Phiabs d s c ρ ψ z < ⊤ := by
  have hm := l48_meas_Phiabs hd hcrit hβ hρ hc hψ
  have h2 : ∀ᵐ z ∂(withDensityReal ρ), l48_Phiabs d s c ρ ψ z ^ 2 < ⊤ :=
    ae_lt_top (hm.pow_const 2) (lt_of_le_of_lt hK ENNReal.ofReal_lt_top).ne
  filter_upwards [h2] with z hz
  by_contra h
  rw [not_lt, top_le_iff] at h
  rw [h] at hz
  simp at hz

/-- Fubini: `∫ ψ (g₊ * μ) dμ = ∫ Φ dμ`. -/
theorem l48_int_psi_h {ψ : Torus d → ℝ} (hψ : Measurable ψ) (hψ1 : Integrable ψ (withDensityReal ρ)) :
    ∫ y, ψ y * convMeasure (gPlus d s c) (withDensityReal ρ) y ∂(withDensityReal ρ) =
      ∫ z, l48_Phi d s c ρ ψ z ∂(withDensityReal ρ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  obtain ⟨Cg, hCg0, hCg⟩ := conv_gPlus hd hs0 hsd hρ hc
  have hF : AEStronglyMeasurable (fun q : Torus d × Torus d => ψ q.1 * gPlus d s c (q.1 - q.2))
      ((withDensityReal ρ).prod (withDensityReal ρ)) :=
    ((hψ.comp measurable_fst).mul (hgm.comp (measurable_fst.sub measurable_snd))).aestronglyMeasurable
  have hint : Integrable (fun q : Torus d × Torus d => ψ q.1 * gPlus d s c (q.1 - q.2))
      ((withDensityReal ρ).prod (withDensityReal ρ)) := by
    rw [integrable_prod_iff hF]
    refine ⟨Eventually.of_forall fun y => ?_, ?_⟩
    · exact (gPlus_int hd hcrit hβ hρ hc hs0 hsd y).const_mul (ψ y)
    · have e : ∀ y, ∫ z, ‖ψ y * gPlus d s c (y - z)‖ ∂(withDensityReal ρ) =
          |ψ y| * convMeasure (gPlus d s c) (withDensityReal ρ) y := by
        intro y
        unfold convMeasure
        rw [← integral_const_mul]
        refine integral_congr_ae (Eventually.of_forall fun z => ?_)
        have hG0 : 0 ≤ gPlus d s c (y - z) := hc _
        simp only [norm_mul, Real.norm_eq_abs, abs_of_nonneg hG0]
      simp_rw [e]
      refine Integrable.mono' (hψ1.abs.mul_const Cg)
        ((hψ.abs.mul (measurable_convMeasure hgm _)).aestronglyMeasurable)
        (Eventually.of_forall fun y => ?_)
      rw [Real.norm_eq_abs, abs_mul, abs_abs, abs_of_nonneg (hCg y).1]
      exact mul_le_mul_of_nonneg_left (hCg y).2 (abs_nonneg _)
  have h1 : ∀ y, ψ y * convMeasure (gPlus d s c) (withDensityReal ρ) y =
      ∫ z, ψ y * gPlus d s c (y - z) ∂(withDensityReal ρ) := fun y => by
    unfold convMeasure; rw [integral_const_mul]
  simp_rw [h1]
  unfold l48_Phi
  exact integral_integral_swap hint

theorem l48_abs_int_psi_h_le {ψ : Torus d → ℝ} (hψ : Measurable ψ) (hψ1 : Integrable ψ (withDensityReal ρ))
    {Cg : ℝ} (hCg : ∀ y, 0 ≤ convMeasure (gPlus d s c) (withDensityReal ρ) y ∧
      convMeasure (gPlus d s c) (withDensityReal ρ) y ≤ Cg) :
    |∫ y, ψ y * convMeasure (gPlus d s c) (withDensityReal ρ) y ∂(withDensityReal ρ)| ≤
      Cg * ∫ y, |ψ y| ∂(withDensityReal ρ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  refine (abs_integral_le_integral_abs).trans ?_
  rw [← integral_const_mul]
  refine integral_mono_of_nonneg (Eventually.of_forall fun y => abs_nonneg _)
    (hψ1.abs.const_mul Cg) (Eventually.of_forall fun y => ?_)
  show |ψ y * convMeasure (gPlus d s c) (withDensityReal ρ) y| ≤ Cg * |ψ y|
  rw [abs_mul, abs_of_nonneg (hCg y).1, mul_comm]
  exact mul_le_mul_of_nonneg_right (hCg y).2 (abs_nonneg _)

theorem l48_ell_ae {N : ℕ} (hN : 2 ≤ N) (x : Torus d) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) 1)
    (i : Fin (N - 1)) {ψ : Torus d → ℝ} (hψ : Measurable ψ)
    (hψ1 : Integrable ψ (withDensityReal ρ)) {K : ℝ}
    (hK : ∫⁻ z, l48_Phiabs d s c ρ ψ z ^ 2 ∂(withDensityReal ρ) ≤ ENNReal.ofReal K) :
    ∀ᵐ Y ∂(critPole d s c β ρ N x t),
      ∫ y, ψ y * cavityField d s c β ρ N i Y y ∂(withDensityReal ρ) =
        (β / N) * ∑ j ∈ Finset.univ.erase i, l48_Phi d s c ρ ψ (Y j) -
          β * ∫ z, l48_Phi d s c ρ ψ z ∂(withDensityReal ρ) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  obtain ⟨Cg, hCg0, hCg⟩ := conv_gPlus hd hs0 hsd hρ hc
  obtain ⟨M1, hM1, hM⟩ := pole_marg_le hd hs0 hsd hβ hρ
  have hgood := l48_Phiabs_ae_lt_top hd hcrit hβ hρ hc hψ hK
  have hPeq : critPole d s c β ρ N x t =
      poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t :=
    critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t
  -- almost every `Y` has all `Φ_abs (Y j)` finite
  have hall : ∀ᵐ Y ∂(critPole d s c β ρ N x t), ∀ j : Fin (N - 1), l48_Phiabs d s c ρ ψ (Y j) < ⊤ := by
    rw [ae_all_iff]
    intro j
    have hmap := (hM N hN x t ht).2 j
    rw [← hPeq] at hmap
    have hac : (critPole d s c β ρ N x t).map (fun Y : Config d (N - 1) => Y j) ≪ withDensityReal ρ :=
      Measure.absolutelyContinuous_of_le_smul hmap
    exact ae_of_ae_map (measurable_pi_apply j).aemeasurable (hac hgood)
  filter_upwards [hall] with Y hY
  have hI : ∀ j : Fin (N - 1), Integrable (fun y => ψ y * gPlus d s c (y - Y j)) (withDensityReal ρ) := by
    intro j
    refine ⟨(hψ.mul (hgm.comp (measurable_id.sub measurable_const))).aestronglyMeasurable, ?_⟩
    have := hY j
    unfold l48_Phiabs at this
    refine lt_of_le_of_lt (le_of_eq ?_) this
    refine lintegral_congr fun y => ?_
    have hG0 : 0 ≤ gPlus d s c (y - Y j) := hc _
    rw [Real.enorm_eq_ofReal_abs, abs_mul, abs_of_nonneg hG0]
  have hhi : Integrable (fun y => ψ y * convMeasure (gPlus d s c) (withDensityReal ρ) y) (withDensityReal ρ) := by
    refine Integrable.mono' (hψ1.abs.mul_const Cg)
      ((hψ.mul (measurable_convMeasure hgm _)).aestronglyMeasurable)
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hCg y).1]
    exact mul_le_mul_of_nonneg_left (hCg y).2 (abs_nonneg _)
  have e1 : ∀ y, ψ y * cavityField d s c β ρ N i Y y =
      (β / N) * ∑ j ∈ Finset.univ.erase i, ψ y * gPlus d s c (y - Y j) -
        β * (ψ y * convMeasure (gPlus d s c) (withDensityReal ρ) y) := by
    intro y
    unfold cavityField
    rw [← Finset.mul_sum]
    ring
  simp_rw [e1]
  rw [integral_sub ((integrable_finsetSum _ fun j _ => hI j).const_mul _) (hhi.const_mul _),
    integral_const_mul, integral_const_mul, integral_finsetSum _ fun j _ => hI j,
    l48_int_psi_h hd hcrit hβ hρ hc hψ hψ1]
  rfl

/-- Pole variance of the empirical sum of `Φ(y_j)` (TeX: "the pole variance estimate for all `n`
coordinates"). -/
theorem l48_var_S :
    ∃ Cv : ℝ, 0 ≤ Cv ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1,
      ∀ Φ : Torus d → ℝ, Measurable Φ → ∀ K : ℝ, 0 < K →
        ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) ≤ ENNReal.ofReal K →
        ∫⁻ Y, ENNReal.ofReal ((∑ j, Φ (Y j) - ∫ Y', ∑ j, Φ (Y' j) ∂(critPole d s c β ρ N x t)) ^ 2)
          ∂(critPole d s c β ρ N x t) ≤ ENNReal.ofReal (Cv * K * N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨C₁, hC₁, hvar⟩ := PoleCavityAux.pole_variance_clause hd hs0 hsd β hβ ρ hρ
  refine ⟨C₁ * Real.exp (β * |c|), by positivity, fun N hN x t ht Φ hΦ K hK hKint => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hlam : 0 ≤ β / N := by positivity
  rw [critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t]
  have h1 := hvar N hN x t ht Φ hΦ
  have hE : ∫⁻ y, ‖Φ y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y)))
      ∂(withDensityReal ρ) ≤ ENNReal.ofReal (Real.exp (β * |c|)) * ENNReal.ofReal K := by
    calc _ ≤ ∫⁻ y, ENNReal.ofReal (Real.exp (β * |c|)) * ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) := by
          refine lintegral_mono fun y => ?_
          have e2 : ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y))) ≤
              ENNReal.ofReal (Real.exp (β * |c|)) := by
            refine ENNReal.ofReal_le_ofReal (Real.exp_le_exp.2 ?_)
            have h4 := hc (x - y)
            have h5 : 0 ≤ t * (β / N) := mul_nonneg ht.1 hlam
            have h6 : t * (β / N) ≤ β := by
              have : β / N ≤ β := by
                rw [div_le_iff₀ hN0]
                have : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
                nlinarith
              nlinarith [ht.2]
            have h7 : -(t * (β / N)) * periodicRiesz d s (x - y) ≤ (t * (β / N)) * c := by nlinarith
            have h8 : (t * (β / N)) * c ≤ (t * (β / N)) * |c| :=
              mul_le_mul_of_nonneg_left (le_abs_self c) h5
            have h9 : (t * (β / N)) * |c| ≤ β * |c| := mul_le_mul_of_nonneg_right h6 (abs_nonneg _)
            linarith
          have e3 : ‖Φ y‖ₑ ^ 2 = ENNReal.ofReal (Φ y ^ 2) := by
            rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
          rw [e3, mul_comm]
          exact mul_le_mul' e2 le_rfl
      _ = ENNReal.ofReal (Real.exp (β * |c|)) * ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) :=
          lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
      _ ≤ _ := mul_le_mul' le_rfl hKint
  have h2 := h1.trans (mul_le_mul' le_rfl hE)
  rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← ENNReal.ofReal_mul (by positivity)] at h2
  unfold evariance at h2
  refine le_trans (le_of_eq ?_) (h2.trans (ENNReal.ofReal_le_ofReal ?_))
  · refine lintegral_congr fun Y => ?_
    rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _), sq_abs]
  · have hn : ((N - 1 : ℕ) : ℝ) ≤ N := by exact_mod_cast (by omega : N - 1 ≤ N)
    have hKp := hK.le
    have : C₁ * ((N - 1 : ℕ) : ℝ) * (Real.exp (β * |c|) * K) ≤ C₁ * Real.exp (β * |c|) * K * N := by
      have h0 : 0 ≤ C₁ * (Real.exp (β * |c|) * K) := by positivity
      nlinarith [mul_le_mul_of_nonneg_left hn h0]
    exact this

/-- The `i`-th coordinate of `Φ` in `L²(P)`. -/
theorem l48_Phi_i :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin (N - 1),
      ∀ Φ : Torus d → ℝ, Measurable Φ → ∀ K : ℝ, 0 < K →
        ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) ≤ ENNReal.ofReal K →
        ∫⁻ Y, ENNReal.ofReal (Φ (Y i) ^ 2) ∂(critPole d s c β ρ N x t) ≤ ENNReal.ofReal (M * K) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨M1, hM1, hM⟩ := pole_marg_le hd hs0 hsd hβ hρ
  refine ⟨M1, hM1.le, fun N hN x t ht i Φ hΦ K hK hKint => ?_⟩
  have hmap := (hM N hN x t ht).2 i
  rw [← critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t] at hmap
  calc ∫⁻ Y, ENNReal.ofReal (Φ (Y i) ^ 2) ∂(critPole d s c β ρ N x t)
      = ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂((critPole d s c β ρ N x t).map
          (fun Y : Config d (N - 1) => Y i)) :=
        (lintegral_map (ENNReal.measurable_ofReal.comp (hΦ.pow_const 2)) (measurable_pi_apply i)).symm
    _ ≤ ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(ENNReal.ofReal M1 • withDensityReal ρ) :=
        lintegral_mono' hmap le_rfl
    _ = ENNReal.ofReal M1 * ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) :=
        lintegral_smul_measure _ _
    _ ≤ ENNReal.ofReal M1 * ENNReal.ofReal K := mul_le_mul' le_rfl hKint
    _ = ENNReal.ofReal (M1 * K) := (ENNReal.ofReal_mul hM1.le).symm

theorem l48_delta_le {N : ℕ} (hN : 2 ≤ N) :
    deltaN d s N ≤ 2 / Real.sqrt N := by
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hNd := N_mul_deltaN_crit (d := d) hcrit (by omega : 1 ≤ N)
  have hδ : deltaN d s N = (1 + Real.log N) / N := by
    rw [eq_div_iff hN0.ne', mul_comm]; exact hNd
  have hS0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hSS : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have h1 : Real.log (Real.sqrt N) ≤ Real.sqrt N - 1 := Real.log_le_sub_one_of_pos hS0
  have h2 : Real.log (Real.sqrt N) = Real.log N / 2 := Real.log_sqrt hN0.le
  rw [hδ, div_le_div_iff₀ hN0 hS0]
  nlinarith

theorem l48_marg_dom :
    ∃ M1 : ℝ, 0 < M1 ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ j : Fin (N - 1),
      (critPole d s c β ρ N x t).map (fun Y : Config d (N - 1) => Y j) ≤
        ENNReal.ofReal M1 • withDensityReal ρ := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  obtain ⟨M1, hM1, hM⟩ := pole_marg_le hd hs0 hsd hβ hρ
  refine ⟨M1, hM1, fun N hN x t ht j => ?_⟩
  rw [critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t]
  exact (hM N hN x t ht).2 j

theorem l48_sq_integrable {Φ : Torus d → ℝ} (hΦ : Measurable Φ) {K : ℝ}
    (hKint : ∫⁻ y, ENNReal.ofReal (Φ y ^ 2) ∂(withDensityReal ρ) ≤ ENNReal.ofReal K) :
    Integrable (fun y => Φ y ^ 2) (withDensityReal ρ) ∧ Integrable Φ (withDensityReal ρ) := by
  have hμ := isProbabilityMeasure_mu hρ
  have hΦ2i : Integrable (fun y => Φ y ^ 2) (withDensityReal ρ) := by
    refine ⟨(hΦ.pow_const 2).aestronglyMeasurable, ?_⟩
    refine lt_of_le_of_lt (le_of_eq ?_) (lt_of_le_of_lt hKint ENNReal.ofReal_lt_top)
    refine lintegral_congr fun y => ?_
    rw [Real.enorm_eq_ofReal_abs, abs_of_nonneg (sq_nonneg _)]
  refine ⟨hΦ2i, ?_⟩
  have hmem : MemLp Φ 2 (withDensityReal ρ) :=
    (memLp_two_iff_integrable_sq hΦ.aestronglyMeasurable).2 hΦ2i
  exact hmem.integrable (by norm_num)

set_option maxHeartbeats 800000 in
/-- The linear term `∫ ψ v_Y dμ` in `L²(P)` (TeX `R:eq:L-linear-bound`). -/
theorem l48_linear :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, ∀ i : Fin (N - 1),
      ∀ ψ : Torus d → ℝ, Measurable ψ → Integrable ψ (withDensityReal ρ) → ∀ A K : ℝ, 0 < K → 0 ≤ A →
        ∫ y, |ψ y| ∂(withDensityReal ρ) ≤ A →
        ∫⁻ z, l48_Phiabs d s c ρ ψ z ^ 2 ∂(withDensityReal ρ) ≤ ENNReal.ofReal K →
        eLpNorm (fun Y : Config d (N - 1) =>
            ∫ y, ψ y * cavityField d s c β ρ N i Y y ∂(withDensityReal ρ)) 2
          (critPole d s c β ρ N x t) ≤ ENNReal.ofReal (C * (Real.sqrt K + A) / Real.sqrt N) := by
  obtain ⟨hs0, hsd⟩ := hs_aux hd hcrit
  have hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cg, hCg0, hCg⟩ := conv_gPlus hd hs0 hsd hρ hc
  obtain ⟨Cv, hCv0, hvarS⟩ := l48_var_S hd hcrit hβ hρ hc
  obtain ⟨M, hM0, hMi⟩ := l48_Phi_i hd hcrit hβ hρ hc
  obtain ⟨Cms, hCms0, hms⟩ := l48_mean_shift hd hcrit hβ hρ hc
  obtain ⟨M1, hM1, hdom⟩ := l48_marg_dom hd hcrit hβ hρ hc
  refine ⟨β * (Real.sqrt Cv + Real.sqrt M + 2 * Cms + Cg), by positivity,
    fun N hN x t ht i ψ hψ hψ1 A K hK hA hAint hKint => ?_⟩
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hr0 : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hr1 : 1 ≤ Real.sqrt N := Real.one_le_sqrt.2 (by exact_mod_cast (by omega : 1 ≤ N))
  have hrr : Real.sqrt N * Real.sqrt N = N := Real.mul_self_sqrt hN0.le
  have hlam : 0 ≤ β / N := by positivity
  have hPprob : IsProbabilityMeasure (critPole d s c β ρ N x t) := by
    rw [critPole_eq_poleLaw (c := c) hd hs0 hsd β hβ hρ hN x t]
    exact pole_isProb hd hs0 hsd β hρ (N - 1) (β / N) hlam x t ht.1
  set Φ := l48_Phi d s c ρ ψ with hΦdef
  have hΦm : Measurable Φ := l48_meas_Phi hd hcrit hβ hρ hc hψ
  have hΦK := l48_Phi_sq_le hd hcrit hβ hρ hc hψ hKint
  obtain ⟨hΦ2i, hΦ1i⟩ := l48_sq_integrable hd hcrit hβ hρ hc hΦm hΦK
  have hae := l48_ell_ae hd hcrit hβ hρ hc hN x ht i hψ hψ1 hKint
  set S : Config d (N - 1) → ℝ := fun Y => ∑ j, Φ (Y j) with hS
  have hSm : Measurable S := Finset.measurable_sum _ fun j _ => hΦm.comp (measurable_pi_apply j)
  set m : ℝ := ∫ Y, S Y ∂(critPole d s c β ρ N x t) with hm
  set μΦ : ℝ := ∫ z, Φ z ∂(withDensityReal ρ) with hμΦ
  set c0 : ℝ := (β / N) * m - β * μΦ with hc0
  have hℓ : (fun Y : Config d (N - 1) =>
        ∫ y, ψ y * cavityField d s c β ρ N i Y y ∂(withDensityReal ρ)) =ᵐ[critPole d s c β ρ N x t]
      (fun Y => (β / N) * (S Y - m) - (β / N) * Φ (Y i) + c0) := by
    filter_upwards [hae] with Y hY
    rw [hY]
    have h := l48_split_erase i (fun j => Φ (Y j))
    simp only [hS, hc0]
    rw [h]
    ring
  rw [eLpNorm_congr_ae hℓ]
  have hsplit : (fun Y : Config d (N - 1) => (β / N) * (S Y - m) - (β / N) * Φ (Y i) + c0) =
      ((fun Y => (β / N) * (S Y - m)) - (fun Y => (β / N) * Φ (Y i))) + (fun _ => c0) := rfl
  rw [hsplit]
  -- the three pieces
  have hb1 : eLpNorm (fun Y : Config d (N - 1) => (β / N) * (S Y - m)) 2 (critPole d s c β ρ N x t) ≤
      ENNReal.ofReal ((β / N) * Real.sqrt (Cv * K * N)) := by
    have hS2 : eLpNorm (fun Y => S Y - m) 2 (critPole d s c β ρ N x t) ≤
        ENNReal.ofReal (Real.sqrt (Cv * K * N)) := by
      refine (l48_eLpNorm_le_iff (f := fun Y : Config d (N - 1) => S Y - m)
        (hSm.sub measurable_const) (Real.sqrt_nonneg _)).2 ?_
      rw [Real.sq_sqrt (by positivity)]
      exact hvarS N hN x t ht Φ hΦm K hK hΦK
    calc eLpNorm (fun Y : Config d (N - 1) => (β / N) * (S Y - m)) 2 (critPole d s c β ρ N x t)
        = eLpNorm ((β / N) • fun Y => S Y - m) 2 (critPole d s c β ρ N x t) := rfl
      _ ≤ ‖β / N‖ₑ * eLpNorm (fun Y => S Y - m) 2 (critPole d s c β ρ N x t) := eLpNorm_const_smul_le
      _ ≤ ENNReal.ofReal (β / N) * ENNReal.ofReal (Real.sqrt (Cv * K * N)) := by
          rw [Real.enorm_eq_ofReal hlam]; exact mul_le_mul' le_rfl hS2
      _ = _ := (ENNReal.ofReal_mul hlam).symm
  have hb2 : eLpNorm (fun Y : Config d (N - 1) => (β / N) * Φ (Y i)) 2 (critPole d s c β ρ N x t) ≤
      ENNReal.ofReal ((β / N) * Real.sqrt (M * K)) := by
    have hΦ2 : eLpNorm (fun Y : Config d (N - 1) => Φ (Y i)) 2 (critPole d s c β ρ N x t) ≤
        ENNReal.ofReal (Real.sqrt (M * K)) := by
      refine (l48_eLpNorm_le_iff (f := fun Y : Config d (N - 1) => Φ (Y i))
        (hΦm.comp (measurable_pi_apply i)) (Real.sqrt_nonneg _)).2 ?_
      rw [Real.sq_sqrt (by positivity)]
      exact hMi N hN x t ht i Φ hΦm K hK hΦK
    calc eLpNorm (fun Y : Config d (N - 1) => (β / N) * Φ (Y i)) 2 (critPole d s c β ρ N x t)
        = eLpNorm ((β / N) • fun Y : Config d (N - 1) => Φ (Y i)) 2 (critPole d s c β ρ N x t) := rfl
      _ ≤ ‖β / N‖ₑ * eLpNorm (fun Y : Config d (N - 1) => Φ (Y i)) 2 (critPole d s c β ρ N x t) :=
          eLpNorm_const_smul_le
      _ ≤ ENNReal.ofReal (β / N) * ENNReal.ofReal (Real.sqrt (M * K)) := by
          rw [Real.enorm_eq_ofReal hlam]; exact mul_le_mul' le_rfl hΦ2
      _ = _ := (ENNReal.ofReal_mul hlam).symm
  have hb3 : eLpNorm (fun _ : Config d (N - 1) => c0) 2 (critPole d s c β ρ N x t) =
      ENNReal.ofReal |c0| := by
    rw [eLpNorm_const c0 (by norm_num) (IsProbabilityMeasure.ne_zero _)]
    simp [Real.enorm_eq_ofReal_abs]
  -- the constant
  have hδ0 : 0 ≤ deltaN d s N := by
    have := inv_le_deltaN (d := d) hs0 N (by omega)
    exact (inv_nonneg.2 hN0.le).trans this
  have hδ := l48_delta_le hd hcrit hβ hρ hc hN
  have hmj : ∀ j : Fin (N - 1), |∫ Y, Φ (Y j) ∂(critPole d s c β ρ N x t) - μΦ| ≤
      Cms * Real.sqrt K * deltaN d s N := fun j => hms N hN x t ht j Φ hΦm K hK hΦK
  have hint_j : ∀ j : Fin (N - 1), Integrable (fun Y : Config d (N - 1) => Φ (Y j))
      (critPole d s c β ρ N x t) := by
    intro j
    have h1 : Integrable Φ ((critPole d s c β ρ N x t).map (fun Y : Config d (N - 1) => Y j)) :=
      (hΦ1i.smul_measure ENNReal.ofReal_ne_top).mono_measure (hdom N hN x t ht j)
    exact (integrable_map_measure hΦm.aestronglyMeasurable (measurable_pi_apply j).aemeasurable).1 h1
  have hmsum : m = ∑ j : Fin (N - 1), ∫ Y, Φ (Y j) ∂(critPole d s c β ρ N x t) := by
    simp only [hm, hS]
    exact integral_finsetSum _ fun j _ => hint_j j
  have hn : ((N - 1 : ℕ) : ℝ) = N - 1 := by rw [Nat.cast_sub (by omega : 1 ≤ N), Nat.cast_one]
  have hmn : |m - ((N - 1 : ℕ) : ℝ) * μΦ| ≤ ((N - 1 : ℕ) : ℝ) * (Cms * Real.sqrt K * deltaN d s N) := by
    have e : m - ((N - 1 : ℕ) : ℝ) * μΦ =
        ∑ j : Fin (N - 1), (∫ Y, Φ (Y j) ∂(critPole d s c β ρ N x t) - μΦ) := by
      rw [hmsum, Finset.sum_sub_distrib]
      simp
    rw [e]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun j _ => hmj j).trans (le_of_eq ?_)
    simp
  have hμΦ_le : |μΦ| ≤ Cg * A := by
    have e1 : μΦ = ∫ y, ψ y * convMeasure (gPlus d s c) (withDensityReal ρ) y ∂(withDensityReal ρ) :=
      (l48_int_psi_h hd hcrit hβ hρ hc hψ hψ1).symm
    rw [e1]
    exact (l48_abs_int_psi_h_le hd hcrit hβ hρ hc hψ hψ1 hCg).trans
      (mul_le_mul_of_nonneg_left hAint hCg0)
  have hc0e : c0 = (β / N) * (m - ((N - 1 : ℕ) : ℝ) * μΦ) - (β / N) * μΦ := by
    simp only [hc0]
    rw [hn]
    field_simp
    ring
  have hc0b : |c0| ≤ β * (Cms * Real.sqrt K * deltaN d s N) + β * Cg * A / N := by
    rw [hc0e]
    have e1 : |(β / N) * (m - ((N - 1 : ℕ) : ℝ) * μΦ)| ≤ β * (Cms * Real.sqrt K * deltaN d s N) := by
      rw [abs_mul, abs_of_nonneg hlam]
      have h2 : (β / N) * ((N - 1 : ℕ) : ℝ) ≤ β := by
        rw [hn]
        have : (β / N) * ((N : ℝ) - 1) = β - β / N := by field_simp
        rw [this]; linarith
      calc (β / N) * |m - ((N - 1 : ℕ) : ℝ) * μΦ|
          ≤ (β / N) * (((N - 1 : ℕ) : ℝ) * (Cms * Real.sqrt K * deltaN d s N)) :=
            mul_le_mul_of_nonneg_left hmn hlam
        _ = ((β / N) * ((N - 1 : ℕ) : ℝ)) * (Cms * Real.sqrt K * deltaN d s N) := by ring
        _ ≤ β * (Cms * Real.sqrt K * deltaN d s N) :=
            mul_le_mul_of_nonneg_right h2 (by positivity)
    have e2 : |(β / N) * μΦ| ≤ β * Cg * A / N := by
      rw [abs_mul, abs_of_nonneg hlam]
      calc (β / N) * |μΦ| ≤ (β / N) * (Cg * A) := mul_le_mul_of_nonneg_left hμΦ_le hlam
        _ = β * Cg * A / N := by ring
    calc |(β / N) * (m - ((N - 1 : ℕ) : ℝ) * μΦ) - (β / N) * μΦ|
        ≤ |(β / N) * (m - ((N - 1 : ℕ) : ℝ) * μΦ)| + |(β / N) * μΦ| := abs_sub _ _
      _ ≤ _ := add_le_add e1 e2
  -- assemble
  refine (eLpNorm_add_le (by norm_num)).trans ?_
  refine (add_le_add ((eLpNorm_sub_le (by norm_num)).trans (add_le_add hb1 hb2)) (le_of_eq hb3)).trans ?_
  rw [← ENNReal.ofReal_add (by positivity) (by positivity), ← ENNReal.ofReal_add (by positivity) (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  -- real inequality
  set r := Real.sqrt N with hr
  have hsK := Real.sqrt_nonneg K
  have e1 : (β / N) * Real.sqrt (Cv * K * N) = β * Real.sqrt Cv * Real.sqrt K / r := by
    rw [Real.sqrt_mul (by positivity), Real.sqrt_mul hCv0]
    rw [← hr, ← hrr]
    field_simp
  have e2 : (β / N) * Real.sqrt (M * K) = β * Real.sqrt M * Real.sqrt K / (r * r) := by
    rw [Real.sqrt_mul hM0, ← hrr]
    field_simp
  have e2' : β * Real.sqrt M * Real.sqrt K / (r * r) ≤ β * Real.sqrt M * Real.sqrt K / r := by
    refine div_le_div_of_nonneg_left (by positivity) hr0 ?_
    nlinarith
  have e3 : β * (Cms * Real.sqrt K * deltaN d s N) ≤ β * (Cms * Real.sqrt K * (2 / r)) :=
    mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hδ (by positivity)) hβ.le
  have e4 : β * Cg * A / N ≤ β * Cg * A / r := by
    rw [← hrr]
    refine div_le_div_of_nonneg_left (by positivity) hr0 ?_
    nlinarith
  have hfin : β * Real.sqrt Cv * Real.sqrt K / r + β * Real.sqrt M * Real.sqrt K / r +
      β * Cms * Real.sqrt K * (2 / r) + β * Cg * A / r =
      (β * (Real.sqrt Cv + Real.sqrt M + 2 * Cms + Cg) * (Real.sqrt K + A) / r) -
        (β * Cg * Real.sqrt K / r + β * (Real.sqrt Cv + Real.sqrt M + 2 * Cms) * A / r) := by
    field_simp
    ring
  have hrest : 0 ≤ β * Cg * Real.sqrt K / r + β * (Real.sqrt Cv + Real.sqrt M + 2 * Cms) * A / r := by
    positivity
  have hmain : (β / N) * Real.sqrt (Cv * K * N) + (β / N) * Real.sqrt (M * K) + |c0| ≤
      β * Real.sqrt Cv * Real.sqrt K / r + β * Real.sqrt M * Real.sqrt K / r +
        β * Cms * Real.sqrt K * (2 / r) + β * Cg * A / r := by
    rw [e1, e2]
    linarith [e2', e3, e4, hc0b]
  calc _ ≤ _ := hmain
    _ = _ := hfin
    _ ≤ _ := sub_le_self _ hrest

end PhiFacts

end L48

end HRS

end
