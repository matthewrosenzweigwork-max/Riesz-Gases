import HRS.Main.EqBiasAux11

/-!
# EQ-BIAS, S9c: per-time variance of the pole sum
-/

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

namespace HRS

namespace Main

variable {d : ℕ} {s c : ℝ}

open HRS.External HRS.PoleCavityAux HRS.MarginalAux HRS.ProdTransfer HRS.CavResp

theorem eqbias_amgm {V₁ V₂ θ : ℝ} (hV₁ : 0 ≤ V₁) (hV₂ : 0 ≤ V₂) (hθ : 0 < θ) :
    2 * Real.sqrt (V₁ * V₂) ≤ θ * V₁ + V₂ / θ := by
  have h : Real.sqrt (V₁ * V₂) ≤ (θ * V₁ + V₂ / θ) / 2 := by
    rw [Real.sqrt_le_iff]
    refine ⟨by positivity, ?_⟩
    have : ((θ * V₁ + V₂ / θ) / 2) ^ 2 - V₁ * V₂ = ((θ * V₁ - V₂ / θ) / 2) ^ 2 := by
      field_simp
      ring
    nlinarith [sq_nonneg ((θ * V₁ - V₂ / θ) / 2)]
  linarith

theorem eqbias_alg {V V₁ V₂ a J₁ J₂ n K W εA θ : ℝ} (hn : 0 ≤ n) (hK : 0 ≤ K) (hεA : 0 ≤ εA)
    (hθ : 0 < θ) (hV₂0 : 0 ≤ V₂) (hV₂W : V₂ ≤ W) (hV₁0 : 0 ≤ V₁)
    (hmink : |V - V₁| ≤ V₂ + 2 * Real.sqrt (V₁ * V₂)) (h1 : |V₁ - n * a| ≤ n ^ 2 * K)
    (ha : |a - J₁| ≤ εA * J₁) (hJ₁ : 0 ≤ J₁) (hJ₂ : 0 ≤ J₂) :
    |V - n * (J₁ + J₂)| ≤ (1 + 1 / θ) * W + θ * (n * (1 + εA) * J₁ + n ^ 2 * K) +
      n ^ 2 * K + n * (εA * J₁) + n * J₂ := by
  have hs := eqbias_amgm hV₁0 hV₂0 hθ
  have hna : |n * a - n * J₁| ≤ n * (εA * J₁) := by
    rw [← mul_sub, abs_mul, abs_of_nonneg hn]
    exact mul_le_mul_of_nonneg_left ha hn
  have hV₁ : V₁ ≤ n * (1 + εA) * J₁ + n ^ 2 * K := by
    have h1' := (abs_le.1 h1).2
    have h2' := (abs_le.1 ha).2
    have : n * a ≤ n * (J₁ + εA * J₁) := mul_le_mul_of_nonneg_left (by linarith) hn
    nlinarith
  have hθV : θ * V₁ ≤ θ * (n * (1 + εA) * J₁ + n ^ 2 * K) :=
    mul_le_mul_of_nonneg_left hV₁ hθ.le
  have hVW : V₂ / θ ≤ W / θ := div_le_div_of_nonneg_right hV₂W hθ.le
  have hc : (1 + 1 / θ) * W = W + W / θ := by ring
  rw [hc]
  have a1 := abs_le.1 hmink
  have a2 := abs_le.1 h1
  have a3 := abs_le.1 hna
  rw [abs_le]
  constructor <;> nlinarith [mul_nonneg hn hJ₂]

/-- The complementary part `g_+ 1{g_+ ≤ H}`. -/
def eqbias_rest (d : ℕ) (s c : ℝ) (x : Torus d) (H : ℝ) (y : Torus d) : ℝ :=
  if H < gPlus d s c (x - y) then 0 else gPlus d s c (x - y)

theorem eqbias_rest_measurable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (x : Torus d) (H : ℝ) :
    Measurable (eqbias_rest d s c x H) := by
  have hgm := measurable_gPlus hd hs0 hsd c
  have hfm : Measurable fun y : Torus d => gPlus d s c (x - y) :=
    hgm.comp (measurable_const.sub measurable_id)
  exact Measurable.ite (measurableSet_lt measurable_const hfm) measurable_const hfm

theorem eqbias_rest_props (hc : ∀ z, 0 ≤ periodicRiesz d s z + c) (x : Torus d) (H : ℝ)
    (y : Torus d) :
    0 ≤ eqbias_rest d s c x H y ∧ eqbias_rest d s c x H y ≤ gPlus d s c (x - y) ∧
      (0 ≤ H → eqbias_rest d s c x H y ≤ H) ∧
      gPlus d s c (x - y) = eqbias_core d s c x H y + eqbias_rest d s c x H y ∧
      eqbias_core d s c x H y * eqbias_rest d s c x H y = 0 := by
  unfold eqbias_rest eqbias_core
  by_cases h : H < gPlus d s c (x - y)
  · simp only [h, if_true]
    refine ⟨le_rfl, hc _, ?_, by ring, by ring⟩
    exact fun hH => hH
  · simp only [h, ite_false]
    refine ⟨hc _, le_rfl, fun _ => not_lt.1 h, by ring, by ring⟩

theorem eqbias_sqint (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {ρ : Torus d → ℝ}
    (hρ : SmoothPosDensity ρ) {φ : Torus d → ℝ} (hφm : Measurable φ) (hφ0 : ∀ y, 0 ≤ φ y)
    (x : Torus d) (hφ : ∀ y, φ y ≤ gPlus d s c (x - y)) {u : ℝ} (hu : 0 < u) :
    Integrable (fun y => φ y ^ 2 * Real.exp (-u * gPlus d s c (x - y))) (withDensityReal ρ) := by
  have := isProbabilityMeasure_mu hρ
  have hgm := measurable_gPlus hd hs0 hsd c
  have hgxm : Measurable fun y : Torus d => gPlus d s c (x - y) :=
    hgm.comp (measurable_const.sub measurable_id)
  refine Integrable.mono' (integrable_const (2 / u ^ 2))
    ((hφm.pow_const 2).mul (Real.measurable_exp.comp (hgxm.const_mul _))).aestronglyMeasurable
    (Eventually.of_forall fun y => ?_)
  have h0 : 0 ≤ φ y ^ 2 * Real.exp (-u * gPlus d s c (x - y)) :=
    mul_nonneg (sq_nonneg _) (Real.exp_pos _).le
  rw [Real.norm_eq_abs, abs_of_nonneg h0]
  have hgy : 0 ≤ gPlus d s c (x - y) := (hφ0 y).trans (hφ y)
  calc φ y ^ 2 * Real.exp (-u * gPlus d s c (x - y))
      ≤ gPlus d s c (x - y) ^ 2 * Real.exp (-u * gPlus d s c (x - y)) :=
        mul_le_mul_of_nonneg_right (pow_le_pow_left₀ (hφ0 y) (hφ y) 2) (Real.exp_pos _).le
    _ = gPlus d s c (x - y) ^ 2 * Real.exp (-(u * gPlus d s c (x - y))) := by rw [neg_mul]
    _ ≤ 2 / u ^ 2 := eqbias_sqexp_bdd hu hgy

set_option maxHeartbeats 1600000 in
theorem eqbias_var_F (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (hc : ∀ z, 0 ≤ periodicRiesz d s z + c)
    (hc0 : 0 ≤ c) :
    ∃ Cψ Cv κ : ℝ, 0 ≤ Cψ ∧ 0 ≤ Cv ∧ 0 ≤ κ ∧
      ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ x : Torus d, ∀ t ∈ Set.Icc (0 : ℝ) 1, 0 < t →
      ∀ ε : ℝ, 0 ≤ ε →
      (∀ y' : Torus d,
        Integrable (fun Y => |cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) Y y'|)
          (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ∧
        ∫ Y, |cavityField d s c β ρ N (⟨0, by omega⟩ : Fin (N - 1)) Y y'|
          ∂(poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ≤ ε) →
      ∀ H : ℝ, 0 ≤ H → ∀ θ : ℝ, 0 < θ →
      MemLp (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i)) 2
          (poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t) ∧
      |Var[fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i);
            poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t] -
        ((N - 1 : ℕ) : ℝ) * ∫ y, gPlus d s c (x - y) ^ 2 *
          Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) ∂(withDensityReal ρ)| ≤
      (1 + 1 / θ) * (Cv * ((N - 1 : ℕ) : ℝ) * (Real.exp (β * c) *
          ∫ y, eqbias_rest d s c x H y ^ 2 ∂(withDensityReal ρ))) +
        θ * (((N - 1 : ℕ) : ℝ) * (1 + Cψ * (ε + 1 / (N : ℝ))) *
          (∫ y, gPlus d s c (x - y) ^ 2 * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))
            ∂(withDensityReal ρ)) +
          ((N - 1 : ℕ) : ℝ) ^ 2 * (κ * (∫ y, eqbias_core d s c x H y ∂(withDensityReal ρ)) ^ 2)) +
        ((N - 1 : ℕ) : ℝ) ^ 2 * (κ * (∫ y, eqbias_core d s c x H y ∂(withDensityReal ρ)) ^ 2) +
        ((N - 1 : ℕ) : ℝ) * (Cψ * (ε + 1 / (N : ℝ)) *
          ∫ y, gPlus d s c (x - y) ^ 2 * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))
            ∂(withDensityReal ρ)) +
        ((N - 1 : ℕ) : ℝ) * ∫ y, eqbias_rest d s c x H y ^ 2 ∂(withDensityReal ρ) := by
  haveI hμ := isProbabilityMeasure_mu hρ
  obtain ⟨Cψ, hCψ0, hdiag⟩ := eqbias_diag hd hs0 hsd hβ hρ hc
  obtain ⟨M, C₀, hM0, hC₀0, hmom⟩ := eqbias_core_moments hd hs0 hsd hβ hρ hc hc0
  obtain ⟨Cv, hCv0, hvar⟩ := PoleCavityAux.pole_variance_clause hd hs0 hsd β hβ ρ hρ
  refine ⟨Cψ, Cv, max (M ^ 2) C₀, hCψ0, hCv0.le, le_max_of_le_right hC₀0, ?_⟩
  intro N hN x t ht ht0 ε hε0 hε H hH0 θ hθ
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast (by omega : 1 ≤ N)
  have hn : 0 < N - 1 := by omega
  have hlam : 0 ≤ β / N := by positivity
  have hu : 0 < t * (β / N) := by positivity
  have hPprob := (isProbabilityMeasure_poleLaw hd hs0 hsd β hβ ρ hρ N hN x t ht).2
  set P := poleLaw (periodicRiesz d s) (withDensityReal ρ) (N - 1) (β / N) β x t with hP
  have hexch := MarginalAux.poleLaw_exchangeable hd hs0 hsd β hρ (N - 1) (β / N) hlam x t
  have hf1m := eqbias_core_measurable hd hs0 hsd (c := c) x H
  have hf2m := eqbias_rest_measurable hd hs0 hsd (c := c) x H
  have hprops := eqbias_rest_props (s := s) (c := c) hc x H
  have hf10 := fun y => (eqbias_core_le hc x H y).1
  have hf1g := fun y => (eqbias_core_le hc x H y).2
  have hf20 := fun y => (hprops y).1
  have hf2g := fun y => (hprops y).2.1
  have hsplit := fun y => (hprops y).2.2.2.1
  have hprod0 := fun y => (hprops y).2.2.2.2
  -- notation
  set n : ℝ := ((N - 1 : ℕ) : ℝ) with hndef
  have hn0 : 0 ≤ n := Nat.cast_nonneg _
  set m := ∫ y, eqbias_core d s c x H y ∂(withDensityReal ρ) with hmdef
  have hm0 : 0 ≤ m := integral_nonneg hf10
  set T := ∫ y, eqbias_rest d s c x H y ^ 2 ∂(withDensityReal ρ) with hTdef
  have hT0 : 0 ≤ T := integral_nonneg fun y => sq_nonneg _
  set εA := Cψ * (ε + 1 / (N : ℝ)) with hεA
  have hεA0 : 0 ≤ εA := by positivity
  set g : Torus d → ℝ := fun y => gPlus d s c (x - y) with hg
  have hE0 : ∀ y, 0 ≤ Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) := fun y => (Real.exp_pos _).le
  have hE1 : ∀ y, Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) ≤ 1 := fun y => by
    have hg0 : 0 ≤ gPlus d s c (x - y) := hc _
    exact Real.exp_le_one_iff.2 (by nlinarith [mul_nonneg hu.le hg0])
  -- the integrals
  have hi1 := eqbias_sqint hd hs0 hsd hρ (c := c) (hf1m) hf10 x hf1g hu
  have hi2 := eqbias_sqint hd hs0 hsd hρ (c := c) (hf2m) hf20 x hf2g hu
  set J₁ := ∫ y, eqbias_core d s c x H y ^ 2 * Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) ∂(withDensityReal ρ) with hJ₁
  set J₂ := ∫ y, eqbias_rest d s c x H y ^ 2 * Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) ∂(withDensityReal ρ) with hJ₂
  set J := ∫ y, gPlus d s c (x - y) ^ 2 * Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) ∂(withDensityReal ρ) with hJ
  have hJ₁0 : 0 ≤ J₁ := integral_nonneg fun y => mul_nonneg (sq_nonneg _) (hE0 y)
  have hJ₂0 : 0 ≤ J₂ := integral_nonneg fun y => mul_nonneg (sq_nonneg _) (hE0 y)
  have hJsum : J = J₁ + J₂ := by
    rw [hJ₁, hJ₂, ← integral_add hi1 hi2]
    refine integral_congr_ae (Eventually.of_forall fun y => ?_)
    simp only
    have := hsplit y
    have h0 := hprod0 y
    calc gPlus d s c (x - y) ^ 2 * Real.exp (-(t * (β / N)) * gPlus d s c (x - y))
        = (eqbias_core d s c x H y + eqbias_rest d s c x H y) ^ 2 * Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) := by rw [← this]
      _ = eqbias_core d s c x H y ^ 2 * Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) +
          eqbias_rest d s c x H y ^ 2 * Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) +
          2 * (eqbias_core d s c x H y * eqbias_rest d s c x H y) *
            Real.exp (-(t * (β / N)) * gPlus d s c (x - y)) := by ring
      _ = _ := by rw [h0]; ring
  have hT_int : Integrable (fun y => eqbias_rest d s c x H y ^ 2) (withDensityReal ρ) := by
    refine Integrable.mono' (integrable_const (H ^ 2)) (hf2m.pow_const 2).aestronglyMeasurable
      (Eventually.of_forall fun y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (sq_nonneg _)]
    exact pow_le_pow_left₀ (hf20 y) ((hprops y).2.2.1 hH0) 2
  have hJ₂T : J₂ ≤ T := by
    rw [hJ₂, hTdef]
    refine integral_mono_of_nonneg (Eventually.of_forall fun y => mul_nonneg (sq_nonneg _) (hE0 y)) hT_int
      (Eventually.of_forall fun y => ?_)
    simpa using mul_le_mul_of_nonneg_left (hE1 y) (sq_nonneg (eqbias_rest d s c x H y))
  have hJ₁J : J₁ ≤ J := by linarith
  -- diag
  obtain ⟨hh2, hdg⟩ := hdiag N hN x t ht ht0 ε hε0 hε H
  -- moments
  obtain ⟨hone, hpair⟩ := hmom N hN x t ht H
  have hκ1 : (M * m) ^ 2 ≤ max (M ^ 2) C₀ * m ^ 2 := by
    rw [mul_pow]; exact mul_le_mul_of_nonneg_right (le_max_left _ _) (sq_nonneg _)
  have hκ2 : C₀ * m ^ 2 ≤ max (M ^ 2) C₀ * m ^ 2 :=
    mul_le_mul_of_nonneg_right (le_max_right _ _) (sq_nonneg _)
  obtain ⟨hF1, hV1⟩ := eqbias_var_sum hn hexch hf1m hf10 hh2 (Cone := M * m) (Cpair := C₀ * m ^ 2)
    (by positivity) (by positivity) (fun i => hone i) (fun i j hij => hpair i j hij)
  have hV1' : |Var[fun Y : Config d (N - 1) => ∑ i, eqbias_core d s c x H (Y i); P] -
      n * ∫ Y, eqbias_core d s c x H (Y ⟨0, hn⟩) ^ 2 ∂P| ≤ n ^ 2 * (max (M ^ 2) C₀ * m ^ 2) :=
    hV1.trans (mul_le_mul_of_nonneg_left (max_le hκ1 hκ2) (sq_nonneg _))
  -- F₂
  have hF2m : MemLp (fun Y : Config d (N - 1) => ∑ i, eqbias_rest d s c x H (Y i)) 2 P := by
    refine MemLp.of_bound (Finset.measurable_sum _ fun i _ =>
      hf2m.comp (measurable_pi_apply i)).aestronglyMeasurable (n * H)
      (Eventually.of_forall fun Y => ?_)
    rw [Real.norm_eq_abs, abs_of_nonneg (Finset.sum_nonneg fun i _ => hf20 _)]
    calc ∑ i, eqbias_rest d s c x H (Y i) ≤ ∑ _i : Fin (N - 1), H :=
          Finset.sum_le_sum fun i _ => (hprops _).2.2.1 hH0
      _ = n * H := by simp [hndef]
  have hV2 : Var[fun Y : Config d (N - 1) => ∑ i, eqbias_rest d s c x H (Y i); P] ≤
      Cv * n * (Real.exp (β * c) * T) := by
    have hev := hvar N hN x t ht (eqbias_rest d s c x H) hf2m
    have hlin : ∫⁻ y, ‖eqbias_rest d s c x H y‖ₑ ^ 2 ∂(withDensityReal ρ) = ENNReal.ofReal T := by
      have : ∀ y, ‖eqbias_rest d s c x H y‖ₑ ^ 2 = ENNReal.ofReal (eqbias_rest d s c x H y ^ 2) :=
        fun y => by rw [Real.enorm_eq_ofReal (hf20 y), ← ENNReal.ofReal_pow (hf20 y)]
      simp_rw [this]
      exact (ofReal_integral_eq_lintegral_ofReal hT_int
        (Eventually.of_forall fun y => sq_nonneg _)).symm
    have hexp : ∀ y, ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y))) ≤
        ENNReal.ofReal (Real.exp (β * c)) := fun y =>
      ENNReal.ofReal_le_ofReal (eqbias_exp_le hβ hc0 hN0 hN1 ht.1 ht.2
        (by have := hc (x - y); linarith))
    have h3 : ∫⁻ y, ‖eqbias_rest d s c x H y‖ₑ ^ 2 *
        ENNReal.ofReal (Real.exp (-(t * (β / N)) * periodicRiesz d s (x - y))) ∂(withDensityReal ρ) ≤
        ENNReal.ofReal T * ENNReal.ofReal (Real.exp (β * c)) := by
      calc _ ≤ ∫⁻ y, ‖eqbias_rest d s c x H y‖ₑ ^ 2 * ENNReal.ofReal (Real.exp (β * c))
            ∂(withDensityReal ρ) := lintegral_mono fun y => mul_le_mul' le_rfl (hexp y)
        _ = _ := by rw [lintegral_mul_const _ (by
              exact (hf2m.enorm.pow_const 2)), hlin]
    have h4 := hev.trans (mul_le_mul' le_rfl h3)
    have h5 : ENNReal.ofReal (Cv * ((N - 1 : ℕ) : ℝ)) *
        (ENNReal.ofReal T * ENNReal.ofReal (Real.exp (β * c))) =
        ENNReal.ofReal (Cv * n * (Real.exp (β * c) * T)) := by
      rw [← ENNReal.ofReal_mul hT0, ← ENNReal.ofReal_mul (by positivity)]
      congr 1; ring
    rw [h5] at h4
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h4
    rw [ENNReal.toReal_ofReal (by positivity)] at this
    exact this
  have hFeq : (fun Y : Config d (N - 1) => ∑ i, gPlus d s c (x - Y i)) =
      fun Y => (∑ i, eqbias_core d s c x H (Y i)) + ∑ i, eqbias_rest d s c x H (Y i) := by
    funext Y
    rw [← Finset.sum_add_distrib]
    exact Finset.sum_congr rfl fun i _ => hsplit _
  have hmink := eqbias_var_mink hF1 hF2m
  rw [hFeq]
  refine ⟨hF1.add hF2m, ?_⟩
  have key := eqbias_alg (V := Var[fun Y : Config d (N - 1) =>
      (∑ i, eqbias_core d s c x H (Y i)) + ∑ i, eqbias_rest d s c x H (Y i); P])
    (V₁ := Var[fun Y : Config d (N - 1) => ∑ i, eqbias_core d s c x H (Y i); P])
    (V₂ := Var[fun Y : Config d (N - 1) => ∑ i, eqbias_rest d s c x H (Y i); P])
    (a := ∫ Y, eqbias_core d s c x H (Y ⟨0, hn⟩) ^ 2 ∂P) (J₁ := J₁) (J₂ := J₂) (n := n)
    (K := max (M ^ 2) C₀ * m ^ 2) (W := Cv * n * (Real.exp (β * c) * T)) (εA := εA) (θ := θ)
    hn0 (by positivity) hεA0 hθ (variance_nonneg _ _) hV2 (variance_nonneg _ _) hmink hV1' hdg hJ₁0 hJ₂0
  rw [hJsum]
  have e1 : θ * (n * (1 + εA) * J₁ + n ^ 2 * (max (M ^ 2) C₀ * m ^ 2)) ≤
      θ * (n * (1 + εA) * (J₁ + J₂) + n ^ 2 * (max (M ^ 2) C₀ * m ^ 2)) := by
    gcongr; linarith
  have e2 : n * (εA * J₁) ≤ n * (εA * (J₁ + J₂)) := by gcongr; linarith
  have e3 : n * J₂ ≤ n * T := by gcongr
  linarith [key, e1, e2, e3]


end Main

end HRS

end
