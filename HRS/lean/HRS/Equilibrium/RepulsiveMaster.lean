/-
# HRS.Equilibrium.RepulsiveMaster — package REP-06: the master cutoff data

Assembly of `DGRHS.Concentration.MasterCutoffData μ N (exponent d β N μ) u₀` for the periodic
logarithm, following `DGRHS.Gaussian.gaussianLogSourceMasterData` (Euclidean, not vendored):

* the adaptive near-field scale `α_u = adaptiveScale δ A β N u d` (restated from
  `DGRHS.Gaussian.gaussianLogAdaptiveScale`), with the arithmetic
  `β N nearConst d Λ α_u^d ≤ u/8` for `A ≥ 8 nearConst d Λ` and
  `log(δ/α_u) ≤ max 0 ((1/d) log(A(1+βN)δ^d))` for `u ≥ 1`;
* the comparison (M1): off the collision set
  `exponent ≤ β iidNeg((heatPos α²)~) + ½ iidNeg(q_u) + β iidNeg((heatTail δ²)~) + β Ch + β|E|/2
           ≤ u/8 + ½ iidNeg(q_u) + lowConst d β δ Ch E`,
  so `u ≤ exponent ⇒ u ≤ iidNeg(q_u)` once `4 lowConst ≤ u₀ ≤ u`;
* the cap (M2) and the norm fields (M3) from REP-04 and REP-05;
* the size bound `masterCutoffSize ≤ K N^{2/3}` (in fact `O(log² N)`), the analogue of
  `DGRHS.Gaussian.gaussianLogAdaptive_actual_size_bound`.

`sorry`-ed specifications; see `docs/REPULSIVE_PLAN.md` (REP-06).
-/
import HRS.Equilibrium.RepulsiveNear
import HRS.Equilibrium.RepulsivePositive
import HRS.Equilibrium.RepulsiveL2

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace Repulsive

variable {d : ℕ}

/-! ### Arithmetic of the adaptive scale (restated `DGRHS.Gaussian.gaussianLogAdaptiveScale_*`) -/

theorem adaptiveScale_pos {δ A β n u dr : ℝ} (hδ : 0 < δ) (hA : 0 < A) (hβ : 0 ≤ β) (hn : 0 ≤ n)
    (hu : 0 < u) (hdr : 0 < dr) : 0 < adaptiveScale δ A β n u dr := by
  have hK : 0 < A * (1 + β * n) := mul_pos hA (by have := mul_nonneg hβ hn; linarith)
  unfold adaptiveScale
  exact lt_min hδ (Real.rpow_pos_of_pos (div_pos hu hK) _)

theorem adaptiveScale_le {δ A β n u dr : ℝ} : adaptiveScale δ A β n u dr ≤ δ := by
  unfold adaptiveScale
  exact min_le_left _ _

/-- `α_u^d ≤ u / (A (1 + β n))`. -/
theorem adaptiveScale_rpow_le {δ A β n u dr : ℝ} (hδ : 0 < δ) (hA : 0 < A) (hβ : 0 ≤ β) (hn : 0 ≤ n)
    (hu : 0 < u) (hdr : 0 < dr) :
    adaptiveScale δ A β n u dr ^ dr ≤ u / (A * (1 + β * n)) := by
  have hK : 0 < A * (1 + β * n) := mul_pos hA (by have := mul_nonneg hβ hn; linarith)
  have hpos := adaptiveScale_pos hδ hA hβ hn hu hdr
  have hle : adaptiveScale δ A β n u dr ≤ (u / (A * (1 + β * n))) ^ (1 / dr) := by
    unfold adaptiveScale
    exact min_le_right _ _
  calc adaptiveScale δ A β n u dr ^ dr ≤ ((u / (A * (1 + β * n))) ^ (1 / dr)) ^ dr :=
        Real.rpow_le_rpow hpos.le hle hdr.le
    _ = u / (A * (1 + β * n)) := by
        rw [← Real.rpow_mul (div_pos hu hK).le, one_div, inv_mul_cancel₀ hdr.ne', Real.rpow_one]

/-- Near-field error: `β n C α_u^d ≤ u/8` when `8 C ≤ A`, `C ≥ 0`. -/
theorem adaptiveScale_near_error_le {δ A β n u dr C : ℝ} (hδ : 0 < δ) (hA : 0 < A) (hβ : 0 ≤ β)
    (hn : 0 ≤ n) (hu : 0 < u) (hdr : 0 < dr) (hC : 0 ≤ C) (hCA : 8 * C ≤ A) :
    β * n * (C * adaptiveScale δ A β n u dr ^ dr) ≤ u / 8 := by
  have hK : 0 < A * (1 + β * n) := mul_pos hA (by have := mul_nonneg hβ hn; linarith)
  have hP0 : 0 ≤ adaptiveScale δ A β n u dr ^ dr :=
    Real.rpow_nonneg (adaptiveScale_pos hδ hA hβ hn hu hdr).le _
  have hPK : adaptiveScale δ A β n u dr ^ dr * (A * (1 + β * n)) ≤ u :=
    (le_div_iff₀ hK).1 (adaptiveScale_rpow_le hδ hA hβ hn hu hdr)
  have hx : 0 ≤ β * n := mul_nonneg hβ hn
  have h1 : 8 * C * adaptiveScale δ A β n u dr ^ dr ≤ A * adaptiveScale δ A β n u dr ^ dr :=
    mul_le_mul_of_nonneg_right hCA hP0
  have h2 := mul_le_mul_of_nonneg_left h1 hx
  have h3 : 0 ≤ A * adaptiveScale δ A β n u dr ^ dr := mul_nonneg hA.le hP0
  nlinarith [h2, h3, hPK]

/-- Logarithmic mass of the band: `log(δ/α_u) ≤ max 0 ((1/d) log(A (1 + β n) δ^d))` for `u ≥ 1`. -/
theorem log_div_adaptiveScale_le {δ A β n u dr : ℝ} (hδ : 0 < δ) (hA : 0 < A) (hβ : 0 ≤ β)
    (hn : 0 ≤ n) (hu : 1 ≤ u) (hdr : 0 < dr) :
    Real.log (δ / adaptiveScale δ A β n u dr) ≤
      max 0 ((1 / dr) * Real.log (A * (1 + β * n) * δ ^ dr)) := by
  have hK : 0 < A * (1 + β * n) := mul_pos hA (by have := mul_nonneg hβ hn; linarith)
  have hu0 : 0 < u := by linarith
  have hlogu : 0 ≤ Real.log u := Real.log_nonneg hu
  have hL : 0 ≤ 1 / dr := (one_div_pos.2 hdr).le
  have hpos := adaptiveScale_pos hδ hA hβ hn hu0 hdr
  have hdef : adaptiveScale δ A β n u dr = min δ ((u / (A * (1 + β * n))) ^ (1 / dr)) := rfl
  rw [hdef] at hpos ⊢
  rcases le_total δ ((u / (A * (1 + β * n))) ^ (1 / dr)) with h | h
  · rw [min_eq_left h, div_self hδ.ne', Real.log_one]
    exact le_max_left _ _
  · rw [min_eq_right h] at hpos ⊢
    have hlogt : Real.log ((u / (A * (1 + β * n))) ^ (1 / dr))
        = (1 / dr) * (Real.log u - Real.log (A * (1 + β * n))) := by
      rw [Real.log_rpow (div_pos hu0 hK), Real.log_div hu0.ne' hK.ne']
    have hKd : (1 / dr) * Real.log (A * (1 + β * n) * δ ^ dr)
        = Real.log δ + (1 / dr) * Real.log (A * (1 + β * n)) := by
      rw [Real.log_mul hK.ne' (Real.rpow_pos_of_pos hδ dr).ne', Real.log_rpow hδ, mul_add,
        ← mul_assoc, one_div_mul_cancel hdr.ne', one_mul, add_comm]
    rw [Real.log_div hδ.ne' hpos.ne', hlogt]
    refine le_max_of_le_right ?_
    rw [hKd]
    nlinarith [mul_nonneg hL hlogu]

theorem log_div_adaptiveScale_nonneg {δ A β n u dr : ℝ} (hδ : 0 < δ) (hA : 0 < A) (hβ : 0 ≤ β)
    (hn : 0 ≤ n) (hu : 0 < u) (hdr : 0 < dr) :
    0 ≤ Real.log (δ / adaptiveScale δ A β n u dr) := by
  have hpos := adaptiveScale_pos hδ hA hβ hn hu hdr
  apply Real.log_nonneg
  rw [one_le_div hpos]
  exact adaptiveScale_le

/-- Sublinear growth of `(c₀ + c₁ log(1 + b n))²`: bounded by `K n^{2/3}` for `n ≥ 1`
(`log(1 + b n) ≤ log(1 + b) + log n` and `log n ≤ 3 n^{1/3}`). -/
theorem log_sq_le_rpow (c₀ c₁ b : ℝ) (hc₀ : 0 ≤ c₀) (hc₁ : 0 ≤ c₁) (hb : 0 ≤ b) :
    ∃ K : ℝ, ∀ n : ℕ, 1 ≤ n →
      (c₀ + c₁ * Real.log (1 + b * n)) ^ 2 ≤ K * (n : ℝ) ^ ((2 : ℝ) / 3) := by
  have hL0 : 0 ≤ Real.log (1 + b) := Real.log_nonneg (by linarith)
  have hM0 : 0 ≤ c₀ + c₁ * Real.log (1 + b) + 3 * c₁ := by
    have := mul_nonneg hc₁ hL0; linarith
  refine ⟨(c₀ + c₁ * Real.log (1 + b) + 3 * c₁) ^ 2, fun n hn => ?_⟩
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast hn
  have hn0 : (0 : ℝ) ≤ n := by linarith
  obtain ⟨s, hs⟩ : ∃ s : ℝ, s = (n : ℝ) ^ ((1 : ℝ) / 3) := ⟨_, rfl⟩
  have hs1 : 1 ≤ s := by rw [hs]; exact Real.one_le_rpow hn1 (by norm_num)
  have hs2 : s ^ 2 = (n : ℝ) ^ ((2 : ℝ) / 3) := by
    rw [hs, ← Real.rpow_natCast, ← Real.rpow_mul hn0]; norm_num
  have hlogn : Real.log (n : ℝ) ≤ 3 * s := by
    have h := Real.log_le_rpow_div hn0 (by norm_num : (0 : ℝ) < 1 / 3)
    have h3 : (n : ℝ) ^ ((1 : ℝ) / 3) / (1 / 3) = 3 * (n : ℝ) ^ ((1 : ℝ) / 3) := by ring
    rw [hs]; linarith
  have hb1 : (0 : ℝ) < 1 + b := by linarith
  have hlogmono : Real.log (1 + b * n) ≤ Real.log (1 + b) + Real.log n := by
    rw [← Real.log_mul hb1.ne' (by linarith : (0 : ℝ) < n).ne']
    exact Real.log_le_log (by have := mul_nonneg hb hn0; linarith) (by nlinarith)
  have hlog1 : 0 ≤ Real.log (1 + b * n) :=
    Real.log_nonneg (by have := mul_nonneg hb hn0; linarith)
  have hx0 : 0 ≤ c₀ + c₁ * Real.log (1 + b * n) := by
    have := mul_nonneg hc₁ hlog1; linarith
  have hxM : c₀ + c₁ * Real.log (1 + b * n) ≤ (c₀ + c₁ * Real.log (1 + b) + 3 * c₁) * s := by
    have h1 : c₁ * Real.log (1 + b * n) ≤ c₁ * (Real.log (1 + b) + 3 * s) :=
      mul_le_mul_of_nonneg_left (by linarith) hc₁
    have h2 : 0 ≤ (c₀ + c₁ * Real.log (1 + b)) * (s - 1) :=
      mul_nonneg (by have := mul_nonneg hc₁ hL0; linarith) (by linarith)
    nlinarith
  have hsq : (c₀ + c₁ * Real.log (1 + b * n)) ^ 2
      ≤ ((c₀ + c₁ * Real.log (1 + b) + 3 * c₁) * s) ^ 2 :=
    pow_le_pow_left₀ hx0 hxM 2
  rw [← hs2]
  nlinarith [hsq]

/-! ### Choice of the band scale -/

variable {ρ : Torus d → ℝ} {Λ : ℝ} {μ : Measure (Torus d)}

/-- Existence of `δ ∈ (0, 1/2]` with the norm-field smallness required by `MasterCutoffData`
(`bandRowControl d Λ δ = Λ l2Const d δ^d → 0`). -/
theorem exists_master_scale (hd : 2 ≤ d) (hΛ0 : 0 ≤ Λ) {β : ℝ} (hβ : 0 ≤ β) {L : ℝ} (hL : 0 < L) :
    ∃ δ : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧
      64 * β ^ 2 * bandRowControl d Λ δ ≤ 1 / L ∧
      8 * β * Real.sqrt (bandRowControl d Λ δ) ≤ 1 / L := by
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hl2 : 0 ≤ l2Const d := by
    unfold l2Const
    exact mul_nonneg (mul_nonneg (mul_nonneg (sq_nonneg _) (sq_nonneg _))
      (Real.rpow_nonneg (by positivity) _)) (thetaConst_pos d).le
  have hLL : 0 < L + L ^ 2 := by nlinarith [sq_nonneg L]
  obtain ⟨K, hKdef⟩ : ∃ K : ℝ, K = Λ * l2Const d := ⟨_, rfl⟩
  have hK0 : 0 ≤ K := by rw [hKdef]; exact mul_nonneg hΛ0 hl2
  obtain ⟨T, hTdef⟩ : ∃ T : ℝ, T = 1 / (64 * (β ^ 2 + 1) * (L + L ^ 2)) := ⟨_, rfl⟩
  have hT0 : 0 < T := by
    rw [hTdef]; exact one_div_pos.mpr (mul_pos (by positivity) hLL)
  have hT' : T * (64 * (β ^ 2 + 1) * (L + L ^ 2)) = 1 := by
    rw [hTdef]; field_simp
  obtain ⟨t, htdef⟩ : ∃ t : ℝ, t = T / (K + 1) := ⟨_, rfl⟩
  have ht0 : 0 < t := by rw [htdef]; exact div_pos hT0 (by linarith)
  obtain ⟨δ, hδdef⟩ : ∃ δ : ℝ, δ = min (1 / 2) (t ^ (1 / (d : ℝ))) := ⟨_, rfl⟩
  have hδpos : 0 < δ := by
    rw [hδdef]; exact lt_min (by norm_num) (Real.rpow_pos_of_pos ht0 _)
  have hδ2 : δ ≤ 1 / 2 := by rw [hδdef]; exact min_le_left _ _
  have hδt : δ ^ (d : ℝ) ≤ t := by
    have h1 : δ ≤ t ^ (1 / (d : ℝ)) := by rw [hδdef]; exact min_le_right _ _
    calc δ ^ (d : ℝ) ≤ (t ^ (1 / (d : ℝ))) ^ (d : ℝ) :=
          Real.rpow_le_rpow hδpos.le h1 hd0.le
      _ = t := by
          rw [← Real.rpow_mul ht0.le, one_div, inv_mul_cancel₀ hd0.ne', Real.rpow_one]
  have hpow : (δ ^ 2) ^ ((d : ℝ) / 2) = δ ^ (d : ℝ) := by
    rw [← Real.rpow_natCast, ← Real.rpow_mul hδpos.le]
    congr 1
    push_cast
    ring
  have hR : bandRowControl d Λ δ = K * δ ^ (d : ℝ) := by
    unfold bandRowControl
    rw [hpow, hKdef]
  have hR0 : 0 ≤ bandRowControl d Λ δ := by
    rw [hR]; exact mul_nonneg hK0 (Real.rpow_nonneg hδpos.le _)
  have hRT : bandRowControl d Λ δ ≤ T := by
    rw [hR]
    calc K * δ ^ (d : ℝ) ≤ K * t := mul_le_mul_of_nonneg_left hδt hK0
      _ = K * (T / (K + 1)) := by rw [htdef]
      _ ≤ T := by
        rw [mul_div_assoc', div_le_iff₀ (by linarith)]
        nlinarith
  have hQ0 : 0 ≤ 64 * β ^ 2 * T := mul_nonneg (by positivity) hT0.le
  have hQ1 : 64 * β ^ 2 * T * (L + L ^ 2) ≤ 1 := by
    nlinarith [hT', sq_nonneg β, mul_nonneg hT0.le hLL.le]
  have hQL : 64 * β ^ 2 * T * L ≤ 1 := by
    nlinarith [mul_nonneg hQ0 hL.le, mul_nonneg hQ0 (sq_nonneg L)]
  have hR_le : 64 * β ^ 2 * bandRowControl d Λ δ ≤ 64 * β ^ 2 * T :=
    mul_le_mul_of_nonneg_left hRT (by positivity)
  refine ⟨δ, hδpos, hδ2, ?_, ?_⟩
  · rw [le_div_iff₀ hL]
    nlinarith [mul_le_mul_of_nonneg_right hR_le hL.le]
  · rw [le_div_iff₀ hL]
    have hs := Real.sq_sqrt hR0
    have hsq0 : 0 ≤ Real.sqrt (bandRowControl d Λ δ) := Real.sqrt_nonneg _
    have hx0 : 0 ≤ 8 * β * Real.sqrt (bandRowControl d Λ δ) * L := by
      have := mul_nonneg (mul_nonneg (by norm_num : (0 : ℝ) ≤ 8) hβ) hsq0
      exact mul_nonneg this hL.le
    have h1 : (8 * β * Real.sqrt (bandRowControl d Λ δ) * L) ^ 2 ≤ 1 := by
      have e : (8 * β * Real.sqrt (bandRowControl d Λ δ) * L) ^ 2
          = 64 * β ^ 2 * bandRowControl d Λ δ * L ^ 2 := by
        rw [mul_pow, mul_pow, mul_pow, hs]; ring
      rw [e]
      nlinarith [mul_le_mul_of_nonneg_right hR_le (sq_nonneg L), mul_nonneg hQ0 hL.le, hQ1]
    nlinarith [h1, hx0]

/-! ### The comparison (M1) -/

/-- Mellin integrals of a fixed `x` over a subset of `(c, ∞)` are dominated by the integral of the
integrand at the origin (`|Ψ(x,t)| ≤ Ψ(0,t)`). -/
theorem psi_setIntegral_norm_le (hd : 2 ≤ d) {c : ℝ} (hc : 0 < c) {S : Set ℝ}
    (hS : MeasurableSet S) (hSc : S ⊆ Ioi c) (x : Torus d) :
    ‖∫ t in S, heatWeight d t * psiFn x t‖ ≤
      ∫ t in Ioi c, heatWeight d t * psiFn (0 : Torus d) t := by
  have hI0 : IntegrableOn (fun t => heatWeight d t * psiFn (0 : Torus d) t) (Ioi c) :=
    integrableOn_heatWeight_psiFn_Ioi hd 0 hc
  have hIS : IntegrableOn (fun t => heatWeight d t * psiFn (0 : Torus d) t) S :=
    hI0.mono_set hSc
  refine (norm_integral_le_of_norm_le hIS ?_).trans ?_
  · refine ae_restrict_of_forall_mem hS fun t ht => ?_
    have htc : 0 < t := lt_trans hc (show c < t from hSc ht)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (heatWeight_nonneg (d := d) t htc.le)]
    exact mul_le_mul_of_nonneg_left (abs_psiFn_le_psiFn_zero x htc)
      (heatWeight_nonneg (d := d) t htc.le)
  · refine setIntegral_mono_set hI0 ?_ (ae_of_all _ fun t ht => hSc ht)
    refine ae_restrict_of_forall_mem measurableSet_Ioi fun t ht => ?_
    have h1 : c < t := ht
    exact mul_nonneg (heatWeight_nonneg (d := d) t (hc.trans h1).le)
      (psiFn_zero_nonneg (d := d) (hc.trans h1))

/-- `|heatBand d a b x| ≤ subA d 0 · ∫_{(a,∞)} t^{d/2-1} Ψ(0,t) dt` for every `b` (no `b ≤ 1`). -/
theorem band_abs_le_const (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (x : Torus d) :
    |heatBand d a b x| ≤
      KernelAux.subA d 0 * ∫ t in Ioi a, heatWeight d t * psiFn (0 : Torus d) t := by
  unfold heatBand
  rw [abs_mul, abs_of_nonneg (subA_zero_pos hd).le]
  refine mul_le_mul_of_nonneg_left ?_ (subA_zero_pos hd).le
  have h := psi_setIntegral_norm_le (S := Ioc a b) hd ha measurableSet_Ioc Ioc_subset_Ioi_self x
  rwa [Real.norm_eq_abs] at h

/-- `|heatTail d b x| ≤ subA d 0 · ∫_{(b,∞)} t^{d/2-1} Ψ(0,t) dt`. -/
theorem tail_abs_le_const (hd : 2 ≤ d) {b : ℝ} (hb : 0 < b) (x : Torus d) :
    |heatTail d b x| ≤
      KernelAux.subA d 0 * ∫ t in Ioi b, heatWeight d t * psiFn (0 : Torus d) t := by
  unfold heatTail
  rw [abs_mul, abs_of_nonneg (subA_zero_pos hd).le]
  refine mul_le_mul_of_nonneg_left ?_ (subA_zero_pos hd).le
  have h := psi_setIntegral_norm_le hd hb measurableSet_Ioi subset_rfl x
  rwa [Real.norm_eq_abs] at h

/-- A bounded measurable function has bounded, hence integrable, translates for a probability `μ`. -/
theorem intg_translate_of_abs_le {f : Torus d → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ z, |f z| ≤ M) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (x : Torus d) :
    Integrable (fun y => f (x - y)) μ :=
  Integrable.of_bound (hf.comp (measurable_const.sub measurable_id)).aestronglyMeasurable M
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM _)

/-- The convolution of a bounded measurable function against a probability `μ` is integrable. -/
theorem intg_convMeasure_of_abs_le {f : Torus d → ℝ} (hf : Measurable f) {M : ℝ}
    (hM : ∀ z, |f z| ≤ M) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    Integrable (convMeasure f μ) μ := by
  refine Integrable.of_bound (PoleCavityAux.measurable_convMeasure hf μ).aestronglyMeasurable M
    (ae_of_all _ fun x => ?_)
  have h := norm_integral_le_of_norm_le_const (μ := μ) (f := fun y => f (x - y)) (C := M)
    (ae_of_all _ fun y => by rw [Real.norm_eq_abs]; exact hM _)
  rw [probReal_univ, mul_one] at h
  exact h

/-- Integrability of a sum of two convolutions. -/
theorem intg_convMeasure_add {μ : Measure (Torus d)} [IsProbabilityMeasure μ] {f₁ f₂ : Torus d → ℝ}
    (h₁c : Integrable (convMeasure f₁ μ) μ) (h₂c : Integrable (convMeasure f₂ μ) μ)
    (h₁ : ∀ x, Integrable (fun y => f₁ (x - y)) μ) (h₂ : ∀ x, Integrable (fun y => f₂ (x - y)) μ) :
    Integrable (convMeasure (fun z => f₁ z + f₂ z) μ) μ := by
  have hC : convMeasure (fun z => f₁ z + f₂ z) μ =
      fun z => convMeasure f₁ μ z + convMeasure f₂ μ z := by
    funext z
    unfold convMeasure
    exact integral_add (h₁ z) (h₂ z)
  rw [hC]
  exact h₁c.add h₂c

/-- Decomposition of the centred logarithm off the diagonal (`0 < a ≤ b`):
`g̃ = (heatPos a)~ + (heatBand a b)~ + (heatTail b)~` (the constant `heatPosMass` is killed by
centering; `heatBand d 0 a` and `heatPos d a` agree off the origin). -/
theorem pairKernel_decomp (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) [IsProbabilityMeasure μ] {a b : ℝ} (ha : 0 < a) (hab : a ≤ b)
    (x y : Torus d) (hxy : x ≠ y) :
    pairKernel (periodicRiesz d 0) μ (x, y) =
      pairKernel (heatPos d a) μ (x, y) + pairKernel (heatBand d a b) μ (x, y) +
        pairKernel (heatTail d b) μ (x, y) := by
  have hb : 0 < b := ha.trans_le hab
  have hPi : ∀ x, Integrable (fun y => heatPos d a (x - y)) μ :=
    fun x => integrable_heatPos_shift hd hμ hρ hΛ ha x
  have hPc : Integrable (convMeasure (heatPos d a) μ) μ :=
    integrable_convMeasure_heatPos hd hμ hρ hΛ ha
  have hBi : ∀ x, Integrable (fun y => heatBand d a b (x - y)) μ :=
    fun x => intg_translate_of_abs_le (measurable_heatBand hd a b)
      (fun z => band_abs_le_const hd ha z) μ x
  have hBc : Integrable (convMeasure (heatBand d a b) μ) μ :=
    intg_convMeasure_of_abs_le (measurable_heatBand hd a b)
      (fun z => band_abs_le_const hd ha z) μ
  have hTi : ∀ x, Integrable (fun y => heatTail d b (x - y)) μ :=
    fun x => intg_translate_of_abs_le (continuous_heatTail hd hb).measurable
      (fun z => tail_abs_le_const hd hb z) μ x
  have hTc : Integrable (convMeasure (heatTail d b) μ) μ :=
    intg_convMeasure_of_abs_le (continuous_heatTail hd hb).measurable
      (fun z => tail_abs_le_const hd hb z) μ
  have hAi : ∀ x, Integrable (fun y => heatPos d a (x - y) + heatBand d a b (x - y)) μ :=
    fun x => (hPi x).add (hBi x)
  have hAc : Integrable (convMeasure (fun z => heatPos d a z + heatBand d a b z) μ) μ :=
    intg_convMeasure_add hPc hBc hPi hBi
  have hBi' : ∀ x, Integrable
      (fun y => heatPos d a (x - y) + heatBand d a b (x - y) + heatTail d b (x - y)) μ :=
    fun x => (hAi x).add (hTi x)
  have hBc' : Integrable
      (convMeasure (fun z => heatPos d a z + heatBand d a b z + heatTail d b z) μ) μ :=
    intg_convMeasure_add hAc hTc hAi hTi
  have hCi : ∀ _x : Torus d, Integrable (fun _ : Torus d => -heatPosMass d a) μ :=
    fun _ => integrable_const _
  have hCc : Integrable (convMeasure (fun _ : Torus d => -heatPosMass d a) μ) μ :=
    intg_convMeasure_of_abs_le measurable_const (M := |heatPosMass d a|)
      (fun z => (abs_neg _).le) μ
  have hcong : pairKernel (periodicRiesz d 0) μ (x, y) =
      pairKernel (fun z => heatPos d a z + heatBand d a b z + heatTail d b z + -heatPosMass d a)
        μ (x, y) := by
    refine pairKernel_congr_offDiag hμ hρ (fun z hz => ?_) x y hxy
    rw [heatBand_decomp hd z hz ha hab, heatBand_zero_eq hd z hz ha]
    ring
  have e1 : pairKernel (fun z => heatPos d a z + heatBand d a b z + heatTail d b z
      + -heatPosMass d a) μ (x, y) =
      pairKernel (fun z => heatPos d a z + heatBand d a b z + heatTail d b z) μ (x, y)
        + pairKernel (fun _ : Torus d => -heatPosMass d a) μ (x, y) :=
    pairKernel_add (f₁ := fun z => heatPos d a z + heatBand d a b z + heatTail d b z)
      (f₂ := fun _ : Torus d => -heatPosMass d a) hBi' (fun x => hCi x) hBc' hCc x y
  have hs1 : pairKernel (fun z => heatPos d a z + heatBand d a b z) μ (x, y) =
      pairKernel (heatPos d a) μ (x, y) + pairKernel (heatBand d a b) μ (x, y) :=
    pairKernel_add (f₁ := heatPos d a) (f₂ := heatBand d a b) hPi hBi hPc hBc x y
  have hs2 : pairKernel (fun z => heatPos d a z + heatBand d a b z + heatTail d b z) μ (x, y) =
      pairKernel (fun z => heatPos d a z + heatBand d a b z) μ (x, y)
        + pairKernel (heatTail d b) μ (x, y) :=
    pairKernel_add (f₁ := fun z => heatPos d a z + heatBand d a b z) (f₂ := heatTail d b)
      hAi hTi hAc hTc x y
  rw [pairKernel_const, add_zero] at e1
  rw [hcong, e1, hs2, hs1]

/-- Off the collision set, with `Ch` a bound for `|g*μ|` and `E = ∬ g dμ dμ`:
`exponent ≤ β N Λ heatPosMass d a + ½ iidNeg(2β (heatBand a b)~) + lowConst d β √b Ch E`
(uses `iidNegativeStatistic_heatPos_le`, `iidNegativeStatistic_heatTail_le`). -/
theorem exponent_le (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β) {a δ : ℝ} (ha : 0 < a)
    (hab : a ≤ δ ^ 2) {Ch : ℝ} (hCh : ∀ x, |convMeasure (periodicRiesz d 0) μ x| ≤ Ch)
    {N : ℕ} (hN : 0 < N) (X : Config d N) (hX : X ∉ collisionSet d N) :
    exponent d β N μ X ≤
      β * N * (Λ * heatPosMass d a) +
        (1 / 2) * DGRHS.Concentration.iidNegativeStatistic N
          (fun p => 2 * β * pairKernel (heatBand d a (δ ^ 2)) μ p) X +
        lowConst d β δ Ch (energyPairing (periodicRiesz d 0) μ μ) := by
  have hb : 0 < δ ^ 2 := lt_of_lt_of_le ha hab
  have hNr : (0 : ℝ) < N := by exact_mod_cast hN
  have hN' : (N : ℝ) ≠ 0 := hNr.ne'
  have hdec : DGRHS.Concentration.iidNegativeStatistic N (pairKernel (periodicRiesz d 0) μ) X =
      DGRHS.Concentration.iidNegativeStatistic N (fun p => pairKernel (heatPos d a) μ p +
        pairKernel (heatBand d a (δ ^ 2)) μ p + pairKernel (heatTail d (δ ^ 2)) μ p) X :=
    iidNegativeStatistic_congr _ _ X hX fun x y hxy =>
      pairKernel_decomp hd hμ hρ hΛ ha hab x y hxy
  have hsA : DGRHS.Concentration.iidNegativeStatistic N (fun p => pairKernel (heatPos d a) μ p +
        pairKernel (heatBand d a (δ ^ 2)) μ p + pairKernel (heatTail d (δ ^ 2)) μ p) X =
      DGRHS.Concentration.iidNegativeStatistic N (fun p => pairKernel (heatPos d a) μ p +
        pairKernel (heatBand d a (δ ^ 2)) μ p) X +
      DGRHS.Concentration.iidNegativeStatistic N (pairKernel (heatTail d (δ ^ 2)) μ) X :=
    iidNegativeStatistic_add _ _ X
  have hsB : DGRHS.Concentration.iidNegativeStatistic N (fun p => pairKernel (heatPos d a) μ p +
        pairKernel (heatBand d a (δ ^ 2)) μ p) X =
      DGRHS.Concentration.iidNegativeStatistic N (pairKernel (heatPos d a) μ) X +
      DGRHS.Concentration.iidNegativeStatistic N (pairKernel (heatBand d a (δ ^ 2)) μ) X :=
    iidNegativeStatistic_add _ _ X
  have hsc : DGRHS.Concentration.iidNegativeStatistic N
      (fun p => 2 * β * pairKernel (heatBand d a (δ ^ 2)) μ p) X =
      2 * β * DGRHS.Concentration.iidNegativeStatistic N
        (pairKernel (heatBand d a (δ ^ 2)) μ) X :=
    iidNegativeStatistic_smul (2 * β) _ X
  have hP : DGRHS.Concentration.iidNegativeStatistic N (pairKernel (heatPos d a) μ) X ≤
      (N : ℝ) * (Λ * heatPosMass d a) :=
    iidNegativeStatistic_heatPos_le hd hμ hρ hΛ ha X
  have hT : DGRHS.Concentration.iidNegativeStatistic N (pairKernel (heatTail d (δ ^ 2)) μ) X ≤
      2 * heatTail d (δ ^ 2) 0 :=
    iidNegativeStatistic_heatTail_le hd hb X
  have hCs : ∑ i, convMeasure (periodicRiesz d 0) μ (X i) ≤ (N : ℝ) * Ch := by
    calc ∑ i, convMeasure (periodicRiesz d 0) μ (X i) ≤ ∑ _i : Fin N, Ch :=
          Finset.sum_le_sum fun i _ => (le_abs_self _).trans (hCh _)
      _ = (N : ℝ) * Ch := by simp
  have hS : (β / (N : ℝ)) * ∑ i, convMeasure (periodicRiesz d 0) μ (X i) ≤ β * Ch := by
    calc (β / (N : ℝ)) * ∑ i, convMeasure (periodicRiesz d 0) μ (X i)
        ≤ (β / (N : ℝ)) * ((N : ℝ) * Ch) :=
          mul_le_mul_of_nonneg_left hCs (div_nonneg hβ hNr.le)
      _ = β * Ch := by field_simp
  have hE : -(β / 2 * energyPairing (periodicRiesz d 0) μ μ) ≤
      β * (|energyPairing (periodicRiesz d 0) μ μ| / 2) := by
    have h1 := mul_le_mul_of_nonneg_left (neg_le_abs (energyPairing (periodicRiesz d 0) μ μ))
      (div_nonneg hβ (by norm_num : (0 : ℝ) ≤ 2))
    linarith
  have hβP := mul_le_mul_of_nonneg_left hP hβ
  have hβT := mul_le_mul_of_nonneg_left hT hβ
  rw [exponent_eq β hN μ X, hdec, hsA, hsB, hsc]
  unfold lowConst
  linarith

/-- The comparison field (M1) of `MasterCutoffData`: for `u ≥ u₀ ≥ 4 lowConst`, `A ≥ 8 nearConst`,
a.e. `u ≤ exponent → u ≤ iidNeg(q_u)` with `q_u = masterKernel d (α_u) δ β μ`. -/
theorem ae_exponent_compare (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β) {δ : ℝ} (hδ : 0 < δ)
    {A : ℝ} (hA : 0 < A) (hA' : 8 * nearConst d Λ ≤ A) {Ch : ℝ}
    (hCh : ∀ x, |convMeasure (periodicRiesz d 0) μ x| ≤ Ch) {u₀ : ℝ} (hu₀ : 1 ≤ u₀)
    (hlow : 4 * lowConst d β δ Ch (energyPairing (periodicRiesz d 0) μ μ) ≤ u₀)
    {N : ℕ} (hN : 1 ≤ N) {u : ℝ} (hu : u₀ ≤ u) :
    ∀ᵐ X ∂(Measure.pi fun _ : Fin N => μ), u ≤ exponent d β N μ X →
      u ≤ DGRHS.Concentration.iidNegativeStatistic N
        (masterKernel d (adaptiveScale δ A β N u d) δ β μ) X := by
  have hΛ0 : 0 ≤ Λ := le_trans (hρ.nonneg 0) (hΛ 0)
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hnC : 0 ≤ nearConst d Λ :=
    mul_nonneg (mul_nonneg hΛ0 (subA_zero_pos hd).le) (div_nonneg (by norm_num) (Nat.cast_nonneg d))
  have hu0 : 0 < u := by linarith
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hα : 0 < adaptiveScale δ A β N u d := adaptiveScale_pos hδ hA hβ hn hu0 hdR
  have hαδ : adaptiveScale δ A β N u d ≤ δ := adaptiveScale_le
  have hab : adaptiveScale δ A β N u d ^ 2 ≤ δ ^ 2 := pow_le_pow_left₀ hα.le hαδ 2
  have hnear : β * N * (Λ * heatPosMass d (adaptiveScale δ A β N u d ^ 2)) ≤ u / 8 := by
    rw [heatPosMass_sq hd Λ hα.le]
    exact adaptiveScale_near_error_le hδ hA hβ hn hu0 hdR hnC hA'
  have hlow' : lowConst d β δ Ch (energyPairing (periodicRiesz d 0) μ μ) ≤ u / 4 := by
    linarith
  filter_upwards [ae_notMem_collisionSet (by omega : 1 ≤ d) hμ hρ N] with X hX
  intro hle
  have hkey := exponent_le hd hμ hρ hΛ hβ (pow_pos hα 2) hab hCh (by omega : 0 < N) X hX
  show u ≤ DGRHS.Concentration.iidNegativeStatistic N
    (fun p => 2 * β * pairKernel (heatBand d (adaptiveScale δ A β N u d ^ 2) (δ ^ 2)) μ p) X
  linarith

/-! ### The size bound and the data -/

/-- Affine majorant of the band logarithm: for `u ≥ 1`,
`log(δ/α_u) ≤ |(1/d) log(A δ^d)| + (1/d) log(1 + β N)` (from `log_div_adaptiveScale_le`). -/
theorem log_div_adaptiveScale_le_affine {δ A β : ℝ} (hδ : 0 < δ) (hA : 0 < A) (hβ : 0 ≤ β)
    {N : ℕ} {u : ℝ} (hu : 1 ≤ u) (hdr : 0 < (d : ℝ)) :
    Real.log (δ / adaptiveScale δ A β (N : ℝ) u d) ≤
      |(1 / (d : ℝ)) * Real.log (A * δ ^ (d : ℝ))| + (1 / (d : ℝ)) * Real.log (1 + β * N) := by
  have hn : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hl := log_div_adaptiveScale_le hδ hA hβ hn hu hdr
  have hK : 0 < A * δ ^ (d : ℝ) := mul_pos hA (Real.rpow_pos_of_pos hδ _)
  have hβn : 0 ≤ β * N := mul_nonneg hβ hn
  have hB : 0 < 1 + β * N := by linarith
  have hL0 : 0 ≤ Real.log (1 + β * N) := Real.log_nonneg (by linarith)
  have hd1 : 0 ≤ 1 / (d : ℝ) := by positivity
  refine hl.trans (max_le ?_ ?_)
  · exact add_nonneg (abs_nonneg _) (mul_nonneg hd1 hL0)
  · have e : A * (1 + β * N) * δ ^ (d : ℝ) = (A * δ ^ (d : ℝ)) * (1 + β * N) := by ring
    rw [e, Real.log_mul hK.ne' hB.ne', mul_add]
    have := le_abs_self ((1 / (d : ℝ)) * Real.log (A * δ ^ (d : ℝ)))
    linarith

/-- Size bound: `masterCutoffValues ⊆ [0, (1 + 8βC L_N)(1 + 16βC L_N)]` with
`L_N = max 0 ((1/d) log(A(1+βN)δ^d))`, hence bounded above and `masterCutoffSize ≤ K N^{2/3}`
(analogue of `DGRHS.Gaussian.gaussianLogAdaptive_actual_size_bound`). -/
theorem masterCutoffSize_le (hd : 2 ≤ d) [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β) {δ : ℝ}
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) {A : ℝ} (hA : 0 < A) {u₀ : ℝ} (hu₀ : 1 ≤ u₀) :
    ∃ K : ℝ, ∀ N : ℕ, 1 ≤ N →
      BddAbove (DGRHS.Concentration.masterCutoffValues μ
        (fun u => masterKernel d (adaptiveScale δ A β N u d) δ β μ)
        (fun u => masterCap d (adaptiveScale δ A β N u d) δ β) u₀) ∧
      DGRHS.Concentration.masterCutoffSize μ
        (fun u => masterKernel d (adaptiveScale δ A β N u d) δ β μ)
        (fun u => masterCap d (adaptiveScale δ A β N u d) δ β) u₀ ≤ K * (N : ℝ) ^ ((2 : ℝ) / 3) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hC0 : 0 ≤ bandSupConst d := (bandSupConst_pos hd).le
  have hX : 0 ≤ 16 * β * bandSupConst d := mul_nonneg (mul_nonneg (by norm_num) hβ) hC0
  have h8 : 0 ≤ 8 * β * bandSupConst d := mul_nonneg (mul_nonneg (by norm_num) hβ) hC0
  have hd1 : 0 ≤ 1 / (d : ℝ) := by positivity
  obtain ⟨c₀, hc₀⟩ : ∃ c₀ : ℝ, c₀ = 1 + 16 * β * bandSupConst d *
      |(1 / (d : ℝ)) * Real.log (A * δ ^ (d : ℝ))| := ⟨_, rfl⟩
  obtain ⟨c₁, hc₁⟩ : ∃ c₁ : ℝ, c₁ = 16 * β * bandSupConst d * (1 / (d : ℝ)) := ⟨_, rfl⟩
  have hc₀0 : 0 ≤ c₀ := by
    rw [hc₀]; exact add_nonneg zero_le_one (mul_nonneg hX (abs_nonneg _))
  have hc₁0 : 0 ≤ c₁ := by rw [hc₁]; exact mul_nonneg hX hd1
  obtain ⟨K, hK⟩ := log_sq_le_rpow c₀ c₁ β hc₀0 hc₁0 hβ
  refine ⟨K, fun N hN => ?_⟩
  have hN0 : (0 : ℝ) ≤ N := Nat.cast_nonneg N
  have hbound : ∀ u : ℝ, u₀ ≤ u →
      min u (masterCap d (adaptiveScale δ A β N u d) δ β) *
        (1 + (eLpNormEssSup (masterKernel d (adaptiveScale δ A β N u d) δ β μ)
          (μ.prod μ)).toReal) ≤ K * (N : ℝ) ^ ((2 : ℝ) / 3) := by
    intro u hu
    have hu1 : 1 ≤ u := hu₀.trans hu
    have hu0 : 0 < u := by linarith
    have hα : 0 < adaptiveScale δ A β N u d := adaptiveScale_pos hδ hA hβ hN0 hu0 hdR
    have hαδ : adaptiveScale δ A β N u d ≤ δ := adaptiveScale_le
    have hL := log_div_adaptiveScale_le_affine (d := d) (N := N) hδ hA hβ hu1 hdR
    have hlog0 : 0 ≤ Real.log (δ / adaptiveScale δ A β N u d) :=
      log_div_adaptiveScale_nonneg hδ hA hβ hN0 hu0 hdR
    obtain ⟨Lb, hLb⟩ : ∃ Lb : ℝ, Lb = |(1 / (d : ℝ)) * Real.log (A * δ ^ (d : ℝ))| +
        (1 / (d : ℝ)) * Real.log (1 + β * N) := ⟨_, rfl⟩
    rw [← hLb] at hL
    have hL0 : 0 ≤ Lb := by
      rw [hLb]
      exact add_nonneg (abs_nonneg _)
        (mul_nonneg hd1 (Real.log_nonneg (by have := mul_nonneg hβ hN0; linarith)))
    have hm : masterCap d (adaptiveScale δ A β N u d) δ β ≤ 1 + 16 * β * bandSupConst d * Lb := by
      unfold masterCap
      have h1 := mul_le_mul_of_nonneg_left hL h8
      have h2 := mul_nonneg h8 hL0
      linarith
    have hq : (eLpNormEssSup (masterKernel d (adaptiveScale δ A β N u d) δ β μ)
        (μ.prod μ)).toReal ≤ 16 * β * bandSupConst d * Lb := by
      have h0 := eLpNormEssSup_masterKernel_le (μ := μ) hd hα hαδ hδ1 hβ
      have h1 := mul_le_mul_of_nonneg_left hL hX
      linarith
    have hmin0 : 0 ≤ min u (masterCap d (adaptiveScale δ A β N u d) δ β) := by
      refine le_min hu0.le ?_
      unfold masterCap
      have := mul_nonneg h8 hlog0
      linarith
    have hmin_le : min u (masterCap d (adaptiveScale δ A β N u d) δ β) ≤
        1 + 16 * β * bandSupConst d * Lb := (min_le_right _ _).trans hm
    have hq0 : 0 ≤ (eLpNormEssSup (masterKernel d (adaptiveScale δ A β N u d) δ β μ)
        (μ.prod μ)).toReal := ENNReal.toReal_nonneg
    have hfac : 1 + (eLpNormEssSup (masterKernel d (adaptiveScale δ A β N u d) δ β μ)
        (μ.prod μ)).toReal ≤ 1 + 16 * β * bandSupConst d * Lb := by linarith
    have hY0 : 0 ≤ 1 + 16 * β * bandSupConst d * Lb := by
      have := mul_nonneg hX hL0; linarith
    have hYc : 1 + 16 * β * bandSupConst d * Lb ≤ c₀ + c₁ * Real.log (1 + β * N) := by
      have e : c₀ + c₁ * Real.log (1 + β * N) = 1 + 16 * β * bandSupConst d * Lb := by
        rw [hc₀, hc₁, hLb]; ring
      exact le_of_eq e.symm
    have s1 := mul_le_mul hmin_le hfac (by linarith) hY0
    have s2 := mul_le_mul hYc hYc hY0 (hY0.trans hYc)
    have hstep := s1.trans s2
    have hK' := hK N hN
    rw [sq] at hK'
    exact hstep.trans hK'
  refine ⟨bddAbove_def.mpr ⟨K * (N : ℝ) ^ ((2 : ℝ) / 3), ?_⟩, ?_⟩
  · rintro s ⟨u, hu, rfl⟩
    exact hbound u hu
  · unfold DGRHS.Concentration.masterCutoffSize
    refine csSup_le ⟨_, u₀, le_rfl, rfl⟩ ?_
    rintro s ⟨u, hu, rfl⟩
    exact hbound u hu

/-- The master cutoff data for the periodic logarithm, uniformly in `N ≥ 1`: there are a band
scale `δ`, a threshold `u₀` and a near-field constant `A` such that for every `N ≥ 1` the kernels
`u ↦ masterKernel d (α_u) δ β μ` and caps `u ↦ masterCap d (α_u) δ β` form a
`MasterCutoffData μ N (exponent d β N μ) u₀`. -/
theorem exists_masterData (hd : 2 ≤ d) (hμ : μ = withDensityReal ρ) (hρ : IsProbDensity ρ)
    (hΛ : ∀ x, ρ x ≤ Λ) [IsProbabilityMeasure μ] {β : ℝ} (hβ : 0 ≤ β) :
    ∃ δ u₀ A : ℝ, 0 < δ ∧ δ ≤ 1 / 2 ∧ 1 ≤ u₀ ∧ 0 < A ∧
      ∀ N : ℕ, 1 ≤ N →
        ∃ data : DGRHS.Concentration.MasterCutoffData μ N (exponent d β N μ) u₀,
          data.kernel = (fun u => masterKernel d (adaptiveScale δ A β N u d) δ β μ) ∧
          data.cap = (fun u => masterCap d (adaptiveScale δ A β N u d) δ β) := by
  have hdR : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  have hΛ0 : 0 ≤ Λ := le_trans (hρ.nonneg 0) (hΛ 0)
  have hnC : 0 ≤ nearConst d Λ :=
    mul_nonneg (mul_nonneg hΛ0 (subA_zero_pos hd).le) (div_nonneg (by norm_num) (Nat.cast_nonneg d))
  obtain ⟨Ch, hCh⟩ := HRS.convMeasure_bounded (s := 0) hd le_rfl hdR ρ hρ Λ hΛ
  have hCh' : ∀ x, |convMeasure (periodicRiesz d 0) μ x| ≤ Ch := by
    rw [hμ]; exact hCh
  obtain ⟨δ, hδpos, hδ2, hrow, hop⟩ :=
    exists_master_scale (L := DGRHS.Concentration.glzUniversalTailConstant) hd hΛ0 hβ
      DGRHS.Concentration.glzUniversalTailConstant_pos
  have hδ1 : δ ≤ 1 := by linarith
  have hδ2' : δ ^ 2 ≤ 1 / 2 := by nlinarith
  obtain ⟨u₀, hu₀def⟩ : ∃ u₀ : ℝ, u₀ = max 1
      (4 * lowConst d β δ Ch (energyPairing (periodicRiesz d 0) μ μ)) := ⟨_, rfl⟩
  obtain ⟨A, hAdef⟩ : ∃ A : ℝ, A = 8 * nearConst d Λ + 1 := ⟨_, rfl⟩
  have hA : 0 < A := by rw [hAdef]; linarith
  have hA' : 8 * nearConst d Λ ≤ A := by rw [hAdef]; linarith
  have hu₀1 : 1 ≤ u₀ := by rw [hu₀def]; exact le_max_left _ _
  have hlow : 4 * lowConst d β δ Ch (energyPairing (periodicRiesz d 0) μ μ) ≤ u₀ := by
    rw [hu₀def]; exact le_max_right _ _
  refine ⟨δ, u₀, A, hδpos, hδ2, hu₀1, hA, fun N hN => ?_⟩
  obtain ⟨K, hK⟩ := masterCutoffSize_le (μ := μ) hd hβ hδpos hδ1 hA hu₀1
  have hαpos : ∀ u : ℝ, u₀ ≤ u → 0 < adaptiveScale δ A β N u d := fun u hu =>
    adaptiveScale_pos hδpos hA hβ (Nat.cast_nonneg N) (by linarith) hdR
  have hαδ : ∀ u : ℝ, adaptiveScale δ A β N u d ≤ δ := fun _ => adaptiveScale_le
  have hnorm : ∀ u : ℝ, u₀ ≤ u →
      (∀ᵐ x ∂μ, ∫ y, masterKernel d (adaptiveScale δ A β N u d) δ β μ (x, y) ^ 2 ∂μ ≤
          1 / DGRHS.Concentration.glzUniversalTailConstant) ∧
      (∫ p, masterKernel d (adaptiveScale δ A β N u d) δ β μ p ^ 2 ∂(μ.prod μ)) ≤
          1 / DGRHS.Concentration.glzUniversalTailConstant ∧
      ∀ h2 : MemLp (masterKernel d (adaptiveScale δ A β N u d) δ β μ) 2 (μ.prod μ),
        ‖DGRHS.Kernel.integralOperator (masterKernel d (adaptiveScale δ A β N u d) δ β μ) h2‖ ≤
          1 / DGRHS.Concentration.glzUniversalTailConstant := fun u hu =>
    masterKernel_norm_fields hd hμ hρ hΛ (hαpos u hu) (hαδ u) hδ2' hβ
      DGRHS.Concentration.glzUniversalTailConstant_pos hrow hop
  exact ⟨{ kernel := fun u => masterKernel d (adaptiveScale δ A β N u d) δ β μ
           cap := fun u => masterCap d (adaptiveScale δ A β N u d) δ β
           measurable := fun u hu => measurable_masterKernel hd (hαpos u hu)
           memLp := fun u hu => memLp_top_masterKernel hd (hαpos u hu) (hαδ u) hδ1 hβ
           symmetric := fun u _ x y => masterKernel_symm hd _ δ β x y
           canonical := fun u hu => ae_of_all _ fun x =>
             integral_masterKernel_eq_zero hd (hαpos u hu) x
           cap_pos := fun u hu => masterCap_pos hd (hαpos u hu) (hαδ u) hβ
           compare := fun u hu => ae_exponent_compare hd hμ hρ hΛ hβ hδpos hA hA' hCh' hu₀1
             hlow hN hu
           capped := fun u hu => ae_of_all _ fun X =>
             iidNegativeStatistic_masterKernel_le hd (hαpos u hu) (hαδ u) hδ1 hβ X
           row := fun u hu => (hnorm u hu).1
           joint := fun u hu => (hnorm u hu).2.1
           operator := fun u hu => (hnorm u hu).2.2 _
           size_finite := (hK N hN).1 },
    rfl, rfl⟩

end Repulsive

end HRS

end
