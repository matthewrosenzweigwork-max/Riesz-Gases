import HRS.Prob.Metrics

/-!
# Packet FamW / W3: moment facts on `ℝ` for the Wasserstein comparison

* `third_moment_le_wasserstein` (T1): `|∫ z³ dP| ≤ 3√B · W₂(P,Q)` when `∫ z⁴ ≤ B` under `P` and `Q`
  and `∫ z³ dQ = 0`.
* `fourth_moment_of_tail` (T2): a tail bound `P(|z| > x) ≤ 4 e^{-x²/(2D)}` gives `∫ z⁴ dP ≤ 32 D²`.
* `gaussianReal_third_moment_zero` (T3): the centred Gaussian has vanishing third moment.

Proof of T1: for a coupling `π`, `z.1³ - z.2³ = (z.1 - z.2) h(z)` with `h = z.1² + z.1 z.2 + z.2²`.
Hölder in `ℝ≥0∞` bounds the signed difference by the cost factor times `‖h‖₂`, and
`h² ≤ (9/2)(z.1⁴ + z.2⁴)` bounds `‖h‖₂ ≤ 3√B`.  The infimum over couplings is taken last.
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

noncomputable section

namespace HRS.ME.FamW

/-- The product measure is a coupling of `P` and `Q`. -/
theorem prod_isCoupling (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q] :
    IsCoupling (P.prod Q) P Q := by
  unfold IsCoupling
  refine ⟨?_, ?_⟩
  · rw [Measure.map_fst_prod]; simp
  · rw [Measure.map_snd_prod]; simp

/-- Transfer of a real integral along the first marginal of a coupling. -/
theorem integral_fst_of (π : Measure (ℝ × ℝ)) (P : Measure ℝ) (hπ : π.map Prod.fst = P)
    (g : ℝ → ℝ) (hg : Measurable g) : ∫ z, g z ∂P = ∫ z : ℝ × ℝ, g z.1 ∂π := by
  subst hπ
  exact integral_map measurable_fst.aemeasurable hg.aestronglyMeasurable

/-- Transfer of a real integral along the second marginal of a coupling. -/
theorem integral_snd_of (π : Measure (ℝ × ℝ)) (Q : Measure ℝ) (hπ : π.map Prod.snd = Q)
    (g : ℝ → ℝ) (hg : Measurable g) : ∫ z, g z ∂Q = ∫ z : ℝ × ℝ, g z.2 ∂π := by
  subst hπ
  exact integral_map measurable_snd.aemeasurable hg.aestronglyMeasurable

/-- Integrability transfers along the first marginal of a coupling. -/
theorem integrable_fst_of (π : Measure (ℝ × ℝ)) (P : Measure ℝ) (hπ : π.map Prod.fst = P)
    {g : ℝ → ℝ} (hg : Measurable g) (h : Integrable g P) :
    Integrable (fun z : ℝ × ℝ => g z.1) π := by
  subst hπ
  exact (integrable_map_measure hg.aestronglyMeasurable measurable_fst.aemeasurable).1 h

/-- Integrability transfers along the second marginal of a coupling. -/
theorem integrable_snd_of (π : Measure (ℝ × ℝ)) (Q : Measure ℝ) (hπ : π.map Prod.snd = Q)
    {g : ℝ → ℝ} (hg : Measurable g) (h : Integrable g Q) :
    Integrable (fun z : ℝ × ℝ => g z.2) π := by
  subst hπ
  exact (integrable_map_measure hg.aestronglyMeasurable measurable_snd.aemeasurable).1 h

/-- A fourth-moment-integrable probability measure has integrable third moment. -/
theorem integrable_cube_of_fourth (P : Measure ℝ) [IsProbabilityMeasure P]
    (h4 : Integrable (fun z : ℝ => z ^ 4) P) : Integrable (fun z : ℝ => z ^ 3) P := by
  refine Integrable.mono' ((integrable_const (1 : ℝ)).add h4)
    (by fun_prop : Continuous fun z : ℝ => z ^ 3).aestronglyMeasurable ?_
  refine Eventually.of_forall fun z => ?_
  have ht : 0 ≤ |z| := abs_nonneg z
  have key : |z| ^ 3 ≤ 1 + |z| ^ 4 := by
    rcases le_total |z| 1 with h | h
    · have h3 : |z| ^ 3 ≤ 1 := pow_le_one₀ ht h
      nlinarith [pow_nonneg ht 4]
    · nlinarith [mul_nonneg (pow_nonneg ht 3) (sub_nonneg.2 h)]
  have h4 : |z| ^ 4 = z ^ 4 := Even.pow_abs ⟨2, rfl⟩ z
  show ‖z ^ 3‖ ≤ 1 + z ^ 4
  rw [Real.norm_eq_abs, abs_pow, ← h4]
  exact key

/-- Per-coupling bound: `|∫ z³ dP| ≤ 3√B · (cost of π)^{1/2}`. -/
theorem coupling_bound (P Q : Measure ℝ) [IsProbabilityMeasure P] [IsProbabilityMeasure Q]
    (B : ℝ) (hB : 0 ≤ B)
    (hP4 : Integrable (fun z : ℝ => z ^ 4) P) (hQ4 : Integrable (fun z : ℝ => z ^ 4) Q)
    (hPB : ∫ z, z ^ 4 ∂P ≤ B) (hQB : ∫ z, z ^ 4 ∂Q ≤ B) (hQ3 : ∫ z, z ^ 3 ∂Q = 0)
    (π : Measure (ℝ × ℝ)) (hπ : IsCoupling π P Q) :
    ENNReal.ofReal |∫ z, z ^ 3 ∂P| ≤
      ENNReal.ofReal (3 * Real.sqrt B) *
        (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π) ^ (1 / (2 : ℝ)) := by
  have : IsProbabilityMeasure π := hπ.isProbabilityMeasure
  have hpq : (2 : ℝ).HolderConjugate 2 := Real.holderConjugate_iff.2 ⟨by norm_num, by norm_num⟩
  -- signed difference of third moments
  have hcube1 : Integrable (fun z : ℝ × ℝ => z.1 ^ 3) π :=
    integrable_fst_of π P hπ.1 (g := fun z : ℝ => z ^ 3) (by fun_prop)
      (integrable_cube_of_fourth P hP4)
  have hcube2 : Integrable (fun z : ℝ × ℝ => z.2 ^ 3) π :=
    integrable_snd_of π Q hπ.2 (g := fun z : ℝ => z ^ 3) (by fun_prop)
      (integrable_cube_of_fourth Q hQ4)
  have e1 : ∫ z, z ^ 3 ∂P = ∫ z : ℝ × ℝ, z.1 ^ 3 ∂π :=
    integral_fst_of π P hπ.1 (fun z : ℝ => z ^ 3) (by fun_prop)
  have e2 : ∫ z, z ^ 3 ∂Q = ∫ z : ℝ × ℝ, z.2 ^ 3 ∂π :=
    integral_snd_of π Q hπ.2 (fun z : ℝ => z ^ 3) (by fun_prop)
  have hdiff : ∫ z, z ^ 3 ∂P = ∫ z : ℝ × ℝ, (z.1 ^ 3 - z.2 ^ 3) ∂π := by
    rw [e1, integral_sub hcube1 hcube2, ← e2, hQ3, sub_zero]
  -- marginal second moments of the cost factor
  have hA : ∫⁻ z : ℝ × ℝ, ‖z.1 - z.2‖ₑ ^ (2 : ℝ) ∂π =
      ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π := by
    refine lintegral_congr fun z => ?_
    rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num),
      Real.norm_eq_abs]
  -- second factor: `∫ ‖h‖ₑ² dπ ≤ 9B`, with `h = z.1² + z.1 z.2 + z.2²`
  have hB2 : ∫⁻ z : ℝ × ℝ, ‖z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2‖ₑ ^ (2 : ℝ) ∂π ≤
      ENNReal.ofReal (9 * B) := by
    have hpt : ∀ z : ℝ × ℝ, ‖z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2‖ₑ ^ (2 : ℝ) ≤
        ENNReal.ofReal (9 / 2 * (z.1 ^ 4 + z.2 ^ 4)) := by
      intro z
      rw [Real.enorm_eq_ofReal_abs, ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num)]
      apply ENNReal.ofReal_le_ofReal
      rw [Real.rpow_two, sq_abs]
      nlinarith [sq_nonneg (z.1 ^ 2 - z.1 * z.2), sq_nonneg (z.2 ^ 2 - z.1 * z.2),
        sq_nonneg (z.1 ^ 2 - z.2 ^ 2)]
    have hi4P : Integrable (fun z : ℝ × ℝ => z.1 ^ 4) π :=
      integrable_fst_of π P hπ.1 (g := fun z : ℝ => z ^ 4) (by fun_prop) hP4
    have hi4Q : Integrable (fun z : ℝ × ℝ => z.2 ^ 4) π :=
      integrable_snd_of π Q hπ.2 (g := fun z : ℝ => z ^ 4) (by fun_prop) hQ4
    have hint : Integrable (fun z : ℝ × ℝ => 9 / 2 * (z.1 ^ 4 + z.2 ^ 4)) π :=
      (hi4P.add hi4Q).const_mul (9 / 2)
    have e4P : ∫ z : ℝ × ℝ, z.1 ^ 4 ∂π = ∫ z, z ^ 4 ∂P :=
      (integral_fst_of π P hπ.1 (fun z : ℝ => z ^ 4) (by fun_prop)).symm
    have e4Q : ∫ z : ℝ × ℝ, z.2 ^ 4 ∂π = ∫ z, z ^ 4 ∂Q :=
      (integral_snd_of π Q hπ.2 (fun z : ℝ => z ^ 4) (by fun_prop)).symm
    calc ∫⁻ z : ℝ × ℝ, ‖z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2‖ₑ ^ (2 : ℝ) ∂π
        ≤ ∫⁻ z : ℝ × ℝ, ENNReal.ofReal (9 / 2 * (z.1 ^ 4 + z.2 ^ 4)) ∂π :=
          lintegral_mono fun z => hpt z
      _ = ENNReal.ofReal (∫ z : ℝ × ℝ, 9 / 2 * (z.1 ^ 4 + z.2 ^ 4) ∂π) :=
          (ofReal_integral_eq_lintegral_ofReal hint
            (Eventually.of_forall fun z => (by positivity : (0 : ℝ) ≤ 9 / 2 * (z.1 ^ 4 + z.2 ^ 4)))).symm
      _ ≤ ENNReal.ofReal (9 * B) := by
          apply ENNReal.ofReal_le_ofReal
          rw [integral_const_mul, integral_add hi4P hi4Q, e4P, e4Q]
          linarith
  have hG : (∫⁻ z : ℝ × ℝ, ‖z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2‖ₑ ^ (2 : ℝ) ∂π) ^ (1 / (2 : ℝ)) ≤
      ENNReal.ofReal (3 * Real.sqrt B) := by
    have h9 : 0 ≤ 9 * B := by linarith
    calc (∫⁻ z : ℝ × ℝ, ‖z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2‖ₑ ^ (2 : ℝ) ∂π) ^ (1 / (2 : ℝ))
        ≤ (ENNReal.ofReal (9 * B)) ^ (1 / (2 : ℝ)) := ENNReal.rpow_le_rpow hB2 (by norm_num)
      _ = ENNReal.ofReal ((9 * B) ^ (1 / (2 : ℝ))) :=
          (ENNReal.ofReal_rpow_of_nonneg h9 (by norm_num))
      _ = ENNReal.ofReal (3 * Real.sqrt B) := by
          congr 1
          rw [← Real.sqrt_eq_rpow, Real.sqrt_mul (by norm_num : (0 : ℝ) ≤ 9),
            show (9 : ℝ) = 3 ^ 2 by norm_num, Real.sqrt_sq (by norm_num : (0 : ℝ) ≤ 3)]
  -- Hölder for the signed difference
  have hHold : ∫⁻ z : ℝ × ℝ, ‖z.1 ^ 3 - z.2 ^ 3‖ₑ ∂π ≤
      (∫⁻ z : ℝ × ℝ, ‖z.1 - z.2‖ₑ ^ (2 : ℝ) ∂π) ^ (1 / (2 : ℝ)) *
        (∫⁻ z : ℝ × ℝ, ‖z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2‖ₑ ^ (2 : ℝ) ∂π) ^ (1 / (2 : ℝ)) := by
    have hf : AEMeasurable (fun z : ℝ × ℝ => ‖z.1 - z.2‖ₑ) π :=
      (by fun_prop : Measurable fun z : ℝ × ℝ => ‖z.1 - z.2‖ₑ).aemeasurable
    have hg : AEMeasurable (fun z : ℝ × ℝ => ‖z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2‖ₑ) π :=
      (by fun_prop : Measurable fun z : ℝ × ℝ => ‖z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2‖ₑ).aemeasurable
    have hH := ENNReal.lintegral_mul_le_Lp_mul_Lq π hpq hf hg
    have heq : ∫⁻ z : ℝ × ℝ, ‖z.1 ^ 3 - z.2 ^ 3‖ₑ ∂π =
        ∫⁻ z : ℝ × ℝ, (‖z.1 - z.2‖ₑ * ‖z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2‖ₑ) ∂π := by
      refine lintegral_congr fun z => ?_
      rw [show z.1 ^ 3 - z.2 ^ 3 = (z.1 - z.2) * (z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2) by ring,
        enorm_mul]
    rw [heq]
    exact hH
  calc ENNReal.ofReal |∫ z, z ^ 3 ∂P|
      = ‖∫ z : ℝ × ℝ, (z.1 ^ 3 - z.2 ^ 3) ∂π‖ₑ := by
        rw [hdiff, Real.enorm_eq_ofReal_abs]
    _ ≤ ∫⁻ z : ℝ × ℝ, ‖z.1 ^ 3 - z.2 ^ 3‖ₑ ∂π := enorm_integral_le_lintegral_enorm _
    _ ≤ (∫⁻ z : ℝ × ℝ, ‖z.1 - z.2‖ₑ ^ (2 : ℝ) ∂π) ^ (1 / (2 : ℝ)) *
        (∫⁻ z : ℝ × ℝ, ‖z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2‖ₑ ^ (2 : ℝ) ∂π) ^ (1 / (2 : ℝ)) := hHold
    _ = (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π) ^ (1 / (2 : ℝ)) *
        (∫⁻ z : ℝ × ℝ, ‖z.1 ^ 2 + z.1 * z.2 + z.2 ^ 2‖ₑ ^ (2 : ℝ) ∂π) ^ (1 / (2 : ℝ)) := by
        rw [hA]
    _ ≤ (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π) ^ (1 / (2 : ℝ)) *
        ENNReal.ofReal (3 * Real.sqrt B) := by gcongr
    _ = ENNReal.ofReal (3 * Real.sqrt B) *
        (∫⁻ z : ℝ × ℝ, ENNReal.ofReal (‖z.1 - z.2‖ ^ (2 : ℝ)) ∂π) ^ (1 / (2 : ℝ)) := mul_comm _ _

/-- **T1.** Third-moment Wasserstein bound: if `∫z⁴ ≤ B` under `P` and `Q`, and `∫z³ dQ = 0`,
then `|∫z³ dP| ≤ 3√B · W₂(P,Q)`, with `W₂ = wassersteinE 2` in `ℝ≥0∞`. -/
theorem third_moment_le_wasserstein (P Q : Measure ℝ) [IsProbabilityMeasure P]
    [IsProbabilityMeasure Q] (B : ℝ) (hB : 0 ≤ B)
    (hP4 : Integrable (fun z : ℝ => z ^ 4) P) (hQ4 : Integrable (fun z : ℝ => z ^ 4) Q)
    (hPB : ∫ z, z ^ 4 ∂P ≤ B) (hQB : ∫ z, z ^ 4 ∂Q ≤ B) (hQ3 : ∫ z, z ^ 3 ∂Q = 0) :
    ENNReal.ofReal |∫ z, z ^ 3 ∂P| ≤ ENNReal.ofReal (3 * Real.sqrt B) * wassersteinE 2 P Q := by
  unfold wassersteinE
  have hK : ENNReal.ofReal (3 * Real.sqrt B) ≠ ⊤ := ENNReal.ofReal_ne_top
  have : Nonempty (couplings P Q) := ⟨⟨P.prod Q, prod_isCoupling P Q⟩⟩
  rw [ENNReal.mul_iInf (fun h => absurd h hK)]
  exact le_iInf fun π => coupling_bound P Q B hB hP4 hQ4 hPB hQB hQ3 π.1 π.2

/-- **T2.** Fourth moment from a Gaussian-type tail bound `P(|z| > x) ≤ 4 e^{-x²/(2D)}`:
`z ↦ z⁴` is `P`-integrable and `∫ z⁴ dP ≤ 32 D²`. -/
theorem fourth_moment_of_tail (P : Measure ℝ) [IsProbabilityMeasure P] (D : ℝ) (hD : 0 < D)
    (htail : ∀ x : ℝ, 0 ≤ x → P {z | x < |z|} ≤ ENNReal.ofReal (4 * Real.exp (-x ^ 2 / (2 * D)))) :
    Integrable (fun z : ℝ => z ^ 4) P ∧ ∫ z, z ^ 4 ∂P ≤ 32 * D ^ 2 := by
  have hb : (0 : ℝ) < 1 / (2 * D) := by positivity
  -- the Gamma-type weight `t³ e^{-t²/(2D)}` on `(0,∞)` (rpow form for the mathlib integral)
  have hFint : IntegrableOn (fun t : ℝ => t ^ (3 : ℝ) * Real.exp (-(1 / (2 * D)) * t ^ (2 : ℝ)))
      (Ioi 0) :=
    integrableOn_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb
  have hFnn : ∀ t ∈ Ioi (0 : ℝ),
      0 ≤ t ^ (3 : ℝ) * Real.exp (-(1 / (2 * D)) * t ^ (2 : ℝ)) := fun t ht =>
    mul_nonneg (Real.rpow_nonneg (le_of_lt ht) _) (Real.exp_pos _).le
  have hFval : ∫ t in Ioi (0 : ℝ), t ^ (3 : ℝ) * Real.exp (-(1 / (2 * D)) * t ^ (2 : ℝ)) =
      2 * D ^ 2 := by
    rw [integral_rpow_mul_exp_neg_mul_rpow (by norm_num) (by norm_num) hb]
    have e1 : (1 / (2 * D)) ^ (-(3 + 1) / 2 : ℝ) = (2 * D) ^ 2 := by
      rw [show (-(3 + 1) / 2 : ℝ) = -(2 : ℝ) by norm_num, Real.rpow_neg hb.le, Real.rpow_two]
      field_simp
    have e2 : ((3 : ℝ) + 1) / 2 = 2 := by norm_num
    rw [e1, e2, Real.Gamma_two]
    ring
  -- layer cake: `∫⁻ z⁴ dP = ∫⁻_{t>0} P(|z| > t) · 4t³`
  have hlc := MeasureTheory.lintegral_comp_eq_lintegral_meas_lt_mul (μ := P)
    (f := fun z : ℝ => |z|) (g := fun t : ℝ => 4 * t ^ 3)
    (Eventually.of_forall fun z => abs_nonneg z) (continuous_abs.measurable).aemeasurable
    (fun _ _ => (by fun_prop : Continuous fun t : ℝ => 4 * t ^ 3).intervalIntegrable _ _)
    ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => by
      have : (0 : ℝ) < t := ht
      positivity)
  have hinner : ∀ w : ℝ, ∫ t in (0 : ℝ)..|w|, 4 * t ^ 3 = w ^ 4 := by
    intro w
    have h4 : |w| ^ 4 = w ^ 4 := Even.pow_abs ⟨2, rfl⟩ w
    rw [intervalIntegral.integral_const_mul, integral_pow]
    norm_num
    linarith [h4]
  simp only [hinner] at hlc
  -- pointwise tail bound on `(0, ∞)`
  have hbound : ∫⁻ t in Ioi (0 : ℝ), P {a | t < |a|} * ENNReal.ofReal (4 * t ^ 3) ≤
      ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
        (16 * (t ^ (3 : ℝ) * Real.exp (-(1 / (2 * D)) * t ^ (2 : ℝ)))) := by
    refine lintegral_mono_ae ((ae_restrict_mem measurableSet_Ioi).mono fun t ht => ?_)
    have ht0 : 0 < t := ht
    have hexp : -t ^ 2 / (2 * D) = -(1 / (2 * D)) * t ^ (2 : ℝ) := by
      rw [Real.rpow_two]; ring
    have h3 : t ^ (3 : ℝ) = t ^ 3 := by exact_mod_cast Real.rpow_natCast t 3
    calc P {a | t < |a|} * ENNReal.ofReal (4 * t ^ 3)
        ≤ ENNReal.ofReal (4 * Real.exp (-t ^ 2 / (2 * D))) * ENNReal.ofReal (4 * t ^ 3) :=
          by gcongr; exact htail t ht0.le
      _ = ENNReal.ofReal (4 * Real.exp (-t ^ 2 / (2 * D)) * (4 * t ^ 3)) :=
          (ENNReal.ofReal_mul (by positivity)).symm
      _ = ENNReal.ofReal (16 * (t ^ (3 : ℝ) * Real.exp (-(1 / (2 * D)) * t ^ (2 : ℝ)))) := by
          rw [hexp, h3]
          congr 1
          ring
  have hint2 : ∫⁻ t in Ioi (0 : ℝ), ENNReal.ofReal
      (16 * (t ^ (3 : ℝ) * Real.exp (-(1 / (2 * D)) * t ^ (2 : ℝ)))) =
      ENNReal.ofReal (∫ t in Ioi (0 : ℝ), 16 * (t ^ (3 : ℝ) * Real.exp (-(1 / (2 * D)) * t ^ (2 : ℝ)))) :=
    (ofReal_integral_eq_lintegral_ofReal (hFint.const_mul 16)
      ((ae_restrict_mem measurableSet_Ioi).mono fun t ht =>
        (by have := hFnn t ht; positivity : (0 : ℝ) ≤ 16 * (t ^ (3 : ℝ) * Real.exp (-(1 / (2 * D)) * t ^ (2 : ℝ)))))).symm
  have hval : ∫ t in Ioi (0 : ℝ), 16 * (t ^ (3 : ℝ) * Real.exp (-(1 / (2 * D)) * t ^ (2 : ℝ))) =
      32 * D ^ 2 := by
    rw [integral_const_mul, hFval]
    ring
  have hfin : ∫⁻ z, ENNReal.ofReal (z ^ 4) ∂P ≤ ENNReal.ofReal (32 * D ^ 2) := by
    rw [hlc]
    refine hbound.trans ?_
    rw [hint2, hval]
  have hnn : 0 ≤ᵐ[P] (fun z : ℝ => z ^ 4) :=
    Eventually.of_forall fun z => (by positivity : (0 : ℝ) ≤ z ^ 4)
  have hint : Integrable (fun z : ℝ => z ^ 4) P := by
    refine ⟨(by fun_prop : Continuous fun z : ℝ => z ^ 4).aestronglyMeasurable, ?_⟩
    exact (hasFiniteIntegral_iff_ofReal hnn).2 (lt_of_le_of_lt hfin ENNReal.ofReal_lt_top)
  refine ⟨hint, ?_⟩
  have h1 := ofReal_integral_eq_lintegral_ofReal hint hnn
  rw [← h1] at hfin
  exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hfin

/-- The third moment of a centred real Gaussian vanishes (oddness). -/
theorem gaussianReal_third_moment_zero (v : ℝ≥0) :
    ∫ z, z ^ 3 ∂(ProbabilityTheory.gaussianReal 0 v) = 0 := by
  set μ := ProbabilityTheory.gaussianReal 0 v with hμ
  have hneg : μ.map (fun x : ℝ => -x) = μ := by
    rw [hμ, ProbabilityTheory.gaussianReal_map_neg, neg_zero]
  have h1 : ∫ z, z ^ 3 ∂μ = ∫ z, (-z) ^ 3 ∂μ := by
    conv_lhs => rw [← hneg]
    rw [integral_map measurable_neg.aemeasurable
      (by fun_prop : Measurable fun z : ℝ => z ^ 3).aestronglyMeasurable]
  simp only [show ∀ z : ℝ, (-z) ^ 3 = -(z ^ 3) from fun z => by ring, integral_neg] at h1
  linarith

end HRS.ME.FamW
