import HRS.Equilibrium.QuadraticLimit.GibbsAuxA

/-!
# Lemma 7.5, `q08_gibbs_approx`: the replacement chain (prefix `q08gl_`)

Abstract chain of replacements `(a, V, z) → (min a R, V, z) → (min a R, Y, z) → (min b R, Y, z) →
(min b R, Y, z̃)`, with all error terms explicit.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

section Chain

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
variable (P : Measure Ω) [IsProbabilityMeasure P]

theorem q08gl_mink {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    Real.sqrt (∫ ω, (f ω + g ω) ^ 2 ∂P) ≤
      Real.sqrt (∫ ω, f ω ^ 2 ∂P) + Real.sqrt (∫ ω, g ω ^ 2 ∂P) := by
  have hfg : ∫ ω, |f ω| * |g ω| ∂P ≤ Real.sqrt (∫ ω, f ω ^ 2 ∂P) * Real.sqrt (∫ ω, g ω ^ 2 ∂P) :=
    q08gl_cs P f g hf hg
  have hI : Integrable (fun ω => f ω * g ω) P := hf.integrable_mul hg
  have h1 : ∫ ω, f ω * g ω ∂P ≤ ∫ ω, |f ω| * |g ω| ∂P := by
    refine integral_mono hI (hf.abs.integrable_mul hg.abs) fun ω => ?_
    rw [← abs_mul]; exact le_abs_self _
  have e : ∫ ω, (f ω + g ω) ^ 2 ∂P = ∫ ω, f ω ^ 2 ∂P + 2 * ∫ ω, f ω * g ω ∂P + ∫ ω, g ω ^ 2 ∂P := by
    have : ∀ ω, (f ω + g ω) ^ 2 = f ω ^ 2 + 2 * (f ω * g ω) + g ω ^ 2 := fun ω => by ring
    simp_rw [this]
    have h1 : Integrable (fun ω => f ω ^ 2) P := hf.integrable_sq
    have h2 : Integrable (fun ω => 2 * (f ω * g ω)) P := hI.const_mul 2
    have h12 : Integrable (fun ω => f ω ^ 2 + 2 * (f ω * g ω)) P := h1.add h2
    rw [integral_add h12 hg.integrable_sq, integral_add h1 h2, integral_const_mul]
  have hF : 0 ≤ ∫ ω, f ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg (f ω)
  have hG : 0 ≤ ∫ ω, g ω ^ 2 ∂P := integral_nonneg fun ω => sq_nonneg (g ω)
  rw [Real.sqrt_le_left (by positivity)]
  rw [e]
  have sF := Real.sq_sqrt hF
  have sG := Real.sq_sqrt hG
  nlinarith [h1, hfg]

theorem q08gl_memLp_min' {a : Ω → ℝ} (ham : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω) (ha : MemLp a 2 P) (R : ℝ)
    (hR : 0 < R) : MemLp (fun ω => min (a ω) R) 2 P := by
  refine ha.mono (ham.min measurable_const).aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (le_min (ha0 ω) hR.le), abs_of_nonneg (ha0 ω)]
  exact min_le_left _ _

/-- Tail estimates of the truncation. -/
theorem q08gl_trunc_tail {a : Ω → ℝ} (ham : Measurable a) (ha0 : ∀ ω, 0 ≤ a ω) (ha : MemLp a 2 P)
    (ha3 : Integrable (fun ω => a ω ^ 3) P) (R : ℝ) (hR : 0 < R) :
    ∫ ω, |a ω - min (a ω) R| ∂P ≤ (∫ ω, a ω ^ 2 ∂P) / R ∧
      ∫ ω, (a ω - min (a ω) R) ^ 2 ∂P ≤ (∫ ω, a ω ^ 3 ∂P) / R := by
  have hmin : MemLp (fun ω => min (a ω) R) 2 P := q08gl_memLp_min' P ham ha0 ha R hR
  have hd : MemLp (fun ω => a ω - min (a ω) R) 2 P := ha.sub hmin
  constructor
  · have h1 : ∫ ω, |a ω - min (a ω) R| ∂P ≤ ∫ ω, a ω ^ 2 / R ∂P := by
      refine integral_mono (hd.integrable one_le_two).abs ((ha.integrable_sq).div_const R) fun ω => ?_
      rw [abs_of_nonneg (by linarith [min_le_left (a ω) R])]
      exact q08gl_tail1 _ _ (ha0 ω) hR
    rwa [integral_div] at h1
  · have h1 : ∫ ω, (a ω - min (a ω) R) ^ 2 ∂P ≤ ∫ ω, a ω ^ 3 / R ∂P :=
      integral_mono hd.integrable_sq (ha3.div_const R) fun ω => q08gl_tail2 _ _ (ha0 ω) hR
    rwa [integral_div] at h1

theorem q08gl_sq_le (u w : ℝ) : (u - w) ^ 2 ≤ 2 * u ^ 2 + 2 * w ^ 2 := by nlinarith [sq_nonneg (u + w)]

set_option maxHeartbeats 1600000 in
/-- The four-step replacement chain `(a, V, z) → (𝔞, V, z) → (𝔞, Y, z) → (𝔟, Y, z) → (𝔟, Y, z̃)`. -/
theorem q08gl_chain (F : (ι → ℝ) → ℝ) (M K : ℝ) (hFc : Continuous F) (hM : ∀ v, |F v| ≤ M) (hK0 : 0 ≤ K)
    (hF : ∀ v v', |F v - F v'| ≤ K * ∑ i, |v i - v' i|)
    (β R : ℝ) (hβ : 0 ≤ β) (hR : 0 < R)
    (a x y bS : Ω → ℝ) (hxm : Measurable x) (hym : Measurable y)
    (hax : ∀ ω, a ω = Real.exp (-β * x ω)) (hbS : ∀ ω, bS ω = Real.exp (-β * y ω))
    (ha2 : MemLp a 2 P) (ha3 : Integrable (fun ω => a ω ^ 3) P) (A₂ A₃ : ℝ)
    (hA2 : ∫ ω, a ω ^ 2 ∂P ≤ A₂) (hA3 : ∫ ω, a ω ^ 3 ∂P ≤ A₃)
    (z₀ : ℝ) (hz₀ : 0 < z₀) (hz : z₀ ≤ ∫ ω, a ω ∂P)
    (V Y : ι → Ω → ℝ) (hVm : ∀ i, Measurable (V i)) (hYm : ∀ i, Measurable (Y i))
    (hV : ∀ i, MemLp (V i) 2 P) (hY : ∀ i, MemLp (Y i) 2 P)
    (B θ ξ : ℝ) (hB0 : 0 ≤ B) (hB : ∀ i, Real.sqrt (∫ ω, V i ω ^ 2 ∂P) ≤ B)
    (hθ : ∀ i, Real.sqrt (∫ ω, (V i ω - Y i ω) ^ 2 ∂P) ≤ θ) (hθ0 : 0 ≤ θ) (hξ0 : 0 ≤ ξ)
    (hxy : Integrable (fun ω => |x ω - y ω|) P) (hξ : ∫ ω, |x ω - y ω| ∂P ≤ ξ ^ 2)
    (z' ρ : ℝ) (hρ : |∫ ω, min (bS ω) R ∂P - z'| ≤ ρ)
    (hsmall : A₂ / R + β * R * ξ ^ 2 + ρ ≤ z₀ / 2) (hR2 : β * R ^ 2 * ξ ^ 2 ≤ 1) :
    z₀ / 2 ≤ z' ∧ |q08gl_Phi P F a V (∫ ω, a ω ∂P) - q08gl_Phi P F (fun ω => min (bS ω) R) Y z'| ≤
      (K / z₀) * (Fintype.card ι * B * Real.sqrt (A₃ / R)) + (M / z₀) * (A₂ / R) +
      (K / z₀) * (2 * (Fintype.card ι * θ * Real.sqrt A₂)) +
      ((K / z₀) * (Fintype.card ι * (B + θ) * (Real.sqrt β * R * ξ)) + (M / z₀) * (β * R * ξ ^ 2)) +
      (2 * (A₂ / R + β * R * ξ ^ 2 + ρ) / z₀ ^ 2) *
        (M * Real.sqrt (2 * A₂ + 2) + (2 * K / z₀) * (Fintype.card ι * (B + θ) * (2 * A₂ + 2))) := by
  set z : ℝ := ∫ ω, a ω ∂P with hzdef
  have hzpos : 0 < z := lt_of_lt_of_le hz₀ hz
  have ha0 : ∀ ω, 0 ≤ a ω := fun ω => by rw [hax]; exact (Real.exp_pos _).le
  have hb0 : ∀ ω, 0 ≤ bS ω := fun ω => by rw [hbS]; exact (Real.exp_pos _).le
  have ham : Measurable a := by
    have : a = fun ω => Real.exp (-β * x ω) := funext hax
    rw [this]; exact Real.measurable_exp.comp (measurable_const.mul hxm)
  have hbm : Measurable bS := by
    have : bS = fun ω => Real.exp (-β * y ω) := funext hbS
    rw [this]; exact Real.measurable_exp.comp (measurable_const.mul hym)
  set 𝔞 : Ω → ℝ := fun ω => min (a ω) R with h𝔞
  set 𝔟 : Ω → ℝ := fun ω => min (bS ω) R with h𝔟
  have h𝔞0 : ∀ ω, 0 ≤ 𝔞 ω := fun ω => le_min (ha0 ω) hR.le
  have h𝔟0 : ∀ ω, 0 ≤ 𝔟 ω := fun ω => le_min (hb0 ω) hR.le
  have h𝔞m : Measurable 𝔞 := ham.min measurable_const
  have h𝔟m : Measurable 𝔟 := hbm.min measurable_const
  have h𝔞le : ∀ ω, 𝔞 ω ≤ a ω := fun ω => min_le_left _ _
  have h𝔞R : ∀ ω, 𝔞 ω ≤ R := fun ω => min_le_right _ _
  have h𝔟R : ∀ ω, 𝔟 ω ≤ R := fun ω => min_le_right _ _
  have h𝔞2 : MemLp 𝔞 2 P := q08gl_memLp_min' P ham ha0 ha2 R hR
  have h𝔟2 : MemLp 𝔟 2 P := by
    refine (memLp_const R).mono h𝔟m.aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (h𝔟0 ω), abs_of_nonneg hR.le]
    exact h𝔟R ω
  have hA2' : 0 ≤ A₂ := (integral_nonneg fun ω => sq_nonneg (a ω)).trans hA2
  have hcard : (0 : ℝ) ≤ Fintype.card ι := Nat.cast_nonneg _
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM (fun _ => 0))
  -- tail estimates
  obtain ⟨hT1, hT2⟩ := q08gl_trunc_tail P ham ha0 ha2 ha3 R hR
  have hτ1 : ∫ ω, |a ω - 𝔞 ω| ∂P ≤ A₂ / R := hT1.trans (div_le_div_of_nonneg_right hA2 hR.le)
  have hτ2 : ∫ ω, (a ω - 𝔞 ω) ^ 2 ∂P ≤ A₃ / R := hT2.trans (div_le_div_of_nonneg_right hA3 hR.le)
  -- Step 1
  have s1 := q08gl_WC P F M K hFc hM hK0 hF a 𝔞 ha0 ha2 h𝔞2 V hVm hV B (A₂ / R) (A₃ / R) hB hτ1 hτ2 z hzpos
  have e1 : (K / z) * ((1 / z) * (Fintype.card ι * B * Real.sqrt (A₃ / R)) * z) =
      (K / z) * (Fintype.card ι * B * Real.sqrt (A₃ / R)) := by
    congr 1; field_simp
  rw [← hzdef, e1] at s1
  have hKz : K / z ≤ K / z₀ := div_le_div_of_nonneg_left hK0 hz₀ hz
  have hMz : M / z ≤ M / z₀ := div_le_div_of_nonneg_left hMnn hz₀ hz
  -- Step 2
  have hint𝔞 : ∫ ω, 𝔞 ω ∂P ≤ z := integral_mono (h𝔞2.integrable one_le_two) (ha2.integrable one_le_two) h𝔞le
  have h𝔞sq : ∫ ω, 𝔞 ω ^ 2 ∂P ≤ A₂ := by
    refine le_trans (integral_mono h𝔞2.integrable_sq ha2.integrable_sq fun ω => ?_) hA2
    exact pow_le_pow_left₀ (h𝔞0 ω) (h𝔞le ω) 2
  have s2 := q08gl_VC P F M K hFc hM hK0 hF 𝔞 h𝔞0 h𝔞2 A₂ h𝔞sq V Y hVm hYm hV hY θ hθ z hzpos
  have hα2 : 0 ≤ Fintype.card ι * θ * Real.sqrt A₂ := by positivity
  have s2' : |q08gl_Phi P F 𝔞 V z - q08gl_Phi P F 𝔞 Y z| ≤ (K / z₀) * (2 * (Fintype.card ι * θ * Real.sqrt A₂)) := by
    refine s2.trans ?_
    have h1 : (Fintype.card ι * θ * Real.sqrt A₂ +
        (1 / z) * (Fintype.card ι * θ * Real.sqrt A₂) * ∫ ω, 𝔞 ω ∂P) ≤
        2 * (Fintype.card ι * θ * Real.sqrt A₂) := by
      have : (1 / z) * (Fintype.card ι * θ * Real.sqrt A₂) * ∫ ω, 𝔞 ω ∂P ≤
          (1 / z) * (Fintype.card ι * θ * Real.sqrt A₂) * z :=
        mul_le_mul_of_nonneg_left hint𝔞 (by positivity)
      have e : (1 / z) * (Fintype.card ι * θ * Real.sqrt A₂) * z = Fintype.card ι * θ * Real.sqrt A₂ := by
        field_simp
      linarith
    calc (K / z) * (Fintype.card ι * θ * Real.sqrt A₂ +
        (1 / z) * (Fintype.card ι * θ * Real.sqrt A₂) * ∫ ω, 𝔞 ω ∂P)
        ≤ (K / z) * (2 * (Fintype.card ι * θ * Real.sqrt A₂)) := mul_le_mul_of_nonneg_left h1 (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hKz (by positivity)
  -- Step 3
  have hpt : ∀ ω, |𝔞 ω - 𝔟 ω| ≤ β * R * |x ω - y ω| := fun ω => by
    simp only [h𝔞, h𝔟]
    rw [hax ω, hbS ω]
    exact q08gl_trunc_exp_lip β R (x ω) (y ω) hβ hR
  have hd𝔞𝔟 : MemLp (fun ω => 𝔞 ω - 𝔟 ω) 2 P := h𝔞2.sub h𝔟2
  have hτ1' : ∫ ω, |𝔞 ω - 𝔟 ω| ∂P ≤ β * R * ξ ^ 2 := by
    calc ∫ ω, |𝔞 ω - 𝔟 ω| ∂P ≤ ∫ ω, β * R * |x ω - y ω| ∂P :=
          integral_mono (hd𝔞𝔟.integrable one_le_two).abs (hxy.const_mul _) hpt
      _ = β * R * ∫ ω, |x ω - y ω| ∂P := integral_const_mul _ _
      _ ≤ β * R * ξ ^ 2 := mul_le_mul_of_nonneg_left hξ (by positivity)
  have hbd : ∀ ω, |𝔞 ω - 𝔟 ω| ≤ R := fun ω =>
    abs_sub_le_iff.2 ⟨by linarith [h𝔞R ω, h𝔟0 ω], by linarith [h𝔟R ω, h𝔞0 ω]⟩
  have hτ2' : ∫ ω, (𝔞 ω - 𝔟 ω) ^ 2 ∂P ≤ (Real.sqrt β * R * ξ) ^ 2 := by
    have e : (Real.sqrt β * R * ξ) ^ 2 = R * (β * R * ξ ^ 2) := by
      rw [mul_pow, mul_pow, Real.sq_sqrt hβ]; ring
    rw [e]
    calc ∫ ω, (𝔞 ω - 𝔟 ω) ^ 2 ∂P ≤ ∫ ω, R * |𝔞 ω - 𝔟 ω| ∂P := by
          refine integral_mono hd𝔞𝔟.integrable_sq ((hd𝔞𝔟.integrable one_le_two).abs.const_mul _) fun ω => ?_
          have : (𝔞 ω - 𝔟 ω) ^ 2 = |𝔞 ω - 𝔟 ω| * |𝔞 ω - 𝔟 ω| := by rw [← sq, sq_abs]
          rw [this, mul_comm R]
          exact mul_le_mul_of_nonneg_left (hbd ω) (abs_nonneg _)
      _ = R * ∫ ω, |𝔞 ω - 𝔟 ω| ∂P := integral_const_mul _ _
      _ ≤ _ := mul_le_mul_of_nonneg_left hτ1' hR.le
  have hYB : ∀ i, Real.sqrt (∫ ω, Y i ω ^ 2 ∂P) ≤ B + θ := by
    intro i
    have h := q08gl_mink P (hV i) ((hY i).sub (hV i))
    have e1 : ∫ ω, (V i ω + (Y i ω - V i ω)) ^ 2 ∂P = ∫ ω, Y i ω ^ 2 ∂P := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_); simp only; ring
    have e2 : ∫ ω, (Y i ω - V i ω) ^ 2 ∂P = ∫ ω, (V i ω - Y i ω) ^ 2 ∂P := by
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_); simp only; ring
    simp only [Pi.sub_apply] at h
    rw [e1, e2] at h
    exact h.trans (add_le_add (hB i) (hθ i))
  have s3 := q08gl_WC P F M K hFc hM hK0 hF 𝔞 𝔟 h𝔞0 h𝔞2 h𝔟2 Y hYm hY (B + θ) (β * R * ξ ^ 2)
    ((Real.sqrt β * R * ξ) ^ 2) hYB hτ1' hτ2' z hzpos
  rw [Real.sqrt_sq (by positivity)] at s3
  have s3' : |q08gl_Phi P F 𝔞 Y z - q08gl_Phi P F 𝔟 Y z| ≤
      (K / z₀) * (Fintype.card ι * (B + θ) * (Real.sqrt β * R * ξ)) + (M / z₀) * (β * R * ξ ^ 2) := by
    refine s3.trans (add_le_add ?_ (mul_le_mul_of_nonneg_right hMz (by positivity)))
    have hX : 0 ≤ Fintype.card ι * (B + θ) * (Real.sqrt β * R * ξ) := by positivity
    have : (1 / z) * (Fintype.card ι * (B + θ) * (Real.sqrt β * R * ξ)) * ∫ ω, 𝔞 ω ∂P ≤
        (1 / z) * (Fintype.card ι * (B + θ) * (Real.sqrt β * R * ξ)) * z :=
      mul_le_mul_of_nonneg_left hint𝔞 (by positivity)
    have e : (1 / z) * (Fintype.card ι * (B + θ) * (Real.sqrt β * R * ξ)) * z =
        Fintype.card ι * (B + θ) * (Real.sqrt β * R * ξ) := by field_simp
    calc (K / z) * ((1 / z) * (Fintype.card ι * (B + θ) * (Real.sqrt β * R * ξ)) * ∫ ω, 𝔞 ω ∂P)
        ≤ (K / z) * (Fintype.card ι * (B + θ) * (Real.sqrt β * R * ξ)) :=
          mul_le_mul_of_nonneg_left (this.trans (le_of_eq e)) (by positivity)
      _ ≤ _ := mul_le_mul_of_nonneg_right hKz hX
  -- Step 4
  have hz1 : z - ∫ ω, 𝔞 ω ∂P ≤ A₂ / R := by
    have : z - ∫ ω, 𝔞 ω ∂P = ∫ ω, |a ω - 𝔞 ω| ∂P := by
      rw [hzdef, ← integral_sub (ha2.integrable one_le_two) (h𝔞2.integrable one_le_two)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only
      rw [abs_of_nonneg (by linarith [h𝔞le ω])]
    rw [this]; exact hτ1
  have hz2 : |∫ ω, 𝔞 ω ∂P - ∫ ω, 𝔟 ω ∂P| ≤ β * R * ξ ^ 2 := by
    rw [← integral_sub (h𝔞2.integrable one_le_two) (h𝔟2.integrable one_le_two)]
    exact (abs_integral_le_integral_abs).trans hτ1'
  have hσ : |z - z'| ≤ A₂ / R + β * R * ξ ^ 2 + ρ := by
    have h3 : |∫ ω, 𝔟 ω ∂P - z'| ≤ ρ := hρ
    have : z - z' = (z - ∫ ω, 𝔞 ω ∂P) + (∫ ω, 𝔞 ω ∂P - ∫ ω, 𝔟 ω ∂P) + (∫ ω, 𝔟 ω ∂P - z') := by ring
    rw [this]
    have h1 : |z - ∫ ω, 𝔞 ω ∂P| ≤ A₂ / R := by
      rw [abs_of_nonneg (by linarith [hint𝔞])]; exact hz1
    refine (abs_add_le _ _).trans ((add_le_add (abs_add_le _ _) le_rfl).trans ?_)
    linarith
  have hz'pos : z₀ / 2 ≤ z' := by
    have := (abs_le.1 hσ).2
    linarith
  have hz'p : 0 < z' := lt_of_lt_of_le (by positivity) hz'pos
  have hint𝔟sq : ∫ ω, 𝔟 ω ^ 2 ∂P ≤ 2 * A₂ + 2 := by
    have h1 : ∫ ω, 𝔟 ω ^ 2 ∂P ≤ ∫ ω, (2 * 𝔞 ω ^ 2 + 2 * (𝔞 ω - 𝔟 ω) ^ 2) ∂P := by
      refine integral_mono h𝔟2.integrable_sq ((h𝔞2.integrable_sq.const_mul 2).add (hd𝔞𝔟.integrable_sq.const_mul 2))
        fun ω => ?_
      have := q08gl_sq_le (𝔞 ω) (𝔞 ω - 𝔟 ω)
      rwa [show 𝔞 ω - (𝔞 ω - 𝔟 ω) = 𝔟 ω by ring] at this
    refine h1.trans ?_
    rw [integral_add (h𝔞2.integrable_sq.const_mul 2) (hd𝔞𝔟.integrable_sq.const_mul 2), integral_const_mul,
      integral_const_mul]
    have : (Real.sqrt β * R * ξ) ^ 2 ≤ 1 := by
      have e : (Real.sqrt β * R * ξ) ^ 2 = β * R ^ 2 * ξ ^ 2 := by
        rw [mul_pow, mul_pow, Real.sq_sqrt hβ]
      rw [e]; exact hR2
    nlinarith [h𝔞sq, hτ2']
  have hint𝔟 : ∫ ω, 𝔟 ω ∂P ≤ Real.sqrt (2 * A₂ + 2) := by
    have := q08gl_integral_le_sqrt P h𝔟2
    have e : ∫ ω, |𝔟 ω| ∂P = ∫ ω, 𝔟 ω ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => abs_of_nonneg (h𝔟0 ω))
    rw [e] at this
    exact this.trans (Real.sqrt_le_sqrt hint𝔟sq)
  have hint𝔟0 : 0 ≤ ∫ ω, 𝔟 ω ∂P := integral_nonneg h𝔟0
  have hYb : ∀ i, |∫ ω, Y i ω * 𝔟 ω ∂P| ≤ (B + θ) * Real.sqrt (2 * A₂ + 2) := by
    intro i
    refine (abs_integral_le_integral_abs).trans ?_
    have := q08gl_cs P (Y i) 𝔟 (hY i) h𝔟2
    have e : ∫ ω, |Y i ω * 𝔟 ω| ∂P = ∫ ω, |Y i ω| * |𝔟 ω| ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => abs_mul _ _)
    rw [e]
    refine this.trans (mul_le_mul (hYB i) (Real.sqrt_le_sqrt hint𝔟sq) (Real.sqrt_nonneg _) (by positivity))
  have s4 := q08gl_ST_z P F M K hFc hM hK0 hF 𝔟 h𝔟0 (h𝔟2.integrable one_le_two) Y hYm z z' hzpos hz'p
  have hinv : |1 / z - 1 / z'| ≤ 2 * (A₂ / R + β * R * ξ ^ 2 + ρ) / z₀ ^ 2 := by
    rw [div_sub_div _ _ hzpos.ne' hz'p.ne', abs_div, abs_of_pos (mul_pos hzpos hz'p)]
    rw [show |1 * z' - z * 1| = |z - z'| by rw [one_mul, mul_one, abs_sub_comm]]
    rw [div_le_div_iff₀ (mul_pos hzpos hz'p) (by positivity)]
    have h1 : z₀ * (z₀ / 2) ≤ z * z' := mul_le_mul hz hz'pos (by positivity) hzpos.le
    have h2 : 0 ≤ A₂ / R + β * R * ξ ^ 2 + ρ := (abs_nonneg _).trans hσ
    nlinarith [mul_le_mul hσ h1 (by positivity) h2]
  have hSum : ∑ i, |∫ ω, Y i ω * 𝔟 ω ∂P| ≤ Fintype.card ι * ((B + θ) * Real.sqrt (2 * A₂ + 2)) := by
    calc ∑ i, |∫ ω, Y i ω * 𝔟 ω ∂P| ≤ ∑ _i : ι, (B + θ) * Real.sqrt (2 * A₂ + 2) :=
          Finset.sum_le_sum fun i _ => hYb i
      _ = _ := by simp
  have hAb : 0 ≤ 2 * A₂ + 2 := by linarith
  have hsq : Real.sqrt (2 * A₂ + 2) * Real.sqrt (2 * A₂ + 2) = 2 * A₂ + 2 := Real.mul_self_sqrt hAb
  have hK' : K / z' ≤ 2 * K / z₀ := by
    rw [div_le_div_iff₀ hz'p hz₀]; nlinarith
  have s4' : |q08gl_Phi P F 𝔟 Y z - q08gl_Phi P F 𝔟 Y z'| ≤
      (2 * (A₂ / R + β * R * ξ ^ 2 + ρ) / z₀ ^ 2) *
        (M * Real.sqrt (2 * A₂ + 2) + (2 * K / z₀) * (Fintype.card ι * (B + θ) * (2 * A₂ + 2))) := by
    refine s4.trans ?_
    have hSp : 0 ≤ ∑ i, |∫ ω, Y i ω * 𝔟 ω ∂P| := Finset.sum_nonneg fun _ _ => abs_nonneg _
    refine mul_le_mul hinv ?_ (add_nonneg (mul_nonneg hMnn hint𝔟0)
      (mul_nonneg (mul_nonneg (div_nonneg hK0 hz'p.le) hSp) hint𝔟0))
      (div_nonneg (mul_nonneg zero_le_two ((abs_nonneg _).trans hσ)) (sq_nonneg _))
    have h1 : (K / z') * (∑ i, |∫ ω, Y i ω * 𝔟 ω ∂P|) * ∫ ω, 𝔟 ω ∂P ≤
        (2 * K / z₀) * (Fintype.card ι * ((B + θ) * Real.sqrt (2 * A₂ + 2))) * Real.sqrt (2 * A₂ + 2) :=
      mul_le_mul (mul_le_mul hK' hSum hSp (by positivity)) hint𝔟 hint𝔟0 (by positivity)
    have e : (2 * K / z₀) * (Fintype.card ι * ((B + θ) * Real.sqrt (2 * A₂ + 2))) * Real.sqrt (2 * A₂ + 2) =
        (2 * K / z₀) * (Fintype.card ι * (B + θ) * (2 * A₂ + 2)) := by
      have : (2 * K / z₀) * (Fintype.card ι * ((B + θ) * Real.sqrt (2 * A₂ + 2))) * Real.sqrt (2 * A₂ + 2) =
          (2 * K / z₀) * (Fintype.card ι * (B + θ)) * (Real.sqrt (2 * A₂ + 2) * Real.sqrt (2 * A₂ + 2)) := by ring
      rw [this, hsq]; ring
    have h2 : M * ∫ ω, 𝔟 ω ∂P ≤ M * Real.sqrt (2 * A₂ + 2) := mul_le_mul_of_nonneg_left hint𝔟 hMnn
    linarith
  -- combine
  have s1' : |q08gl_Phi P F a V z - q08gl_Phi P F 𝔞 V z| ≤
      (K / z₀) * (Fintype.card ι * B * Real.sqrt (A₃ / R)) + (M / z₀) * (A₂ / R) :=
    s1.trans (add_le_add (mul_le_mul_of_nonneg_right hKz (by positivity))
      (mul_le_mul_of_nonneg_right hMz (div_nonneg hA2' hR.le)))
  have t1 := abs_sub_le (q08gl_Phi P F a V z) (q08gl_Phi P F 𝔞 V z) (q08gl_Phi P F 𝔟 Y z')
  have t2 := abs_sub_le (q08gl_Phi P F 𝔞 V z) (q08gl_Phi P F 𝔞 Y z) (q08gl_Phi P F 𝔟 Y z')
  have t3 := abs_sub_le (q08gl_Phi P F 𝔞 Y z) (q08gl_Phi P F 𝔟 Y z) (q08gl_Phi P F 𝔟 Y z')
  exact ⟨hz'pos, by linarith⟩

end Chain

end HRS.Q08

end
