import HRS.Equilibrium.QuadraticLimit.GibbsAuxB

/-!
# Lemma 7.5, `q08_gibbs_approx`: passage to the limit `N → ∞` through the finite-rank CLT
(prefix `q08gl_`)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q08

section Lim

variable {ι : Type*} [Fintype ι] {m : ℕ}

/-- If `S_N → γ` in the sense of integrals of continuous functions of quadratic growth, the tilted
functional of continuous finite-rank functionals converges. -/
theorem q08gl_lim {Ω : ℕ → Type} [∀ N, MeasurableSpace (Ω N)] (P : ∀ N, Measure (Ω N))
    [∀ N, IsProbabilityMeasure (P N)] (S : ∀ N, Ω N → EuclideanSpace ℝ (Fin m))
    (hS : ∀ N, Measurable (S N)) (γ : Measure (EuclideanSpace ℝ (Fin m))) [IsProbabilityMeasure γ]
    (hclt : ∀ Ψ : EuclideanSpace ℝ (Fin m) → ℝ, Continuous Ψ → ∀ C₀ : ℝ,
      (∀ s, |Ψ s| ≤ C₀ * (1 + ‖s‖ ^ 2)) →
        Tendsto (fun N => ∫ ω, Ψ (S N ω) ∂(P N)) atTop (𝓝 (∫ s, Ψ s ∂γ)))
    (F : (ι → ℝ) → ℝ) (M K : ℝ) (hFc : Continuous F) (hM : ∀ v, |F v| ≤ M) (hK0 : 0 ≤ K)
    (hF : ∀ v v', |F v - F v'| ≤ K * ∑ i, |v i - v' i|)
    (w : EuclideanSpace ℝ (Fin m) → ℝ) (hwc : Continuous w) (R : ℝ) (hw0 : ∀ s, 0 ≤ w s)
    (hwR : ∀ s, w s ≤ R)
    (f : ι → EuclideanSpace ℝ (Fin m) → ℝ) (hfc : ∀ i, Continuous (f i))
    (Cf : ℝ) (hCf : 0 ≤ Cf) (hf : ∀ i s, |f i s| ≤ Cf * (1 + ‖s‖ ^ 2)) (z : ℝ) (hz : 0 < z) :
    Tendsto (fun N => q08gl_Phi (P N) F (fun ω => w (S N ω)) (fun i ω => f i (S N ω)) z) atTop
      (𝓝 (q08gl_Phi γ F w f z)) := by
  have hR0 : 0 ≤ R := (hw0 0).trans (hwR 0)
  have hM0 : 0 ≤ M := (abs_nonneg _).trans (hM (fun _ => 0))
  set c : ι → ℝ := fun i => (1 / z) * ∫ s, f i s * w s ∂γ with hc
  set cN : ℕ → ι → ℝ := fun N i => (1 / z) * ∫ ω, f i (S N ω) * w (S N ω) ∂(P N) with hcN
  have hcT : ∀ i, Tendsto (fun N => cN N i) atTop (𝓝 (c i)) := by
    intro i
    have := hclt (fun s => f i s * w s) ((hfc i).mul hwc) (Cf * R) (fun s => by
      rw [abs_mul]
      have h1 : |w s| ≤ R := by rw [abs_of_nonneg (hw0 s)]; exact hwR s
      calc |f i s| * |w s| ≤ (Cf * (1 + ‖s‖ ^ 2)) * R := mul_le_mul (hf i s) h1 (abs_nonneg _) (by positivity)
        _ = Cf * R * (1 + ‖s‖ ^ 2) := by ring)
    exact this.const_mul (1 / z)
  have hT : Tendsto (fun N => ∫ ω, F (fun i => f i (S N ω) - c i) * w (S N ω) ∂(P N)) atTop
      (𝓝 (∫ s, F (fun i => f i s - c i) * w s ∂γ)) := by
    refine hclt (fun s => F (fun i => f i s - c i) * w s)
      ((hFc.comp (continuous_pi fun i => (hfc i).sub continuous_const)).mul hwc) (M * R) (fun s => ?_)
    rw [abs_mul]
    have h1 : |w s| ≤ R := by rw [abs_of_nonneg (hw0 s)]; exact hwR s
    calc |F (fun i => f i s - c i)| * |w s| ≤ M * R := mul_le_mul (hM _) h1 (abs_nonneg _) hM0
      _ ≤ M * R * (1 + ‖s‖ ^ 2) := by
          have : (1 : ℝ) ≤ 1 + ‖s‖ ^ 2 := by nlinarith [sq_nonneg ‖s‖]
          nlinarith [mul_nonneg hM0 hR0]
  have hlim1 : Tendsto (fun N => (1 / z) * ∫ ω, F (fun i => f i (S N ω) - c i) * w (S N ω) ∂(P N)) atTop
      (𝓝 (q08gl_Phi γ F w f z)) := by
    have := hT.const_mul (1 / z)
    simpa [q08gl_Phi, hc] using this
  refine tendsto_of_tendsto_of_dist hlim1 ?_
  -- distance estimate
  have hdist : ∀ N, dist ((1 / z) * ∫ ω, F (fun i => f i (S N ω) - c i) * w (S N ω) ∂(P N))
      (q08gl_Phi (P N) F (fun ω => w (S N ω)) (fun i ω => f i (S N ω)) z) ≤
      (1 / z) * (K * R * ∑ i, |cN N i - c i|) := by
    intro N
    have hmeasF : ∀ c' : ι → ℝ, Measurable (fun ω => F (fun i => f i (S N ω) - c' i) * w (S N ω)) := fun c' =>
      (hFc.measurable.comp (measurable_pi_iff.2 fun i => ((hfc i).measurable.comp (hS N)).sub_const _)).mul
        (hwc.measurable.comp (hS N))
    have hbdd : ∀ c' : ι → ℝ, Integrable (fun ω => F (fun i => f i (S N ω) - c' i) * w (S N ω)) (P N) := by
      intro c'
      refine Integrable.of_bound (C := M * R) (hmeasF c').aestronglyMeasurable (Eventually.of_forall fun ω => ?_)
      rw [Real.norm_eq_abs, abs_mul]
      have h1 : |w (S N ω)| ≤ R := by rw [abs_of_nonneg (hw0 _)]; exact hwR _
      exact mul_le_mul (hM _) h1 (abs_nonneg _) hM0
    unfold q08gl_Phi
    rw [Real.dist_eq, ← mul_sub, abs_mul, abs_of_pos (by positivity : (0 : ℝ) < 1 / z)]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    rw [← integral_sub (hbdd c) (hbdd (cN N))]
    refine (abs_integral_le_integral_abs).trans ?_
    calc ∫ ω, |F (fun i => f i (S N ω) - c i) * w (S N ω) - F (fun i => f i (S N ω) - cN N i) * w (S N ω)| ∂(P N)
        ≤ ∫ ω, K * R * ∑ i, |cN N i - c i| ∂(P N) := by
          refine integral_mono_of_nonneg (Eventually.of_forall fun ω => abs_nonneg _) (integrable_const _)
            (Eventually.of_forall fun ω => ?_)
          dsimp only
          rw [← sub_mul, abs_mul]
          have h1 : |w (S N ω)| ≤ R := by rw [abs_of_nonneg (hw0 _)]; exact hwR _
          have h2 := hF (fun i => f i (S N ω) - c i) (fun i => f i (S N ω) - cN N i)
          have h3 : ∑ i, |(f i (S N ω) - c i) - (f i (S N ω) - cN N i)| = ∑ i, |cN N i - c i| := by
            refine Finset.sum_congr rfl fun i _ => ?_
            rw [show (f i (S N ω) - c i) - (f i (S N ω) - cN N i) = cN N i - c i by ring]
          rw [h3] at h2
          calc |F (fun i => f i (S N ω) - c i) - F (fun i => f i (S N ω) - cN N i)| * |w (S N ω)|
              ≤ (K * ∑ i, |cN N i - c i|) * R := mul_le_mul h2 h1 (abs_nonneg _) (by positivity)
            _ = K * R * ∑ i, |cN N i - c i| := by ring
      _ = K * R * ∑ i, |cN N i - c i| := by simp
  have hlimsum : Tendsto (fun N => (1 / z) * (K * R * ∑ i, |cN N i - c i|)) atTop (𝓝 0) := by
    have : Tendsto (fun N => ∑ i, |cN N i - c i|) atTop (𝓝 0) := by
      have h := tendsto_finset_sum (Finset.univ : Finset ι) fun i _ =>
        ((hcT i).sub_const (c i)).abs
      simpa using h
    have := (this.const_mul (K * R)).const_mul (1 / z)
    simpa using this
  exact squeeze_zero (fun N => dist_nonneg) hdist hlimsum

end Lim

section Gstep

variable {Ω : Type*} [MeasurableSpace Ω] {ι : Type*} [Fintype ι]
variable (P : Measure Ω) [IsProbabilityMeasure P]

set_option maxHeartbeats 800000 in
/-- Removing the truncation of the limit weight. -/
theorem q08gl_gstep (F : (ι → ℝ) → ℝ) (M K : ℝ) (hFc : Continuous F) (hM : ∀ v, |F v| ≤ M) (hK0 : 0 ≤ K)
    (hF : ∀ v v', |F v - F v'| ≤ K * ∑ i, |v i - v' i|)
    (b : Ω → ℝ) (hb0 : ∀ ω, 0 ≤ b ω) (hbm : Measurable b) (hb2 : MemLp b 2 P)
    (hb3 : Integrable (fun ω => b ω ^ 3) P) (B₂ B₃ : ℝ) (hB2 : ∫ ω, b ω ^ 2 ∂P ≤ B₂)
    (hB3 : ∫ ω, b ω ^ 3 ∂P ≤ B₃) (R : ℝ) (hR : 0 < R) (z₀ : ℝ) (hz₀ : 0 < z₀)
    (hz : z₀ / 2 ≤ ∫ ω, min (b ω) R ∂P)
    (f : ι → Ω → ℝ) (hfm : ∀ i, Measurable (f i)) (hf : ∀ i, MemLp (f i) 2 P) (Bf : ℝ)
    (hBf0 : 0 ≤ Bf) (hBf : ∀ i, Real.sqrt (∫ ω, f i ω ^ 2 ∂P) ≤ Bf) :
    |q08gl_Phi P F (fun ω => min (b ω) R) f (∫ ω, min (b ω) R ∂P) -
        q08gl_Phi P F b f (∫ ω, b ω ∂P)| ≤
      (2 * K / z₀) * ((2 / z₀) * (Fintype.card ι * Bf * Real.sqrt (B₃ / R)) * Real.sqrt B₂) +
        (2 * M / z₀) * (B₂ / R) +
      (4 * B₂ / (R * z₀ ^ 2)) * (M * Real.sqrt B₂ + (2 * K / z₀) * (Fintype.card ι * Bf * B₂)) := by
  set z' : ℝ := ∫ ω, min (b ω) R ∂P with hz'
  set zb : ℝ := ∫ ω, b ω ∂P with hzb
  have hz'p : 0 < z' := lt_of_lt_of_le (by positivity) hz
  have hMnn : 0 ≤ M := (abs_nonneg _).trans (hM (fun _ => 0))
  have hB20 : 0 ≤ B₂ := (integral_nonneg fun ω => sq_nonneg (b ω)).trans hB2
  have hb𝔟2 : MemLp (fun ω => min (b ω) R) 2 P := q08gl_memLp_min' P hbm hb0 hb2 R hR
  obtain ⟨hT1, hT2⟩ := q08gl_trunc_tail P hbm hb0 hb2 hb3 R hR
  have hτ1 : ∫ ω, |b ω - min (b ω) R| ∂P ≤ B₂ / R := hT1.trans (div_le_div_of_nonneg_right hB2 hR.le)
  have hτ2 : ∫ ω, (b ω - min (b ω) R) ^ 2 ∂P ≤ B₃ / R := hT2.trans (div_le_div_of_nonneg_right hB3 hR.le)
  have hzbz : zb - z' ≤ B₂ / R := by
    have : zb - z' = ∫ ω, |b ω - min (b ω) R| ∂P := by
      rw [hzb, hz', ← integral_sub (hb2.integrable one_le_two) (hb𝔟2.integrable one_le_two)]
      refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
      simp only
      rw [abs_of_nonneg (by linarith [min_le_left (b ω) R])]
    rw [this]; exact hτ1
  have hzzb : z' ≤ zb := integral_mono (hb𝔟2.integrable one_le_two) (hb2.integrable one_le_two)
    fun ω => min_le_left _ _
  have hzbp : 0 < zb := lt_of_lt_of_le hz'p hzzb
  have hint_b : zb ≤ Real.sqrt B₂ := by
    have := q08gl_integral_le_sqrt P hb2
    have e : ∫ ω, |b ω| ∂P = zb :=
      integral_congr_ae (Eventually.of_forall fun ω => abs_of_nonneg (hb0 ω))
    rw [e] at this
    exact this.trans (Real.sqrt_le_sqrt hB2)
  -- (i) removing the truncation of the weight
  have sA := q08gl_WC P F M K hFc hM hK0 hF b (fun ω => min (b ω) R) hb0 hb2 hb𝔟2 f hfm hf Bf (B₂ / R) (B₃ / R)
    hBf hτ1 hτ2 z' hz'p
  -- (ii) change of the normalising constant
  have sB := q08gl_ST_z P F M K hFc hM hK0 hF b hb0 (hb2.integrable one_le_two) f hfm z' zb hz'p hzbp
  have hinv : |1 / z' - 1 / zb| ≤ 4 * B₂ / (R * z₀ ^ 2) := by
    rw [div_sub_div _ _ hz'p.ne' hzbp.ne', abs_div, abs_of_pos (mul_pos hz'p hzbp)]
    rw [show |1 * zb - z' * 1| = zb - z' by rw [one_mul, mul_one, abs_of_nonneg (by linarith)]]
    rw [div_le_div_iff₀ (mul_pos hz'p hzbp) (by positivity)]
    have h1 : (z₀ / 2) * (z₀ / 2) ≤ z' * zb := mul_le_mul hz (hz.trans hzzb) (by positivity) hz'p.le
    have h2 : (zb - z') * (R * z₀ ^ 2) ≤ B₂ / R * (R * z₀ ^ 2) := mul_le_mul_of_nonneg_right hzbz (by positivity)
    have e : B₂ / R * (R * z₀ ^ 2) = B₂ * z₀ ^ 2 := by field_simp
    nlinarith [mul_le_mul_of_nonneg_left h1 hB20]
  have hfb : ∀ i, |∫ ω, f i ω * b ω ∂P| ≤ Bf * Real.sqrt B₂ := by
    intro i
    refine (abs_integral_le_integral_abs).trans ?_
    have := q08gl_cs P (f i) b (hf i) hb2
    have e : ∫ ω, |f i ω * b ω| ∂P = ∫ ω, |f i ω| * |b ω| ∂P :=
      integral_congr_ae (Eventually.of_forall fun ω => abs_mul _ _)
    rw [e]
    exact this.trans (mul_le_mul (hBf i) (Real.sqrt_le_sqrt hB2) (Real.sqrt_nonneg _) ((Real.sqrt_nonneg _).trans (hBf i)))
  have hSum : ∑ i, |∫ ω, f i ω * b ω ∂P| ≤ Fintype.card ι * (Bf * Real.sqrt B₂) := by
    calc ∑ i, |∫ ω, f i ω * b ω ∂P| ≤ ∑ _i : ι, Bf * Real.sqrt B₂ := Finset.sum_le_sum fun i _ => hfb i
      _ = _ := by simp
  have hsq : Real.sqrt B₂ * Real.sqrt B₂ = B₂ := Real.mul_self_sqrt hB20
  have hKz : K / zb ≤ 2 * K / z₀ := by
    rw [div_le_div_iff₀ hzbp hz₀]; nlinarith [hz.trans hzzb]
  have hbint0 : 0 ≤ zb := hzbp.le
  have hSp : 0 ≤ ∑ i, |∫ ω, f i ω * b ω ∂P| := Finset.sum_nonneg fun _ _ => abs_nonneg _
  have sB' : |q08gl_Phi P F b f z' - q08gl_Phi P F b f zb| ≤
      (4 * B₂ / (R * z₀ ^ 2)) * (M * Real.sqrt B₂ + (2 * K / z₀) * (Fintype.card ι * Bf * B₂)) := by
    refine sB.trans ?_
    refine mul_le_mul hinv ?_ (add_nonneg (mul_nonneg hMnn hbint0)
      (mul_nonneg (mul_nonneg (div_nonneg hK0 hzbp.le) hSp) hbint0)) (by positivity)
    have h1 : (K / zb) * (∑ i, |∫ ω, f i ω * b ω ∂P|) * ∫ ω, b ω ∂P ≤
        (2 * K / z₀) * (Fintype.card ι * (Bf * Real.sqrt B₂)) * Real.sqrt B₂ :=
      mul_le_mul (mul_le_mul hKz hSum hSp (by positivity)) hint_b hbint0 (by positivity)
    have e : (2 * K / z₀) * (Fintype.card ι * (Bf * Real.sqrt B₂)) * Real.sqrt B₂ =
        (2 * K / z₀) * (Fintype.card ι * Bf * B₂) := by
      have : (2 * K / z₀) * (Fintype.card ι * (Bf * Real.sqrt B₂)) * Real.sqrt B₂ =
          (2 * K / z₀) * (Fintype.card ι * Bf) * (Real.sqrt B₂ * Real.sqrt B₂) := by ring
      rw [this, hsq]; ring
    have h2 : M * ∫ ω, b ω ∂P ≤ M * Real.sqrt B₂ := mul_le_mul_of_nonneg_left hint_b hMnn
    linarith
  have hK2 : K / z' ≤ 2 * K / z₀ := by
    rw [div_le_div_iff₀ hz'p hz₀]; nlinarith
  have hM2 : M / z' ≤ 2 * M / z₀ := by
    rw [div_le_div_iff₀ hz'p hz₀]; nlinarith
  have sA' : |q08gl_Phi P F b f z' - q08gl_Phi P F (fun ω => min (b ω) R) f z'| ≤
      (2 * K / z₀) * ((2 / z₀) * (Fintype.card ι * Bf * Real.sqrt (B₃ / R)) * Real.sqrt B₂) +
        (2 * M / z₀) * (B₂ / R) := by
    refine sA.trans (add_le_add ?_ (mul_le_mul_of_nonneg_right hM2 (div_nonneg hB20 hR.le)))
    have h1 : (1 / z') ≤ 2 / z₀ := by
      rw [div_le_div_iff₀ hz'p hz₀]; nlinarith
    have hX : 0 ≤ Fintype.card ι * Bf * Real.sqrt (B₃ / R) := by positivity
    have h2 : (1 / z') * (Fintype.card ι * Bf * Real.sqrt (B₃ / R)) * ∫ ω, b ω ∂P ≤
        (2 / z₀) * (Fintype.card ι * Bf * Real.sqrt (B₃ / R)) * Real.sqrt B₂ :=
      mul_le_mul (mul_le_mul_of_nonneg_right h1 hX) hint_b hbint0 (by positivity)
    exact mul_le_mul hK2 h2 (by positivity) (by positivity)
  have t1 := abs_sub_le (q08gl_Phi P F (fun ω => min (b ω) R) f z') (q08gl_Phi P F b f z') (q08gl_Phi P F b f zb)
  have t2 := abs_sub_comm (q08gl_Phi P F (fun ω => min (b ω) R) f z') (q08gl_Phi P F b f z')
  linarith

end Gstep

end HRS.Q08

end
