import Mathlib
import HRS.MC.S7E4Aux2

/-!
# Packet `s7_E4_normalized_clt`, file 3: abstract normalised CLT

`L^2` norm calculus, and the statement: if `Q_n` is `L^2`-approximated, at every accuracy, by variables with the
law of `(1/2) sum a_k (g_k^2 - 1)` (`|a_k| <= Lam`), and `E Q_n^2 -> infinity`, then `Q_n / sigma_n => N(0,1)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.E4A3

open HRS.MC.Sec7.E4A2 in
theorem quad_second_aux {L : ℕ} (a : Fin L → ℝ) :
    ∫ y : Fin L → ℝ, ((1 / 2 : ℝ) * ∑ k, a k * (y k ^ 2 - 1)) ^ 2
        ∂(Measure.pi fun _ : Fin L => gaussianReal 0 1) = (1 / 2 : ℝ) * ∑ k, a k ^ 2 := quad_second a

variable {Ω : Type} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]

/-- the `L^2(P)` norm of a function -/
def l2n (P : Measure Ω) (f : Ω → ℝ) : ℝ := (eLpNorm f 2 P).toReal

theorem l2n_nonneg (f : Ω → ℝ) : 0 ≤ l2n P f := ENNReal.toReal_nonneg

theorem l2n_sq {f : Ω → ℝ} (hf : MemLp f 2 P) : l2n P f ^ 2 = ∫ ω, f ω ^ 2 ∂P :=
  HRS.MC.Sec7.E0b.e0b_sq_eq hf

theorem l2n_sub {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    |l2n P f - l2n P g| ≤ l2n P (fun ω => f ω - g ω) := by
  have h := abs_norm_sub_norm_le (hf.toLp f) (hg.toLp g)
  rw [← MemLp.toLp_sub hf hg, Lp.norm_toLp, Lp.norm_toLp, Lp.norm_toLp] at h
  exact h

theorem l2n_add_le {f g : Ω → ℝ} (hf : MemLp f 2 P) (hg : MemLp g 2 P) :
    l2n P (fun ω => f ω + g ω) ≤ l2n P f + l2n P g := by
  have h := norm_add_le (hf.toLp f) (hg.toLp g)
  rw [← MemLp.toLp_add hf hg, Lp.norm_toLp, Lp.norm_toLp, Lp.norm_toLp] at h
  exact h

theorem l2n_const_mul (c : ℝ) (f : Ω → ℝ) : l2n P (fun ω => c * f ω) = |c| * l2n P f := by
  unfold l2n
  have : (fun ω => c * f ω) = c • f := by funext ω; simp
  rw [this, eLpNorm_const_smul, ENNReal.toReal_mul]
  simp


open HRS.MC.Sec7.W4 in
theorem normalized_clt (Q : ℕ → Ω → ℝ) (hQ : ∀ n, MemLp (Q n) 2 P) (σ : ℕ → ℝ)
    (hσpos : ∀ n, 0 < σ n) (hσsq : ∀ n, σ n ^ 2 = ∫ ω, Q n ω ^ 2 ∂P)
    (hσtop : Tendsto σ atTop atTop) {Λ : ℝ} (hΛ : 0 ≤ Λ)
    (happrox : ∀ n, ∀ δ : ℝ, 0 < δ → ∃ (L : ℕ) (a : Fin L → ℝ) (S : Ω → ℝ),
      (∀ k, |a k| ≤ Λ) ∧ MemLp S 2 P ∧
        P.map S = (Measure.pi fun _ : Fin L => gaussianReal 0 1).map
          (fun y : Fin L → ℝ => (1 / 2 : ℝ) * ∑ k, a k * (y k ^ 2 - 1)) ∧
        l2n P (fun ω => Q n ω - S ω) ≤ δ) :
    ∀ F : ℝ → ℝ, Continuous F → (∃ M, ∀ x, |F x| ≤ M) →
      Tendsto (fun n => ∫ ω, F (Q n ω / σ n) ∂P) atTop (𝓝 (∫ y, F y ∂(gaussianReal 0 1))) := by
  choose L a S hbd hSmem hlaw hclose using fun n =>
    happrox n (σ n / ((n : ℝ) + 2)) (by have := hσpos n; positivity)
  have hSm : ∀ n, AEMeasurable (S n) P := fun n => (hSmem n).aestronglyMeasurable.aemeasurable
  set s : ℕ → ℝ := fun n => l2n P (S n) with hsdef
  have hs2 : ∀ n, s n ^ 2 = (1 / 2 : ℝ) * ∑ k, a n k ^ 2 := by
    intro n
    rw [hsdef]; dsimp only
    rw [l2n_sq (hSmem n)]
    have hf : Measurable (fun y : Fin (L n) → ℝ => (1 / 2 : ℝ) * ∑ k, a n k * (y k ^ 2 - 1)) := by
      fun_prop
    have := integral_map (μ := P) (hSm n) (f := fun t : ℝ => t ^ 2)
      (by fun_prop : Continuous (fun t : ℝ => t ^ 2)).aestronglyMeasurable
    rw [← this, hlaw n, integral_map hf.aemeasurable (by fun_prop : Continuous (fun t : ℝ => t ^ 2)).aestronglyMeasurable]
    exact quad_second_aux (a n)
  have hQσ : ∀ n, l2n P (Q n) = σ n := fun n => by
    have h1 := l2n_sq (hQ n)
    rw [← hσsq n] at h1
    exact (sq_eq_sq₀ (l2n_nonneg _) (hσpos n).le).1 h1
  have hdel : ∀ n, |σ n - s n| ≤ σ n / ((n : ℝ) + 2) := fun n => by
    have h1 := l2n_sub (hQ n) (hSmem n)
    rw [hQσ] at h1
    exact h1.trans (hclose n)
  have hfrac : ∀ n : ℕ, 1 / ((n : ℝ) + 2) ≤ 1 / 2 := fun n => by
    apply one_div_le_one_div_of_le (by norm_num)
    have : (0 : ℝ) ≤ n := Nat.cast_nonneg n
    linarith
  have hshalf : ∀ n, σ n / 2 ≤ s n := fun n => by
    have h1 := (abs_le.1 (hdel n)).2
    have h2 : σ n / ((n : ℝ) + 2) ≤ σ n / 2 := by
      calc σ n / ((n : ℝ) + 2) = σ n * (1 / ((n : ℝ) + 2)) := by ring
        _ ≤ σ n * (1 / 2) := mul_le_mul_of_nonneg_left (hfrac n) (hσpos n).le
        _ = σ n / 2 := by ring
    linarith
  have hspos : ∀ n, 0 < s n := fun n => lt_of_lt_of_le (by have := hσpos n; positivity) (hshalf n)
  have hsum_pos : ∀ n, 0 < ∑ k, a n k ^ 2 := fun n => by
    have := hs2 n
    have h2 := pow_pos (hspos n) 2
    linarith
  have hmax : Tendsto (fun n => (⨆ j, |a n j|) / Real.sqrt (∑ j, a n j ^ 2)) atTop (𝓝 0) := by
    have hup : Tendsto (fun n => 2 * Λ / σ n) atTop (𝓝 0) :=
      tendsto_const_nhds.div_atTop hσtop
    refine squeeze_zero (fun n => ?_) (fun n => ?_) hup
    · exact div_nonneg (Real.iSup_nonneg fun j => abs_nonneg _) (Real.sqrt_nonneg _)
    · have hnum : (⨆ j, |a n j|) ≤ Λ := Real.iSup_le (hbd n) hΛ
      have hden : σ n / 2 ≤ Real.sqrt (∑ j, a n j ^ 2) := by
        rw [Real.le_sqrt' (by have := hσpos n; positivity)]
        have h1 := hs2 n
        have h2 := hshalf n
        have h3 := hsum_pos n
        nlinarith [hσpos n]
      have hσ2 : 0 < σ n / 2 := by have := hσpos n; positivity
      calc (⨆ j, |a n j|) / Real.sqrt (∑ j, a n j ^ 2) ≤ Λ / (σ n / 2) :=
            div_le_div₀ hΛ hnum hσ2 hden
        _ = 2 * Λ / σ n := by field_simp
  have hW4 := HRS.MC.Sec7.W4.s7_W4_gaussian_quadratic_clt_proof (ι := fun n => Fin (L n)) a hsum_pos hmax
  -- convergence in law of the approximants
  have hXlim : ∀ F : ℝ → ℝ, Continuous F → (∃ M, ∀ x, |F x| ≤ M) →
      Tendsto (fun n => ∫ ω, F (S n ω / s n) ∂P) atTop (𝓝 (∫ y, F y ∂(gaussianReal 0 1))) := by
    intro F hF hFb
    refine (hW4 F hF hFb).congr fun n => ?_
    have hf : Measurable (fun y : Fin (L n) → ℝ => (1 / 2 : ℝ) * ∑ k, a n k * (y k ^ 2 - 1)) := by
      fun_prop
    have hFc : Continuous (fun t : ℝ => F (t / s n)) := hF.comp (continuous_id.div_const _)
    have h1 := integral_map (μ := P) (hSm n) (f := fun t : ℝ => F (t / s n)) hFc.aestronglyMeasurable
    rw [← h1, hlaw n, integral_map hf.aemeasurable hFc.aestronglyMeasurable]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only
    have h2 : Real.sqrt (2 * ∑ j, a n j ^ 2) = 2 * s n := by
      have : 2 * ∑ j, a n j ^ 2 = (2 * s n) ^ 2 := by rw [mul_pow, hs2 n]; ring
      rw [this, Real.sqrt_sq (by have := hspos n; positivity)]
    rw [h2]
    congr 1
    have := (hspos n).ne'
    field_simp
  -- the difference tends to zero in measure
  have hYmem : ∀ n, MemLp (fun ω => Q n ω / σ n) 2 P := fun n => by
    simpa [div_eq_inv_mul] using (hQ n).const_mul (σ n)⁻¹
  have hXmem : ∀ n, MemLp (fun ω => S n ω / s n) 2 P := fun n => by
    simpa [div_eq_inv_mul] using (hSmem n).const_mul (s n)⁻¹
  have hdiffbound : ∀ n, l2n P (fun ω => Q n ω / σ n - S n ω / s n) ≤ 2 / ((n : ℝ) + 2) := by
    intro n
    have hσn := hσpos n
    have hsn := hspos n
    have hm1 : MemLp (fun ω => (σ n)⁻¹ * (Q n ω - S n ω)) 2 P :=
      ((hQ n).sub (hSmem n)).const_mul _
    have hm2 : MemLp (fun ω => ((σ n)⁻¹ - (s n)⁻¹) * S n ω) 2 P := (hSmem n).const_mul _
    have heq : (fun ω => Q n ω / σ n - S n ω / s n) =
        fun ω => (σ n)⁻¹ * (Q n ω - S n ω) + ((σ n)⁻¹ - (s n)⁻¹) * S n ω := by
      funext ω; field_simp; ring
    rw [heq]
    refine (l2n_add_le hm1 hm2).trans ?_
    rw [l2n_const_mul, l2n_const_mul]
    have t1 : |(σ n)⁻¹| * l2n P (fun ω => Q n ω - S n ω) ≤ 1 / ((n : ℝ) + 2) := by
      calc |(σ n)⁻¹| * l2n P (fun ω => Q n ω - S n ω) ≤ (σ n)⁻¹ * (σ n / ((n : ℝ) + 2)) := by
            rw [abs_of_pos (inv_pos.2 hσn)]
            exact mul_le_mul_of_nonneg_left (hclose n) (inv_pos.2 hσn).le
        _ = 1 / ((n : ℝ) + 2) := by field_simp
    have t2 : |(σ n)⁻¹ - (s n)⁻¹| * l2n P (S n) ≤ 1 / ((n : ℝ) + 2) := by
      have hl : l2n P (S n) = s n := rfl
      rw [hl]
      have : |(σ n)⁻¹ - (s n)⁻¹| * s n = |σ n - s n| / σ n := by
        rw [show |(σ n)⁻¹ - (s n)⁻¹| * s n = |((σ n)⁻¹ - (s n)⁻¹) * s n| by
          rw [abs_mul, abs_of_pos hsn]]
        have e : ((σ n)⁻¹ - (s n)⁻¹) * s n = (s n - σ n) / σ n := by field_simp
        rw [e, abs_div, abs_of_pos hσn, abs_sub_comm]
      rw [this]
      calc |σ n - s n| / σ n ≤ (σ n / ((n : ℝ) + 2)) / σ n :=
            div_le_div_of_nonneg_right (hdel n) hσn.le
        _ = 1 / ((n : ℝ) + 2) := by field_simp
    calc _ ≤ 1 / ((n : ℝ) + 2) + 1 / ((n : ℝ) + 2) := add_le_add t1 t2
      _ = 2 / ((n : ℝ) + 2) := by ring
  have hmeasY : TendstoInMeasure P (fun n ω => Q n ω / σ n - S n ω / s n) atTop 0 := by
    refine tendstoInMeasure_of_tendsto_eLpNorm (p := 2) (by norm_num) ?_
    have hup : Tendsto (fun n : ℕ => ENNReal.ofReal (2 / ((n : ℝ) + 2))) atTop (𝓝 0) := by
      have : Tendsto (fun n : ℕ => 2 / ((n : ℝ) + 2)) atTop (𝓝 0) := by
        refine tendsto_const_nhds.div_atTop ?_
        exact tendsto_atTop_add_const_right _ _ tendsto_natCast_atTop_atTop
      simpa using ENNReal.tendsto_ofReal this
    refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hup (fun n => zero_le)
      (fun n => ?_)
    have hmem : MemLp (fun ω => Q n ω / σ n - S n ω / s n) 2 P := (hYmem n).sub (hXmem n)
    have hfin : eLpNorm (fun ω => Q n ω / σ n - S n ω / s n) 2 P ≠ ⊤ := hmem.eLpNorm_ne_top
    have h0 : ((fun n ω => Q n ω / σ n - S n ω / s n) n - 0) =
        fun ω => Q n ω / σ n - S n ω / s n := by funext ω; simp
    simp only [h0]
    rw [← ENNReal.ofReal_toReal hfin]
    exact ENNReal.ofReal_le_ofReal (hdiffbound n)
  intro F hF hFb
  obtain ⟨M, hM⟩ := hFb
  let f : BoundedContinuousFunction ℝ ℝ := BoundedContinuousFunction.ofNormedAddCommGroup F hF M (fun x => by
    simpa [Real.norm_eq_abs] using hM x)
  have hXd : TendstoInDistribution (fun (n : ℕ) (ω : Ω) => S n ω / s n) atTop (id : ℝ → ℝ)
      (fun _ => P) (gaussianReal 0 1) := by
    rw [tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
      (fun n => (hSm n).div_const _) aemeasurable_id]
    intro g
    exact hXlim g g.continuous ⟨‖g‖, fun x => by simpa using g.norm_coe_le_norm x⟩
  have hYd := tendstoInDistribution_of_tendstoInMeasure_sub
    (fun (n : ℕ) (ω : Ω) => Q n ω / σ n) (id : ℝ → ℝ) hXd hmeasY
    (fun n => (hYmem n).aestronglyMeasurable.aemeasurable)
  rw [tendstoInDistribution_iff_forall_integral_rclike_tendsto ℝ
    (fun n => (hYmem n).aestronglyMeasurable.aemeasurable) aemeasurable_id] at hYd
  simpa [f] using hYd f

end HRS.MC.Sec7.E4A3

end
