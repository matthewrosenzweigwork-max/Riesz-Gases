import HRS.MS.SA16Y5Vg1

/-!
# S.A.16 (SA16Y5) Vg2: the Bielecki weight for kernels `C s^{-γ}` (B7, part 2)

`sa16y5g_kappa γ T lam = ∫_0^T e^{-lam s} s^{-γ} ds → 0` (`lam → ∞`, dominated convergence) and the contraction estimate `sa16y5g_volt_diff_le`.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Whole.AppendixA.Phase2SA16R

section Volt3
variable {X : Type*} [NormedAddCommGroup X] [NormedSpace ℝ X] [CompleteSpace X] {γ : ℝ}

lemma VoltKerG.weight {T C : ℝ} {P : ℝ → ℝ → X →L[ℝ] X} (hP : VoltKerG γ T C P) {lam : ℝ} (hl : 0 ≤ lam) :
    VoltKerG γ T C (voltW P lam) := by
  refine ⟨hP.γ0, hP.γ1, fun τ s hs hsτ hτ => ?_, fun x => ?_⟩
  · have h := hP.bound τ s hs hsτ hτ
    have hexp : Real.exp (-lam * s) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith
    calc ‖voltW P lam τ s‖ = Real.exp (-lam * s) * ‖P τ s‖ := by
          simp [voltW, norm_smul, abs_of_pos (Real.exp_pos _)]
      _ ≤ 1 * (C * s ^ (-γ)) := by
          gcongr
      _ = C * s ^ (-γ) := one_mul _
  · have h1 : ContinuousOn (fun q : ℝ × ℝ => Real.exp (-lam * q.2))
        {q | 0 < q.2 ∧ q.2 ≤ q.1 ∧ q.1 ≤ T} := by fun_prop
    exact h1.smul (hP.cont x)

/-- the weighted integral `κ(λ) = ∫_0^T e^{-λ s} s^{-1/2} ds` -/
def sa16y5g_kappa (γ T lam : ℝ) : ℝ := ∫ s in Ioc 0 T, Real.exp (-lam * s) * s ^ (-γ)

lemma sa16y5g_kappa_int (hγ1 : γ < 1) (T : ℝ) {lam : ℝ} (hl : 0 ≤ lam) :
    IntegrableOn (fun s : ℝ => Real.exp (-lam * s) * s ^ (-γ)) (Ioc 0 T) := by
  refine Integrable.mono' (sa16y5g_rpow_int hγ1 T) ?_ ?_
  · refine Measurable.aestronglyMeasurable ?_
    fun_prop
  · rw [ae_restrict_iff' measurableSet_Ioc]
    refine Filter.Eventually.of_forall fun s hs => ?_
    have h0 : 0 ≤ s ^ (-γ) := Real.rpow_nonneg hs.1.le _
    have hexp : Real.exp (-lam * s) ≤ 1 := by
      rw [Real.exp_le_one_iff]; nlinarith [hs.1]
    rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h0)]
    calc Real.exp (-lam * s) * s ^ (-γ) ≤ 1 * s ^ (-γ) := by gcongr
      _ = _ := one_mul _

lemma sa16y5g_kappa_nonneg (γ T lam : ℝ) : 0 ≤ sa16y5g_kappa γ T lam := by
  refine setIntegral_nonneg measurableSet_Ioc fun s hs => ?_
  exact mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hs.1.le _)

lemma sa16y5g_kappa_small (hγ1 : γ < 1) (T : ℝ) {ε : ℝ} (hε : 0 < ε) : ∃ lam : ℝ, 0 ≤ lam ∧ sa16y5g_kappa γ T lam ≤ ε := by
  have h : Tendsto (fun n : ℕ => sa16y5g_kappa γ T (n : ℝ)) atTop (𝓝 0) := by
    have := tendsto_integral_of_dominated_convergence
      (μ := volume.restrict (Ioc (0 : ℝ) T))
      (F := fun (n : ℕ) (s : ℝ) => Real.exp (-(n : ℝ) * s) * s ^ (-γ))
      (f := fun _ => (0 : ℝ)) (bound := fun s : ℝ => s ^ (-γ))
      (fun n => by
        refine Measurable.aestronglyMeasurable ?_
        fun_prop)
      (sa16y5g_rpow_int hγ1 T) ?_ ?_
    · simpa [sa16y5g_kappa] using this
    · intro n
      rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun s hs => ?_
      have h0 : 0 ≤ s ^ (-γ) := Real.rpow_nonneg hs.1.le _
      have hexp : Real.exp (-(n : ℝ) * s) ≤ 1 := by
        rw [Real.exp_le_one_iff]; nlinarith [hs.1, (Nat.cast_nonneg n : (0 : ℝ) ≤ n)]
      rw [Real.norm_eq_abs, abs_of_nonneg (mul_nonneg (Real.exp_pos _).le h0)]
      calc Real.exp (-(n : ℝ) * s) * s ^ (-γ) ≤ 1 * s ^ (-γ) := by gcongr
        _ = _ := one_mul _
    · rw [ae_restrict_iff' measurableSet_Ioc]
      refine Filter.Eventually.of_forall fun s hs => ?_
      have : Tendsto (fun n : ℕ => Real.exp (-(n : ℝ) * s)) atTop (𝓝 0) := by
        have h1 : Tendsto (fun n : ℕ => -(n : ℝ) * s) atTop atBot := by
          have : Tendsto (fun n : ℕ => (n : ℝ) * s) atTop atTop :=
            tendsto_natCast_atTop_atTop.atTop_mul_const hs.1
          exact (tendsto_neg_atTop_atBot.comp this).congr (fun n => by simp [neg_mul])
        exact Real.tendsto_exp_atBot.comp h1
      simpa using this.mul_const (s ^ (-γ))
  obtain ⟨n, hn⟩ := (h.eventually (Iio_mem_nhds hε)).exists
  exact ⟨n, Nat.cast_nonneg n, le_of_lt hn⟩

lemma sa16y5g_volt_diff_le {T C : ℝ} {P : ℝ → ℝ → X →L[ℝ] X} (hP : VoltKerG γ T C P) (hT : 0 < T) {lam : ℝ}
    (hl : 0 ≤ lam) {w w' : ℝ → X} (hw : ContinuousOn w (Icc 0 T)) (hw' : ContinuousOn w' (Icc 0 T))
    {B : ℝ} (hB : ∀ r ∈ Icc (0 : ℝ) T, ‖w r - w' r‖ ≤ B) {τ : ℝ} (hτ : τ ∈ Icc (0 : ℝ) T) :
    ‖voltOp (voltW P lam) w τ - voltOp (voltW P lam) w' τ‖ ≤ C * sa16y5g_kappa γ T lam * B := by
  have hPl := hP.weight hl
  have hC := hP.C_nonneg hT
  have hB0 : 0 ≤ B := (norm_nonneg _).trans (hB 0 ⟨le_rfl, hT.le⟩)
  have i1 := hPl.integrable_integrand hT hw hτ.1 hτ.2
  have i2 := hPl.integrable_integrand hT hw' hτ.1 hτ.2
  unfold voltOp
  rw [intervalIntegral.integral_of_le hτ.1, intervalIntegral.integral_of_le hτ.1, ← integral_sub i1 i2]
  have hbd : ∀ s ∈ Ioc 0 τ, ‖voltW P lam τ s (w (τ - s)) - voltW P lam τ s (w' (τ - s))‖ ≤
      C * B * (Real.exp (-lam * s) * s ^ (-γ)) := by
    intro s hs
    rw [← map_sub]
    have h1 := hP.bound τ s hs.1 hs.2 hτ.2
    have h2 := hB (τ - s) ⟨by linarith [hs.2], by linarith [hs.1, hτ.2]⟩
    have hn : ‖voltW P lam τ s‖ ≤ Real.exp (-lam * s) * (C * s ^ (-γ)) := by
      simp only [voltW, norm_smul, Real.norm_eq_abs, abs_of_pos (Real.exp_pos _)]
      gcongr
    calc ‖voltW P lam τ s (w (τ - s) - w' (τ - s))‖
        ≤ ‖voltW P lam τ s‖ * ‖w (τ - s) - w' (τ - s)‖ := (voltW P lam τ s).le_opNorm _
      _ ≤ (Real.exp (-lam * s) * (C * s ^ (-γ))) * B :=
          mul_le_mul hn h2 (norm_nonneg _)
            (mul_nonneg (Real.exp_pos _).le (mul_nonneg hC (Real.rpow_nonneg hs.1.le _)))
      _ = C * B * (Real.exp (-lam * s) * s ^ (-γ)) := by ring
  have hint : IntegrableOn (fun s : ℝ => C * B * (Real.exp (-lam * s) * s ^ (-γ))) (Ioc 0 T) :=
    (sa16y5g_kappa_int hP.γ1 T hl).const_mul (C * B)
  have hintτ : IntegrableOn (fun s : ℝ => C * B * (Real.exp (-lam * s) * s ^ (-γ))) (Ioc 0 τ) :=
    hint.mono_set (Ioc_subset_Ioc_right hτ.2)
  calc ‖∫ s in Ioc 0 τ, (voltW P lam τ s (w (τ - s)) - voltW P lam τ s (w' (τ - s)))‖
      ≤ ∫ s in Ioc 0 τ, C * B * (Real.exp (-lam * s) * s ^ (-γ)) := by
        refine norm_integral_le_of_norm_le hintτ ?_
        rw [ae_restrict_iff' measurableSet_Ioc]
        exact Filter.Eventually.of_forall hbd
    _ ≤ ∫ s in Ioc 0 T, C * B * (Real.exp (-lam * s) * s ^ (-γ)) := by
        refine setIntegral_mono_set hint ?_ (Ioc_subset_Ioc_right hτ.2).eventuallyLE
        rw [Filter.EventuallyLE, ae_restrict_iff' measurableSet_Ioc]
        refine Filter.Eventually.of_forall fun s hs => ?_
        exact mul_nonneg (mul_nonneg hC hB0) (mul_nonneg (Real.exp_pos _).le (Real.rpow_nonneg hs.1.le _))
    _ = C * sa16y5g_kappa γ T lam * B := by
        rw [integral_const_mul, sa16y5g_kappa]; ring


end Volt3

end HRS.Whole.AppendixA.Phase2SA16R
