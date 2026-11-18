import HRS.MC.L2C3aAux3
import HRS.MC.RegSet
import HRS.PDE.EnergyR2Fn

/-!
# Packet L2C-3a: the exponentially small generator perturbation, in weak form

`|∫ (𝓛_t f - 𝓛_β f) h dx| ≤ C e^{-κt} ‖∇f‖_{L²} ‖h‖_{L²}`.  Route: for `M = -I`
`𝓛_{ρ₁} f - 𝓛_{ρ₂} f (x) = ∫ (ρ₁-ρ₂)(x-z) ⟨∇f(x-z) - ∇f(x), ∇g(z)⟩ dz` (plain form of the cancellation
convolution since `∇g ∈ L¹`), hence `|·| ≤ ‖ρ₁-ρ₂‖_∞ (‖∇g‖₁ |∇f(x)| + (|∇g| ⋆ |∇f|)(x))`;
Cauchy-Schwarz and the Schur/Young inequality give the weak bound; `Regime.relax` (relocated as
`HRS.MC.RegSet.relax_proof`) supplies `‖ρ^t - ρ_β‖_∞ ≤ C e^{-ct}`.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Sec7

namespace HRS.MC.L2C3a

variable {d : ℕ}

theorem l2c3a_cont_of_isCk0 {φ : Torus d → ℝ} (h : Torus.IsCk ((0 : ℕ) : WithTop ℕ∞) φ) :
    Continuous φ :=
  Torus.continuous_of_continuous_lift h.continuous

theorem l2c3a_isCk_of_smooth {φ : Torus d → ℝ} (h : Torus.IsSmooth φ) (k : ℕ) :
    Torus.IsCk (k : WithTop ℕ∞) φ :=
  ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from h)
    (by exact_mod_cast le_top)

theorem l2c3a_proof (R : Regime d) :
    ∃ C κ : ℝ, 0 < κ ∧ ∀ t : ℝ, 0 ≤ t → ∀ f h : Torus d → ℝ, Torus.IsSmooth f → Torus.IsSmooth h →
      |∫ x, (backwardGenerator R.D (R.ρ t) f x - backwardGenerator R.D R.ρβ f x) * h x| ≤
        C * Real.exp (-κ * t) * Real.sqrt (∫ x, ‖Torus.grad f x‖ ^ 2) * Real.sqrt (PDE.l2NormSq h) := by
  obtain ⟨C0, c0, hc0, H0⟩ := HRS.MC.RegSet.relax_proof R 0
  obtain ⟨Λ, hΛ⟩ := HRS.MC.RegSet.reg_proof R 0
  have hs : R.D.s + 1 < d := by
    have h1 := R.hs
    have h2 : (2 : ℝ) ≤ d := by exact_mod_cast R.hd
    linarith
  obtain ⟨CG, hG, hGi⟩ := l2c3a_kernel R.hd R.D.hs0 hs
  set k : Torus d → ℝ := fun z => ‖periodicRieszGrad d R.D.s z‖ with hk
  have hki : Integrable k := hGi.norm
  have hk0 : ∀ z, 0 ≤ k z := fun z => norm_nonneg _
  have hkm : Measurable k := hG.meas.norm
  set N := ∫ z, k z with hN
  have hN0 : 0 ≤ N := integral_nonneg hk0
  refine ⟨2 * N * C0, c0, hc0, ?_⟩
  intro t ht f h hf hh
  have hρ1 := (hΛ t t ⟨ht, le_rfl⟩).1
  have hρ1c : Continuous (R.ρ t) := l2c3a_cont_of_isCk0 hρ1
  have hρβ := l2c3a_isCk_of_smooth R.thermal.2.1 0
  have hρβc : Continuous R.ρβ := l2c3a_cont_of_isCk0 hρβ
  obtain ⟨B₁, hB₁0, hB₁⟩ := l2c3a_bdd_of_cont _ hρ1c
  obtain ⟨B₂, hB₂0, hB₂⟩ := l2c3a_bdd_of_cont _ hρβc
  have hδ : Torus.IsCk ((0 : ℕ) : WithTop ℕ∞) (fun x => R.ρ t x - R.ρβ x) :=
    hρ1.sub hρβ
  set ε := C0 * Real.exp (-c0 * t) with hεdef
  have hε : ∀ x, |R.ρ t x - R.ρβ x| ≤ ε := fun x =>
    (HRS.PDE.R2Aux.abs_le_cbNorm hδ x).trans (H0 t ht)
  have hε0 : 0 ≤ ε := (abs_nonneg _).trans (hε 0)
  have hf1 := l2c3a_isCk_of_smooth hf 1
  have hh0 := l2c3a_isCk_of_smooth hh 0
  have hgc : Continuous (Torus.grad f) := HRS.PDE.MFLinear.continuous_grad hf1
  have hhc : Continuous h := l2c3a_cont_of_isCk0 hh0
  obtain ⟨Bg, hBg0, hBg⟩ := l2c3a_bdd_of_cont _ hgc
  obtain ⟨Bh, hBh0, hBh⟩ := l2c3a_bdd_of_cont _ hhc
  set a : Torus d → ℝ := fun x => ‖Torus.grad f x‖ with ha
  set b : Torus d → ℝ := fun x => |h x| with hb
  have ham : Measurable a := hgc.measurable.norm
  have hbm : Measurable b := hhc.measurable.abs
  have haB : ∀ x, |a x| ≤ Bg := fun x => by
    simp only [ha, abs_norm]; exact hBg x
  have hbB : ∀ x, |b x| ≤ Bh := fun x => by
    simp only [hb, abs_abs]; simpa using hBh x
  have hpt : ∀ x, |backwardGenerator R.D (R.ρ t) f x - backwardGenerator R.D R.ρβ f x| ≤
      ε * (N * a x + ∫ z, k z * a (x - z)) := fun x =>
    l2c3a_diff_bound R.D R.hd R.hM hs hρ1c.measurable hρβc.measurable
      (fun x => by simpa using hB₁ x) (fun x => by simpa using hB₂ x) hε hf1 x
  have hint1 : Integrable (fun x => a x * b x) := l2c3a_integrable_of_bdd (ham.mul hbm)
    (B := Bg * Bh) fun x => by
      rw [abs_mul]; exact mul_le_mul (haB x) (hbB x) (abs_nonneg _) hBg0 |>.trans_eq rfl
  have hint2 := l2c3a_conv_mul_integrable hki hk0 ham hbm haB hbB
  have hrhs : Integrable (fun x => ε * (N * (a x * b x) + (∫ z, k z * a (x - z)) * b x)) :=
    ((hint1.const_mul N).add hint2).const_mul ε
  have step1 : |∫ x, (backwardGenerator R.D (R.ρ t) f x - backwardGenerator R.D R.ρβ f x) * h x| ≤
      ∫ x, ε * (N * (a x * b x) + (∫ z, k z * a (x - z)) * b x) := by
    rw [← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _) hrhs
      (Filter.Eventually.of_forall fun x => ?_)
    beta_reduce
    rw [Real.norm_eq_abs, abs_mul]
    have := mul_le_mul_of_nonneg_right (hpt x) (abs_nonneg (h x))
    calc _ ≤ ε * (N * a x + ∫ z, k z * a (x - z)) * |h x| := this
      _ = _ := by simp only [hb]; ring
  have hcs := l2c3a_cs ham hbm haB hbB
  have hsch := l2c3a_schur hki hk0 ham hbm haB hbB
  have hbsq : ∫ x, b x ^ 2 = PDE.l2NormSq h := by
    simp only [hb, sq_abs]; rfl
  have hasq : ∫ x, a x ^ 2 = ∫ x, ‖Torus.grad f x‖ ^ 2 := rfl
  rw [hbsq, hasq] at hcs hsch
  rw [integral_const_mul, integral_add (hint1.const_mul N) hint2, integral_const_mul] at step1
  have hex : Real.exp (-c0 * t) = Real.exp (-c0 * t) := rfl
  refine step1.trans ?_
  set A := Real.sqrt (∫ x, ‖Torus.grad f x‖ ^ 2)
  set H := Real.sqrt (PDE.l2NormSq h)
  have hA0 : 0 ≤ A := Real.sqrt_nonneg _
  have hH0 : 0 ≤ H := Real.sqrt_nonneg _
  calc ε * ((N * ∫ x, a x * b x) + ∫ x, (∫ z, k z * a (x - z)) * b x)
      ≤ ε * (N * (A * H) + N * (A * H)) := by
        gcongr
    _ = 2 * N * C0 * Real.exp (-c0 * t) * A * H := by simp only [hεdef]; ring

end HRS.MC.L2C3a
