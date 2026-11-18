import HRS.Sections.MovLogAux2

/-!
# MOVLOG (part 3): exponential moment of the pair energy under `Q_N^t`, Hölder transfer, homogeneity

* `movlog_expmoment`: `E_{Q_N^t}[e^{cN|F_N^h|}] ≤ e^{C₀ Nδ_N}` uniformly in `t ≥ 0`, `N ≥ 2` and kernels with `|h| ≤ g + cs`
  everywhere (`movT_pressure_two_sided_C2_proof` + `moments_of_pressure`; TeX L6677-6678), together with measurability of
  the energy.
* `movlog_holder_exp`: `E_ν[e^{c(p-1)|Z|/p}] ≤ ‖dν/dQ‖_{L^p(Q)} (E_Q e^{c|Z|})^{(p-1)/p}` (TeX `P:eq:actual-exp`).
* `movlog_modEnergy_smul`: `F^{a h} = a F^h`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

namespace MovLog

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem movlog_modEnergy_smul {N : ℕ} (a : ℝ) (h : Torus d → Torus d → ℝ) (X : Config d N)
    (μ : Measure (Torus d)) :
    modulatedEnergy (fun x y => a * h x y) X μ = a * modulatedEnergy h X μ := by
  unfold modulatedEnergy
  simp only [integral_const_mul, ← Finset.mul_sum]
  ring

theorem movlog_holder_exp {α : Type*} [MeasurableSpace α] {Q ν : Measure α} [SigmaFinite Q] [IsFiniteMeasure ν]
    (hac : ν ≪ Q) {p : ℝ} (hp : 1 < p) {Z : α → ℝ} (hZ : Measurable Z) {c E F : ℝ} (hc : 0 < c)
    (hE : eLpNorm (ν.rnDeriv Q) (ENNReal.ofReal p) Q ≤ ENNReal.ofReal (Real.exp E))
    (hF : ∫⁻ x, ENNReal.ofReal (Real.exp (c * |Z x|)) ∂Q ≤ ENNReal.ofReal (Real.exp F)) :
    ∫⁻ x, ENNReal.ofReal (Real.exp (c * (p - 1) / p * |Z x|)) ∂ν ≤
      ENNReal.ofReal (Real.exp (E + F * ((p - 1) / p))) := by
  set q : ℝ := p / (p - 1) with hq
  have hp0 : 0 < p := by linarith
  have hp1 : 0 < p - 1 := by linarith
  have hpq : p.HolderConjugate q := Real.HolderConjugate.conjExponent hp
  have hqp : 1 / q = (p - 1) / p := by rw [hq]; field_simp
  have hq0 : 0 < q := by positivity
  set g : α → ℝ≥0∞ := fun x => ENNReal.ofReal (Real.exp (c * (p - 1) / p * |Z x|)) with hg
  have hgm : Measurable g := by
    refine ENNReal.measurable_ofReal.comp (Real.measurable_exp.comp ?_)
    exact (measurable_const.mul hZ.abs)
  have hfm : Measurable (ν.rnDeriv Q) := Measure.measurable_rnDeriv ν Q
  have h1 : ∫⁻ x, g x ∂ν ≤ (∫⁻ x, (ν.rnDeriv Q x) ^ p ∂Q) ^ (1 / p) * (∫⁻ x, g x ^ q ∂Q) ^ (1 / q) := by
    rw [← lintegral_rnDeriv_mul hac hgm.aemeasurable]
    exact ENNReal.lintegral_mul_le_Lp_mul_Lq Q hpq hfm.aemeasurable hgm.aemeasurable
  have h2 : (∫⁻ x, (ν.rnDeriv Q x) ^ p ∂Q) ^ (1 / p) = eLpNorm (ν.rnDeriv Q) (ENNReal.ofReal p) Q := by
    rw [eLpNorm_eq_lintegral_rpow_enorm_toReal (ENNReal.ofReal_pos.2 hp0).ne' ENNReal.ofReal_ne_top
      hfm.aestronglyMeasurable, ENNReal.toReal_ofReal hp0.le]
    simp only [enorm_eq_self]
  have h3 : ∀ x, g x ^ q = ENNReal.ofReal (Real.exp (c * |Z x|)) := fun x => by
    rw [hg]
    simp only
    rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le hq0.le, ← Real.exp_mul]
    congr 2
    rw [hq]; field_simp
  simp_rw [h3] at h1
  rw [h2] at h1
  refine h1.trans ?_
  have h4 : (∫⁻ x, ENNReal.ofReal (Real.exp (c * |Z x|)) ∂Q) ^ (1 / q) ≤
      ENNReal.ofReal (Real.exp (F * ((p - 1) / p))) := by
    calc _ ≤ (ENNReal.ofReal (Real.exp F)) ^ (1 / q) := ENNReal.rpow_le_rpow hF (by positivity)
      _ = _ := by
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.exp_pos _).le (by positivity), ← Real.exp_mul, hqp]
  calc _ ≤ ENNReal.ofReal (Real.exp E) * ENNReal.ofReal (Real.exp (F * ((p - 1) / p))) :=
        mul_le_mul' hE h4
    _ = _ := by
        rw [← ENNReal.ofReal_mul (Real.exp_pos _).le, ← Real.exp_add]

theorem movlog_expmoment (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) (cs : ℝ)
    (hw1 : ∀ z : Torus d, 1 ≤ periodicRiesz d s z + cs) :
    ∃ c C0 : ℝ, 0 < c ∧ 0 ≤ C0 ∧ ∀ N : ℕ, 2 ≤ N → ∀ t : ℝ, 0 ≤ t →
      ∀ h : Torus d → Torus d → ℝ, Measurable (Function.uncurry h) → (∀ x y, h x y = h y x) →
        (∀ x y, |h x y| ≤ 1 * (periodicRiesz d s (x - y) + cs)) →
        Measurable (fun X : Config d N => modulatedEnergy h X (withDensityReal (ρ t))) ∧
        ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (c * N *
            |modulatedEnergy h X (withDensityReal (ρ t))|))
          ∂(modulatedGibbs (periodicRiesz d s) N β (withDensityReal (ρ t))) ≤
          ENNReal.ofReal (Real.exp (C0 * ((N : ℝ) * deltaN d s N))) := by
  have hd1 : 1 ≤ d := by omega
  have hs0 := htr.hs0
  have hsd := htr.hsd
  obtain ⟨c₀, Λ₂, hc₀, hunif⟩ := movT_traj_uniform_proof s β V ρ₀ ρ hs0 hsd htr.hβ htr.V_smooth
    htr.init htr.global
  have hw : ∀ z : Torus d, z ≠ 0 → 1 ≤ periodicRiesz d s z + cs := fun z _ => hw1 z
  obtain ⟨θ₀, C, hθ₀, hC0, hP⟩ := movT_pressure_two_sided_C2_proof hd1 s hs0 hsd cs hw β β htr.hβ
    c₀ hc₀ Λ₂ 1
  refine ⟨β * θ₀, 2 * C + 1, mul_pos htr.hβ hθ₀, by positivity, fun N hN t ht h hm hsym hdom => ?_⟩
  have htrj := movlog_traj htr t
  have hρd := htrj.mf.density t ⟨ht, le_rfl⟩
  have hρck := htrj.ck t ⟨ht, le_rfl⟩
  haveI := isProb_withDensityReal hρd
  have hρΛ : ∀ x, ρ t x ≤ max Λ₂ 0 := fun x =>
    ((le_abs_self _).trans ((mova_abs_le_cbNorm_two hρck x).trans (hunif t ht).2)).trans (le_max_left _ _)
  obtain ⟨hgR, hhR⟩ := rowOK_g_h hd1 s hs0 hsd cs hw 1 (le_max_right _ _) hρΛ hm hdom
  refine ⟨measurable_modulatedEnergy hhR, ?_⟩
  have hδ : 1 ≤ (N : ℝ) * deltaN d s N := one_le_mul_deltaN hs0 N (by omega)
  have hP' := hP (ρ t) hρd hρck (hunif t ht).1 (hunif t ht).2 h hm hsym hdom N hN β ⟨le_rfl, le_rfl⟩
  obtain ⟨hE, -⟩ := moments_of_pressure (N := N) (μ := withDensityReal (ρ t)) (g := periodicRiesz d s)
    (h := h) hgR hhR (δ := deltaN d s N) (C := C) (θ₀ := θ₀) (βm := β) (β := β) hδ hC0 hθ₀ htr.hβ
    le_rfl hP'
  refine hE.trans (le_of_eq ?_)
  rw [mul_assoc]

end MovLog

end HRS

end
