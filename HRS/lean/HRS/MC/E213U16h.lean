import HRS.MC.E213U16g

/-!
# Packet e213u16, file h: the law of the future noise `Γ_τ`

`Γ_τ = Z - 𝖳_τ Z` is a centred Gaussian with the covariance of `IsFutureGaussian`; by uniqueness its law is `canonFut`.
-/

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal BigOperators Matrix

set_option linter.unusedSectionVars false

noncomputable section

namespace HRS.MC.E213U16

open HRS HRS.Sec7 HRS.Main HRS.Uniform HRS.MC.E213O HRS.MC.E213T HRS.MC.E213Q HRS.MC.E213U13 HRS.MC.E213Plan
open HRS.MC.E213U10

variable {d : ℕ}

section Cov

variable {S : PreparedData d} {β₀ m : ℝ} {hE : EdgeworthHyp S β₀ m} (gd : GaussData S β₀ hE)

/-- The kernel of the covariance of the noise. -/
def kerK (S : PreparedData d) (ta tb : ℝ) (φa φb : Torus d → ℝ) (r : ℝ) : ℝ :=
  ∫ x, inner ℝ (Torus.grad (propagator S.dyn S.ρ r ta φa) x) (Torus.grad (propagator S.dyn S.ρ r tb φb) x) * S.ρ r x

theorem u16_covK_def (S : PreparedData d) (ta tb : ℝ) (φa φb : Torus d → ℝ) :
    covK S.dyn S.ρ ta tb φa φb = 2 * S.dyn.invβ * ∫ r in Set.Icc 0 (min ta tb), kerK S ta tb φa φb r := rfl

/-- `covK` only depends on the propagators on the common time interval. -/
theorem u16_covK_congr (S : PreparedData d) {ta tb ta' tb' c : ℝ} {φa φb φa' φb' : Torus d → ℝ}
    (h : min ta tb = c) (h' : min ta' tb' = c)
    (ha : ∀ r ∈ Set.Icc 0 c, propagator S.dyn S.ρ r ta φa = propagator S.dyn S.ρ r ta' φa')
    (hb : ∀ r ∈ Set.Icc 0 c, propagator S.dyn S.ρ r tb φb = propagator S.dyn S.ρ r tb' φb') :
    covK S.dyn S.ρ ta tb φa φb = covK S.dyn S.ρ ta' tb' φa' φb' := by
  unfold covK
  rw [h, h']
  congr 1
  refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  simp only [ha r hr, hb r hr]


theorem u16_Gam_eval_ae {H : ℝ} (hH : 0 < H) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) H) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    ∀ᵐ ω ∂gd.P₀, NegSobolev.eval (pathAt (Gam gd H τ ω) t) φ =
      if τ < t then Nrv gd t φ ω - Nrv gd τ (propagator S.dyn S.ρ τ t φ) ω else 0 := by
  filter_upwards [HRS.MC.E213U11.u11_eta_cont gd H] with ω hc
  rw [u16_Gam_eval gd hH hτ hc ht hφ]
  by_cases h : τ < t
  · rw [if_pos h, if_pos h]
    have hco := u16_cocycle (HRS.MC.E213A.regimeOfPrepared S β₀ hE) hφ (le_refl (0 : ℝ)) hτ.1 h
    have hco' : propagator S.dyn S.ρ 0 t φ = propagator S.dyn S.ρ 0 τ (propagator S.dyn S.ρ τ t φ) := hco
    unfold Nrv
    rw [hco']
    ring
  · rw [if_neg h, if_neg h]

theorem u16_volume_Icc_null {a b : ℝ} (h : b ≤ a) : (volume.restrict (Set.Icc a b)) = 0 := by
  refine Measure.restrict_eq_zero.2 ?_
  rw [Real.volume_Icc]
  simpa using h

theorem u16_Gam_cov {H : ℝ} (hH : 0 < H) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) {ta tb : ℝ}
    (hta : ta ∈ Set.Icc (0 : ℝ) H) (htb : tb ∈ Set.Icc (0 : ℝ) H) {φa φb : Torus d → ℝ}
    (hφa : Torus.IsSmooth φa) (hφb : Torus.IsSmooth φb) :
    ∫ ω, NegSobolev.eval (pathAt (Gam gd H τ ω) ta) φa * NegSobolev.eval (pathAt (Gam gd H τ ω) tb) φb ∂gd.P₀ =
      2 * S.dyn.invβ * ∫ r in Set.Icc τ (min ta tb), kerK S ta tb φa φb r := by
  have ea := u16_Gam_eval_ae gd hH hτ hta hφa
  have eb := u16_Gam_eval_ae gd hH hτ htb hφb
  have e : ∫ ω, NegSobolev.eval (pathAt (Gam gd H τ ω) ta) φa * NegSobolev.eval (pathAt (Gam gd H τ ω) tb) φb ∂gd.P₀ =
      ∫ ω, (if τ < ta then Nrv gd ta φa ω - Nrv gd τ (propagator S.dyn S.ρ τ ta φa) ω else 0) *
        (if τ < tb then Nrv gd tb φb ω - Nrv gd τ (propagator S.dyn S.ρ τ tb φb) ω else 0) ∂gd.P₀ := by
    refine integral_congr_ae ?_
    filter_upwards [ea, eb] with ω h1 h2
    rw [h1, h2]
  rw [e]
  by_cases h1 : τ < ta
  · by_cases h2 : τ < tb
    · simp only [if_pos h1, if_pos h2]
      set ψa := propagator S.dyn S.ρ τ ta φa with hψa
      set ψb := propagator S.dyn S.ρ τ tb φb with hψb
      have sa : Torus.IsSmooth ψa := u16_prop_smooth hE hφa hτ.1 h1.le
      have sb : Torus.IsSmooth ψb := u16_prop_smooth hE hφb hτ.1 h2.le
      obtain ⟨i1, v1⟩ := u16_N_pair gd hH hta htb hφa hφb
      obtain ⟨i2, v2⟩ := u16_N_pair gd hH hta hτ hφa sb
      obtain ⟨i3, v3⟩ := u16_N_pair gd hH hτ htb sa hφb
      obtain ⟨i4, v4⟩ := u16_N_pair gd hH hτ hτ sa sb
      have ex : ∀ ω, (Nrv gd ta φa ω - Nrv gd τ ψa ω) * (Nrv gd tb φb ω - Nrv gd τ ψb ω) =
          Nrv gd ta φa ω * Nrv gd tb φb ω - Nrv gd ta φa ω * Nrv gd τ ψb ω
            - Nrv gd τ ψa ω * Nrv gd tb φb ω + Nrv gd τ ψa ω * Nrv gd τ ψb ω := fun ω => by ring
      simp_rw [ex]
      have j1 : Integrable (fun ω => Nrv gd ta φa ω * Nrv gd tb φb ω - Nrv gd ta φa ω * Nrv gd τ ψb ω) gd.P₀ :=
        i1.sub i2
      have j2 : Integrable (fun ω => Nrv gd ta φa ω * Nrv gd tb φb ω - Nrv gd ta φa ω * Nrv gd τ ψb ω
          - Nrv gd τ ψa ω * Nrv gd tb φb ω) gd.P₀ := j1.sub i3
      rw [integral_add j2 i4, integral_sub j1 i3, integral_sub i1 i2, v1, v2, v3, v4]
      have hP : ∀ (t : ℝ) (φ : Torus d → ℝ), τ < t → Torus.IsSmooth φ → ∀ r ∈ Set.Icc 0 τ,
          propagator S.dyn S.ρ r t φ = propagator S.dyn S.ρ r τ (propagator S.dyn S.ρ τ t φ) :=
        fun t φ ht hφ r hr =>
          u16_cocycle (HRS.MC.E213A.regimeOfPrepared S β₀ hE) hφ hr.1 hr.2 ht
      set J := ∫ r in Set.Icc 0 τ, kerK S ta tb φa φb r with hJ
      have t2 : covK S.dyn S.ρ ta τ φa ψb = 2 * S.dyn.invβ * J := by
        unfold covK
        rw [min_eq_right h1.le, hJ]
        congr 1
        refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
        simp only [kerK]
        rw [hP tb φb h2 hφb r hr]
      have t3 : covK S.dyn S.ρ τ tb ψa φb = 2 * S.dyn.invβ * J := by
        unfold covK
        rw [min_eq_left h2.le, hJ]
        congr 1
        refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
        simp only [kerK]
        rw [hP ta φa h1 hφa r hr]
      have t4 : covK S.dyn S.ρ τ τ ψa ψb = 2 * S.dyn.invβ * J := by
        unfold covK
        rw [min_self, hJ]
        congr 1
        refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
        simp only [kerK]
        rw [hP ta φa h1 hφa r hr, hP tb φb h2 hφb r hr]
      rw [t2, t3, t4, u16_covK_def]
      have hle : τ ≤ min ta tb := le_min h1.le h2.le
      have hint : IntegrableOn (fun r => kerK S ta tb φa φb r) (Set.Icc 0 (min ta tb)) :=
        u16_kernel_integrableOn (HRS.MC.E213A.regimeOfPrepared S β₀ hE) hφa hφb hta.1 htb.1
      have hsp : ∫ r in Set.Icc 0 (min ta tb), kerK S ta tb φa φb r =
          J + ∫ r in Set.Icc τ (min ta tb), kerK S ta tb φa φb r := by
        have h3 : ∫ r in Set.Icc τ (min ta tb), kerK S ta tb φa φb r =
            ∫ r in Set.Ioc τ (min ta tb), kerK S ta tb φa φb r := MeasureTheory.integral_Icc_eq_integral_Ioc
        have hu : Set.Icc 0 (min ta tb) = Set.Icc 0 τ ∪ Set.Ioc τ (min ta tb) :=
          (Set.Icc_union_Ioc_eq_Icc hτ.1 hle).symm
        have ia : IntegrableOn (fun r => kerK S ta tb φa φb r) (Set.Icc 0 τ) :=
          hint.mono_set (Set.Icc_subset_Icc_right hle)
        have ib : IntegrableOn (fun r => kerK S ta tb φa φb r) (Set.Ioc τ (min ta tb)) :=
          hint.mono_set (fun x hx => ⟨hτ.1.trans hx.1.le, hx.2⟩)
        rw [h3, hu, setIntegral_union (Set.disjoint_left.2 fun x hx hx' => absurd hx.2 (not_le.2 hx'.1))
          measurableSet_Ioc ia ib]
      rw [hsp]
      ring
    · have : min ta tb ≤ τ := (min_le_right _ _).trans (not_lt.1 h2)
      rw [u16_volume_Icc_null this, integral_zero_measure, mul_zero]
      simp only [if_neg h2, mul_zero, integral_zero]
  · have : min ta tb ≤ τ := (min_le_left _ _).trans (not_lt.1 h1)
    rw [u16_volume_Icc_null this, integral_zero_measure, mul_zero]
    simp only [if_neg h1, zero_mul, integral_zero]


theorem u16_pathEval_cont {H : ℝ} {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) H) {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Continuous (fun z : PathSpace d m H => NegSobolev.eval (pathAt z t) φ) := by
  obtain ⟨ℓ, hℓ, -⟩ := pathObservation_bounded m H ⟨t, ht⟩ φ (HRS.A33.a33_memSob m hφ)
  have : (fun z : PathSpace d m H => NegSobolev.eval (pathAt z t) φ) = fun z => ℓ z := by
    funext z
    rw [hℓ z, ← HRS.MC.E213U4.u4_pathAt_coe z ⟨t, ht⟩]
  rw [this]
  exact ℓ.continuous

theorem u16_Gam_isFG {H : ℝ} (hH : 0 < H) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) :
    IsFutureGaussian (regime S β₀ hE).D (regime S β₀ hE).ρ m H τ (gd.P₀.map (Gam gd H τ)) := by
  refine ⟨u16_Gam_centered gd H hH hτ, ?_⟩
  intro ta tb φa φb hφa hφb hta htb
  have hm := u16_Gam_aemeasurable gd H hH hτ
  have hc : Continuous (fun z : PathSpace d m H => NegSobolev.eval (pathAt z ta) φa *
      NegSobolev.eval (pathAt z tb) φb) := (u16_pathEval_cont hta hφa).mul (u16_pathEval_cont htb hφb)
  rw [integral_map hm hc.aestronglyMeasurable]
  exact u16_Gam_cov gd hH hτ hta htb hφa hφb

theorem u16_Gam_law {H : ℝ} (hH : 0 < H) {τ : ℝ} (hτ : τ ∈ Set.Icc (0 : ℝ) H) :
    gd.P₀.map (Gam gd H τ) = canonFut hE H τ :=
  HRS.MC.E213U4.isFutureGaussian_unique_proof hE H τ hH (u16_Gam_isFG gd hH hτ)
    ((HRS.MC.E213U5.e213u5_canonFut_spec hE H hH τ hτ).1)

end Cov

end HRS.MC.E213U16

end
