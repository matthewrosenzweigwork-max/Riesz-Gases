/-
# TRR helper 3: `D Λ(w)` is invertible (Fredholm alternative + uniqueness of the response solution).
-/
import HRS.Equilibrium.TRRAux2

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.TRR

variable {d : ℕ}

section Kop

variable {g : Torus d → ℝ}

lemma trr_integral_wd {ρ : Torus d → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (f : Torus d → ℝ) : ∫ x, f x ∂(withDensityReal ρ) = ∫ x, ρ x * f x :=
  integral_withDensityReal_eq ρ hρ hρ0 f

/-- `K_μ f` for `μ = ρ dx`. -/
lemma trr_Kop_eq {ρ : Torus d → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (f : Torus d → ℝ) (x : Torus d) :
    Kop g (withDensityReal ρ) f x =
      convFun g (fun y => ρ y * f y) x - ∫ y, ρ y * convFun g (fun z => ρ z * f z) y := by
  unfold Kop projMean pair
  rw [trr_integral_wd hρ hρ0]
  congr 1
  · show ∫ y, g (x - y) * f y ∂(withDensityReal ρ) = _
    rw [trr_integral_wd hρ hρ0]
    unfold convFun
    congr 1; funext y; ring
  · refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show ρ y * _ = ρ y * _
    congr 1
    show ∫ z, g (y - z) * f z ∂(withDensityReal ρ) = _
    rw [trr_integral_wd hρ hρ0]
    unfold convFun
    congr 1; funext z; ring

end Kop

section Inj

variable {s : ℝ} {g : Torus d → ℝ}

lemma trr_isProb_Nc (w : Cb d) : IsProbDensity (Nc w : Torus d → ℝ) :=
  ⟨fun x => (Nc_pos w x).le, (Nc w).continuous.measurable, by
    have := intC_Nc w
    rwa [intC_apply] at this⟩

lemma trr_memLp_cont (μ : Measure (Torus d)) [IsFiniteMeasure μ] (q : Cb d) :
    MemLp (q : Torus d → ℝ) 2 μ :=
  MemLp.of_bound q.continuous.aestronglyMeasurable ‖q‖
    (Filter.Eventually.of_forall fun x => q.norm_coe_le_norm x)

lemma trr_Nder_apply (w h : Cb d) (x : Torus d) :
    Nder w h x = Nc w x * (h x - intC (Nc w * h)) := by
  rw [Nder_apply]; simp only [ContinuousMap.sub_apply, ContinuousMap.mul_apply,
    ContinuousMap.smul_apply, smul_eq_mul]; ring

lemma trr_Dlam_apply (hg : Integrable g) (β : ℝ) (w h : Cb d) (x : Torus d) :
    Dlam hg β w h x = h x + β * convFun g (fun y => Nc w y * (h y - intC (Nc w * h))) x := by
  unfold Dlam
  simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply,
    ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousMap.add_apply,
    ContinuousMap.smul_apply, smul_eq_mul, ContinuousLinearMap.id_apply, convCLM_apply]
  congr 3
  funext y
  exact trr_Nder_apply w h y

theorem trr_dlam_injective (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (w h : Cb d)
    (hh : Dlam (integral_periodicRiesz hd hs0 hsd).1 β w h = 0) : h = 0 := by
  set g := periodicRiesz d s with hgdef
  have hg : Integrable g := (integral_periodicRiesz hd hs0 hsd).1
  set ρ : Cb d := Nc w with hρ
  set c : ℝ := intC (ρ * h) with hc
  have hpt : ∀ x, h x + β * convFun g (fun y => ρ y * (h y - c)) x = 0 := by
    intro x
    have := congrArg (fun f : Cb d => f x) hh
    simpa [trr_Dlam_apply hg] using this
  have hprob := trr_isProb_Nc w
  have hρm : Measurable (ρ : Torus d → ℝ) := ρ.continuous.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (Nc_pos w x).le
  set F : Torus d → ℝ := convFun g (fun y => ρ y * (h y - c)) with hF
  have hFh : ∀ y, F y = -(h y) / β := fun y => by
    have := hpt y
    field_simp
    linarith
  have hρint : ∫ x, ρ x = 1 := by
    have := intC_Nc w; rwa [intC_apply] at this
  have hρh : ∫ x, ρ x * h x = c := rfl
  -- the response property
  let q : Cb d := h - c • 1
  have hqx : ∀ x, q x = h x - c := fun x => by simp [q]
  have hresp : IsResponse g (withDensityReal ρ) β 0 q := by
    have : IsProbabilityMeasure (withDensityReal (ρ : Torus d → ℝ)) := isProb_withDensityReal hprob
    refine ⟨trr_memLp_cont _ q, ?_, Filter.Eventually.of_forall fun x => ?_⟩
    · unfold pair
      rw [trr_integral_wd hρm hρ0]
      have hi1 : Integrable (fun x => ρ x * h x) := (ρ * h).continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
      have hi2 : Integrable (fun x => ρ x) := ρ.continuous.integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
      simp only [hqx]
      have : ∀ x, ρ x * (h x - c) = ρ x * h x - c * ρ x := fun x => by ring
      simp only [this]
      rw [integral_sub hi1 (hi2.const_mul c), integral_const_mul, hρint, hρh]; ring
    · rw [trr_Kop_eq hρm hρ0]
      have hF' : (fun y => ρ y * q y) = fun y => ρ y * (h y - c) := by funext y; rw [hqx]
      simp only [hF', projMean, pair, integral_zero, sub_zero, Pi.zero_apply]
      rw [hqx]
      have h1 : ∫ y, ρ y * F y = -c / β := by
        have : ∀ y, ρ y * F y = -(ρ y * h y) / β := fun y => by rw [hFh]; ring
        simp only [this]
        rw [integral_div, integral_neg, hρh]
      show h x - c + β * (F x - ∫ y, ρ y * F y) = 0
      rw [h1, hFh x]; field_simp; ring
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, ∀ x, ρ x ≤ Λ :=
    ⟨‖ρ‖, fun x => (le_abs_self _).trans (by simpa using ρ.norm_coe_le_norm x)⟩
  haveI : IsProbabilityMeasure (withDensityReal (ρ : Torus d → ℝ)) := isProb_withDensityReal hprob
  obtain ⟨h0, -, huniq⟩ := exists_unique_response hd hs0 hsd ρ hprob Λ hΛ β hβ.le 0
    (trr_memLp_cont _ 0)
  have hz : IsResponse g (withDensityReal ρ) β (0 : Torus d → ℝ) (0 : Torus d → ℝ) := by
    refine ⟨MemLp.zero, by simp [pair], Filter.Eventually.of_forall fun x => ?_⟩
    simp [Kop, projMean, pair]
  have hq0 : (q : Torus d → ℝ) =ᵐ[withDensityReal ρ] 0 := (huniq q hresp).trans (huniq 0 hz).symm
  have hq1 : (q : Torus d → ℝ) =ᵐ[volume] 0 := by
    have := (ae_withDensity_iff (ENNReal.measurable_ofReal.comp hρm)).1 hq0
    filter_upwards [this] with x hx
    exact hx (by simpa using (Nc_pos w x))
  have hq2 : (q : Torus d → ℝ) = 0 :=
    (Continuous.ae_eq_iff_eq volume q.continuous continuous_const).1 hq1
  have hz2 : ∀ y, h y - c = 0 := fun y => by
    have := congrFun hq2 y
    simpa [hqx] using this
  ext x
  have e : (fun y => ρ y * (h y - c)) = fun _ => 0 := by funext y; rw [hz2 y]; ring
  have hF0 : F x = 0 := by
    show convFun g (fun y => ρ y * (h y - c)) x = 0
    rw [e]; simp [convFun]
  have := hpt x
  rw [hF0] at this
  simpa using this

theorem trr_dlam_equiv (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (w : Cb d) :
    ∃ L : Cb d ≃L[ℝ] Cb d,
      (L : Cb d →L[ℝ] Cb d) = Dlam (integral_periodicRiesz hd hs0 hsd).1 β w := by
  set hg : Integrable (periodicRiesz d s) := (integral_periodicRiesz hd hs0 hsd).1 with hghg
  set A : Cb d →L[ℝ] Cb d := β • (convCLM hg).comp (Nder w) with hA
  have hAc : IsCompactOperator A := by
    have h1 := ((convCLM_isCompact hg).comp_clm (Nder w)).clm_comp (β • ContinuousLinearMap.id ℝ (Cb d))
    convert h1 using 1
    funext v
    simp [hA]
  have hD : Dlam hg β w = ContinuousLinearMap.id ℝ (Cb d) + A := rfl
  rcases hAc.hasEigenvalue_or_mem_resolventSet (μ := (-1 : ℝ)) (by norm_num) with he | hr
  · exfalso
    obtain ⟨v, hv⟩ := he.exists_hasEigenvector
    have hv0 : v ≠ 0 := hv.2
    have hAv : A v = (-1 : ℝ) • v := by
      have := hv.apply_eq_smul
      simpa using this
    apply hv0
    refine trr_dlam_injective hd hs0 hsd hβ w v ?_
    rw [hD]
    simp [hAv]
  · rw [spectrum.mem_resolventSet_iff] at hr
    obtain ⟨u, hu⟩ := hr
    refine ⟨ContinuousLinearEquiv.ofUnit (-u), ?_⟩
    ext v : 1
    simp [hD]
    have := congrArg (fun f : Cb d →L[ℝ] Cb d => f v) hu
    simp at this
    show ((-u : (Cb d →L[ℝ] Cb d)ˣ) : Cb d →L[ℝ] Cb d) v = _
    rw [Units.val_neg, ContinuousLinearMap.neg_apply, this]
    abel

end Inj


end HRS.TRR
