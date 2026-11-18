/-
# TRR helper 7: continuous response of `ρ_θ`, the bias integral `∫ (R P ρ) φ dμ = ∫ ρ² q`.
-/
import HRS.Equilibrium.TRRAux6
import HRS.PDE.MeanFieldAdjointFrozen

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.TRR

variable {d : ℕ} {s β : ℝ}

/-- `IsResponse` from a solution of the linearised equation. -/
theorem trr_isResponse_of_dlam (hg : Integrable (periodicRiesz d s)) (w v ψ : Cb d)
    (hv : Dlam hg β w v = ψ) :
    IsResponse (periodicRiesz d s) (withDensityReal (Nc w)) β ψ
      ⇑(v - intC (Nc w * v) • (1 : Cb d)) := by
  obtain ⟨q, hq⟩ : ∃ q : Cb d, q = v - intC (Nc w * v) • (1 : Cb d) := ⟨_, rfl⟩
  rw [← hq]
  set ρ : Cb d := Nc w with hρ
  set c : ℝ := intC (ρ * v) with hc
  set g := periodicRiesz d s with hg'
  have hprob : IsProbDensity (ρ : Torus d → ℝ) := trr_isProb_Nc w
  have hρm : Measurable (ρ : Torus d → ℝ) := ρ.continuous.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (Nc_pos w x).le
  have : IsProbabilityMeasure (withDensityReal (ρ : Torus d → ℝ)) := isProb_withDensityReal hprob
  have hi : ∀ f : Cb d, Integrable (fun x => f x) := fun f =>
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hqx : ∀ x, q x = v x - c := fun x => by simp [hq]
  have hρint : ∫ x, ρ x = 1 := by
    have := intC_Nc w; rwa [intC_apply] at this
  have hρv : ∫ x, ρ x * v x = c := rfl
  have hpt : ∀ x, v x + β * convFun g (fun y => ρ y * q y) x = ψ x := by
    intro x
    have h := congrArg (fun f : Cb d => f x) hv
    simp only [trr_Dlam_apply hg] at h
    rw [← h]
    simp only [hqx]
    rfl
  have hpq : pair (withDensityReal ρ) q = 0 := by
    unfold pair
    rw [trr_integral_wd hρm hρ0]
    have hi1 : Integrable (fun x => ρ x * v x) := hi (ρ * v)
    have hi2 : Integrable (fun x => ρ x) := hi ρ
    have : ∀ x, ρ x * q x = ρ x * v x - c * ρ x := fun x => by rw [hqx]; ring
    simp only [this]
    rw [integral_sub hi1 (hi2.const_mul c), integral_const_mul, hρint, hρv]; ring
  refine ⟨trr_memLp_cont _ q, hpq, Filter.Eventually.of_forall fun x => ?_⟩
  rw [trr_Kop_eq hρm hρ0]
  set F : Torus d → ℝ := convFun g (fun y => ρ y * q y) with hF
  have hFv : ∀ y, β * F y = ψ y - v y := fun y => by
    have := hpt y
    linarith
  have hic : Integrable (fun y => ρ y * ψ y) := hi (ρ * ψ)
  have hiv : Integrable (fun y => ρ y * v y) := hi (ρ * v)
  have h1 : β * ∫ y, ρ y * F y = (∫ y, ρ y * ψ y) - c := by
    rw [← integral_const_mul]
    have : ∀ y, β * (ρ y * F y) = ρ y * ψ y - ρ y * v y := fun y => by
      calc β * (ρ y * F y) = ρ y * (β * F y) := by ring
        _ = _ := by rw [hFv y]; ring
    simp only [this]
    rw [integral_sub hic hiv, hρv]
  unfold projMean pair
  rw [trr_integral_wd hρm hρ0, mul_sub]
  linarith [hqx x, hFv x, h1]

/-- uniqueness: `responseInverse` is a.e. any continuous response solution. -/
theorem trr_responseInverse_ae_of (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β)
    (w ψ r : Cb d)
    (hr : IsResponse (periodicRiesz d s) (withDensityReal (Nc w)) β ψ r) :
    responseInverse (periodicRiesz d s) (withDensityReal (Nc w)) β ψ
      =ᵐ[withDensityReal (Nc w)] r := by
  set ρ : Cb d := Nc w with hρ
  have hprob : IsProbDensity (ρ : Torus d → ℝ) := trr_isProb_Nc w
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, ∀ x, ρ x ≤ Λ :=
    ⟨‖ρ‖, fun x => (le_abs_self _).trans (by simpa using ρ.norm_coe_le_norm x)⟩
  have : IsProbabilityMeasure (withDensityReal (ρ : Torus d → ℝ)) := isProb_withDensityReal hprob
  obtain ⟨h0, -, huniq⟩ := exists_unique_response hd hs0 hsd ρ hprob Λ hΛ β hβ.le ψ
    (trr_memLp_cont _ ψ)
  have hex : ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) β ψ h := ⟨_, hr⟩
  have e : responseInverse (periodicRiesz d s) (withDensityReal ρ) β ψ = hex.choose := by
    unfold responseInverse
    simp only [hex, dite_true]
  rw [e]
  exact (huniq _ hex.choose_spec).trans (huniq _ hr).symm


section Bias

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (k : Lattice d)

include hd hs0 hsd hβ in
lemma trr_dlam_solve (w f : Cb d) : ∃ v, Dlam (trr_gint hd hs0 hsd) β w v = f := by
  obtain ⟨L, hL⟩ := trr_dlam_equiv hd hs0 hsd hβ w
  exact ⟨L.symm f, by rw [← hL]; exact L.apply_symm_apply f⟩

def Vr (θ : ℝ) : Cb d :=
  (trr_dlam_solve hd hs0 hsd hβ (Wc hd hs0 hsd hβ k θ) (Rc hd hs0 hsd hβ k θ)).choose

lemma Vr_spec (θ : ℝ) :
    Dlam (trr_gint hd hs0 hsd) β (Wc hd hs0 hsd hβ k θ) (Vr hd hs0 hsd hβ k θ) =
      Rc hd hs0 hsd hβ k θ :=
  (trr_dlam_solve hd hs0 hsd hβ (Wc hd hs0 hsd hβ k θ) (Rc hd hs0 hsd hβ k θ)).choose_spec

def rr (θ : ℝ) : Cb d :=
  Vr hd hs0 hsd hβ k θ - intC (Rc hd hs0 hsd hβ k θ * Vr hd hs0 hsd hβ k θ) • (1 : Cb d)

lemma rr_resp (θ : ℝ) :
    IsResponse (periodicRiesz d s) (withDensityReal (Rc hd hs0 hsd hβ k θ)) β
      ⇑(Rc hd hs0 hsd hβ k θ) ⇑(rr hd hs0 hsd hβ k θ) :=
  trr_isResponse_of_dlam (trr_gint hd hs0 hsd) (Wc hd hs0 hsd hβ k θ) _ _
    (Vr_spec hd hs0 hsd hβ k θ)


include hd hs0 hsd hβ in
theorem trr_bias_integral (θ : ℝ) :
    ∫ x, responseInverse (periodicRiesz d s) (withDensityReal (Rc hd hs0 hsd hβ k θ)) β
        (⇑(Rc hd hs0 hsd hβ k θ)) x * Torus.cosMode k x ∂(withDensityReal (Rc hd hs0 hsd hβ k θ)) =
      ∫ x, Rc hd hs0 hsd hβ k θ x * (Rc hd hs0 hsd hβ k θ x * qc hd hs0 hsd hβ k θ x) := by
  set ρ := Rc hd hs0 hsd hβ k θ with hρ
  set q := qc hd hs0 hsd hβ k θ with hq'
  set r := rr hd hs0 hsd hβ k θ with hr'
  set g := periodicRiesz d s with hgdef
  have hg : Integrable g := trr_gint hd hs0 hsd
  have hprob : IsProbDensity (ρ : Torus d → ℝ) := trr_isProb_Nc _
  have hρm : Measurable (ρ : Torus d → ℝ) := ρ.continuous.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (Rc_pos hd hs0 hsd hβ k θ x).le
  have : IsProbabilityMeasure (withDensityReal (ρ : Torus d → ℝ)) := isProb_withDensityReal hprob
  set μ := withDensityReal (ρ : Torus d → ℝ) with hμ
  have hr : IsResponse g μ β ρ r := rr_resp hd hs0 hsd hβ k θ
  have hq : IsResponse g μ β (Torus.cosMode k) q := trr_response_q hd hs0 hsd hβ k θ
  have hae : responseInverse g μ β ρ =ᵐ[μ] r :=
    trr_responseInverse_ae_of hd hs0 hsd hβ (Wc hd hs0 hsd hβ k θ) ρ r hr
  have hiμ : ∀ f : Torus d → ℝ, Continuous f → Integrable f μ := fun f hf =>
    hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hi : ∀ f : Cb d, Integrable (fun x => f x) := fun f =>
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hKc : ∀ f : Cb d, Continuous (Kop g μ f) := fun f => by
    have : Kop g μ f = fun x => convFun g (fun y => ρ y * f y) x -
        ∫ y, ρ y * convFun g (fun z => ρ z * f z) y := funext (trr_Kop_eq hρm hρ0 f)
    rw [this]
    exact (PDE.MFAux.continuous_convFun hg (ρ.continuous.mul f.continuous)).sub continuous_const
  rw [integral_congr_ae (hae.mono fun x hx => by rw [hx])]
  have hm : ∀ f h : Torus d → ℝ, Continuous f → Continuous h →
      Integrable (fun x => f x * h x) μ := fun f h hf hh => hiμ _ (hf.mul hh)
  have hmv : ∀ f h : Cb d, Integrable (fun x => f x * h x) := fun f h => hi (f * h)
  have hrμ : ∫ x, r x ∂μ = 0 := hr.2.1
  have hqμ : ∫ x, q x ∂μ = 0 := hq.2.1
  have hrc : Continuous (r : Torus d → ℝ) := r.continuous
  have hqc : Continuous (q : Torus d → ℝ) := q.continuous
  -- step a
  have ha : ∫ x, r x * Torus.cosMode k x ∂μ = ∫ x, r x * projMean μ (Torus.cosMode k) x ∂μ := by
    have e : ∀ x, r x * projMean μ (Torus.cosMode k) x =
        r x * Torus.cosMode k x - pair μ (Torus.cosMode k) * r x := fun x => by
      unfold projMean; ring
    have i1 : Integrable (fun x => r x * Torus.cosMode k x) μ :=
      hm _ _ hrc (Torus.continuous_cosMode k)
    have i2 : Integrable (fun x => r x) μ := hiμ _ hrc
    refine Eq.trans ?_ (integral_congr_ae (Filter.Eventually.of_forall fun x => (e x).symm))
    rw [integral_sub i1 (i2.const_mul _), integral_const_mul, hrμ]; ring
  -- step b
  have hb : ∫ x, r x * projMean μ (Torus.cosMode k) x ∂μ =
      ∫ x, r x * q x ∂μ + β * ∫ x, r x * Kop g μ q x ∂μ := by
    have e1 : ∫ x, r x * projMean μ (Torus.cosMode k) x ∂μ =
        ∫ x, r x * (q x + β * Kop g μ q x) ∂μ :=
      integral_congr_ae (hq.2.2.mono fun x hx => by simp only [hx])
    have e : ∀ x, r x * (q x + β * Kop g μ q x) = r x * q x + β * (r x * Kop g μ q x) :=
      fun x => by ring
    have i1 : Integrable (fun x => r x * q x) μ := hm _ _ hrc hqc
    have i2 : Integrable (fun x => r x * Kop g μ q x) μ := hm _ _ hrc (hKc q)
    rw [e1]
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall e)) ?_
    rw [integral_add i1 (i2.const_mul _), integral_const_mul]
  -- step c
  have hc : ∫ x, Kop g μ r x * q x ∂μ = ∫ x, r x * Kop g μ q x ∂μ :=
    PDE.MFAdjoint.l2Inner_kop_symm' (by omega) s hs0 hsd ρ hprob ρ.continuous r q r.continuous
      q.continuous hrμ hqμ
  -- step d
  have hd' : ∫ x, r x * q x ∂μ + β * ∫ x, Kop g μ r x * q x ∂μ =
      ∫ x, projMean μ ρ x * q x ∂μ := by
    have e1 : ∫ x, projMean μ ρ x * q x ∂μ = ∫ x, (r x + β * Kop g μ r x) * q x ∂μ :=
      integral_congr_ae (hr.2.2.mono fun x hx => by simp only [hx])
    have e : ∀ x, (r x + β * Kop g μ r x) * q x = r x * q x + β * (Kop g μ r x * q x) :=
      fun x => by ring
    have i1 : Integrable (fun x => r x * q x) μ := hm _ _ hrc hqc
    have i2 : Integrable (fun x => Kop g μ r x * q x) μ := hm _ _ (hKc r) hqc
    rw [e1]
    refine Eq.trans ?_ (integral_congr_ae (Filter.Eventually.of_forall fun x => (e x).symm))
    rw [integral_add i1 (i2.const_mul _), integral_const_mul]
  -- step e
  have hρq : ∫ x, ρ x * q x = 0 := by
    have := hqμ
    rwa [trr_integral_wd hρm hρ0] at this
  have he : ∫ x, projMean μ ρ x * q x ∂μ = ∫ x, ρ x * (ρ x * q x) := by
    rw [trr_integral_wd hρm hρ0]
    have e : ∀ x, ρ x * (projMean μ ρ x * q x) = ρ x * (ρ x * q x) - pair μ ρ * (ρ x * q x) :=
      fun x => by unfold projMean; ring
    have i1 : Integrable (fun x => ρ x * (ρ x * q x)) := hmv ρ (ρ * q)
    have i2 : Integrable (fun x => ρ x * q x) := hmv ρ q
    refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall e)) ?_
    rw [integral_sub i1 (i2.const_mul _), integral_const_mul, hρq]
    ring
  rw [ha, hb, ← hc, hd', he]

end Bias

end HRS.TRR
