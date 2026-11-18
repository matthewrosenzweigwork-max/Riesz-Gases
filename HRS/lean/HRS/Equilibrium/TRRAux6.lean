/-
# TRR helper 6: the density curve `θ ↦ ρ_θ ∈ C(T^d)` and its derivative (clauses 2, 3).
-/
import HRS.Equilibrium.TRRAux5

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.TRR

variable {d : ℕ} {s β : ℝ}

section Curve

variable (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (hβ : 0 < β) (k : Lattice d)

/-- `w_θ = Λ⁻¹(θ cos_k)` -/
def Wc (θ : ℝ) : Cb d := Wsol hd hs0 hsd hβ (θ • cosC k)

/-- `ρ_θ = N(w_θ)` -/
def Rc (θ : ℝ) : Cb d := Nc (Wc hd hs0 hsd hβ k θ)

lemma contDiff_Wc : ContDiff ℝ InfOrd (Wc hd hs0 hsd hβ k) :=
  (contDiff_Wsol hd hs0 hsd hβ).comp (contDiff_id.smul contDiff_const)

lemma contDiff_Rc : ContDiff ℝ InfOrd (Rc hd hs0 hsd hβ k) :=
  contDiff_Nc.comp (contDiff_Wc hd hs0 hsd hβ k)

/-- derivative of `w_θ` -/
def Wd (θ : ℝ) : Cb d := deriv (Wc hd hs0 hsd hβ k) θ

lemma hasDerivAt_Wc (θ : ℝ) : HasDerivAt (Wc hd hs0 hsd hβ k) (Wd hd hs0 hsd hβ k θ) θ :=
  (((contDiff_Wc hd hs0 hsd hβ k).differentiable (by simp [InfOrd])) θ).hasDerivAt

lemma Wd_eq (θ : ℝ) :
    Dlam (trr_gint hd hs0 hsd) β (Wc hd hs0 hsd hβ k θ) (Wd hd hs0 hsd hβ k θ) = cosC k := by
  have h1 := (hasFDerivAt_Lam (trr_gint hd hs0 hsd) β (Wc hd hs0 hsd hβ k θ)).comp_hasDerivAt θ
    (hasDerivAt_Wc hd hs0 hsd hβ k θ)
  have e : (Lam (trr_gint hd hs0 hsd) β ∘ Wc hd hs0 hsd hβ k) = fun θ' => θ' • cosC k :=
    funext fun θ' => Wsol_spec hd hs0 hsd hβ _
  rw [e] at h1
  have h2 : HasDerivAt (fun θ' : ℝ => θ' • cosC k) ((1 : ℝ) • cosC k) θ :=
    (hasDerivAt_id θ).smul_const (cosC k)
  simpa using h1.unique h2

lemma hasDerivAt_Rc (θ : ℝ) :
    HasDerivAt (Rc hd hs0 hsd hβ k) (Nder (Wc hd hs0 hsd hβ k θ) (Wd hd hs0 hsd hβ k θ)) θ :=
  (hasFDerivAt_Nc (Wc hd hs0 hsd hβ k θ)).comp_hasDerivAt θ (hasDerivAt_Wc hd hs0 hsd hβ k θ)

/-- `q_θ = ∂_θρ_θ / ρ_θ` -/
def qc (θ : ℝ) : Cb d :=
  Wd hd hs0 hsd hβ k θ - intC (Rc hd hs0 hsd hβ k θ * Wd hd hs0 hsd hβ k θ) • (1 : Cb d)

lemma qc_apply (θ : ℝ) (x : Torus d) :
    qc hd hs0 hsd hβ k θ x =
      Wd hd hs0 hsd hβ k θ x - intC (Rc hd hs0 hsd hβ k θ * Wd hd hs0 hsd hβ k θ) := by
  simp [qc]

lemma Rd_apply (θ : ℝ) (x : Torus d) :
    Nder (Wc hd hs0 hsd hβ k θ) (Wd hd hs0 hsd hβ k θ) x =
      Rc hd hs0 hsd hβ k θ x * qc hd hs0 hsd hβ k θ x := by
  rw [trr_Nder_apply, qc_apply]; rfl

lemma Rc_pos (θ : ℝ) (x : Torus d) : 0 < Rc hd hs0 hsd hβ k θ x := Nc_pos _ x

lemma Rc_int (θ : ℝ) : ∫ x, Rc hd hs0 hsd hβ k θ x = 1 := by
  have := intC_Nc (Wc hd hs0 hsd hβ k θ)
  rwa [intC_apply] at this

lemma trr_eq_pt (θ : ℝ) (x : Torus d) :
    Wd hd hs0 hsd hβ k θ x + β * convFun (periodicRiesz d s)
      (fun y => Rc hd hs0 hsd hβ k θ y * qc hd hs0 hsd hβ k θ y) x = Torus.cosMode k x := by
  have h : Dlam (trr_gint hd hs0 hsd) β (Wc hd hs0 hsd hβ k θ) (Wd hd hs0 hsd hβ k θ) x =
      cosC k x := by rw [Wd_eq hd hs0 hsd hβ k θ]
  rw [trr_Dlam_apply] at h
  have e : Torus.cosMode k x = cosC k x := rfl
  rw [e, ← h]
  simp only [qc_apply]
  rfl

theorem trr_response_q (θ : ℝ) :
    IsResponse (periodicRiesz d s) (withDensityReal (Rc hd hs0 hsd hβ k θ)) β (Torus.cosMode k)
      (qc hd hs0 hsd hβ k θ) := by
  set ρ := Rc hd hs0 hsd hβ k θ with hρ
  set q := qc hd hs0 hsd hβ k θ with hq
  set g := periodicRiesz d s with hg
  have hprob : IsProbDensity (ρ : Torus d → ℝ) := trr_isProb_Nc _
  have hρm : Measurable (ρ : Torus d → ℝ) := ρ.continuous.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (Rc_pos hd hs0 hsd hβ k θ x).le
  have : IsProbabilityMeasure (withDensityReal (ρ : Torus d → ℝ)) := isProb_withDensityReal hprob
  have hi : ∀ f : Cb d, Integrable (fun x => f x) := fun f =>
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  set v := Wd hd hs0 hsd hβ k θ with hv
  set c := intC (ρ * v) with hc
  have hqx : ∀ x, q x = v x - c := qc_apply hd hs0 hsd hβ k θ
  have hρint : ∫ x, ρ x = 1 := Rc_int hd hs0 hsd hβ k θ
  have hρv : ∫ x, ρ x * v x = c := rfl
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
  have hFv : ∀ y, β * F y = Torus.cosMode k y - v y := fun y => by
    have := trr_eq_pt hd hs0 hsd hβ k θ y
    linarith
  have hic : Integrable (fun y => ρ y * Torus.cosMode k y) := hi (ρ * cosC k)
  have hiv : Integrable (fun y => ρ y * v y) := hi (ρ * v)
  have h1 : β * ∫ y, ρ y * F y = (∫ y, ρ y * Torus.cosMode k y) - c := by
    rw [← integral_const_mul]
    have : ∀ y, β * (ρ y * F y) = ρ y * Torus.cosMode k y - ρ y * v y := fun y => by
      calc β * (ρ y * F y) = ρ y * (β * F y) := by ring
        _ = _ := by rw [hFv y]; ring
    simp only [this]
    rw [integral_sub hic hiv, hρv]
  unfold projMean pair
  rw [trr_integral_wd hρm hρ0, mul_sub]
  linarith [hqx x, hFv x, h1]


lemma trr_deriv_rho (θ : ℝ) (x : Torus d) :
    HasDerivAt (fun θ' => Rc hd hs0 hsd hβ k θ' x)
      (Rc hd hs0 hsd hβ k θ x * qc hd hs0 hsd hβ k θ x) θ := by
  have := (ContinuousMap.evalCLM ℝ x).hasFDerivAt.comp_hasDerivAt θ
    (hasDerivAt_Rc hd hs0 hsd hβ k θ)
  rw [← Rd_apply hd hs0 hsd hβ k θ x]
  exact this

lemma trr_responseInverse_ae (θ : ℝ) :
    responseInverse (periodicRiesz d s) (withDensityReal (Rc hd hs0 hsd hβ k θ)) β
        (Torus.cosMode k) =ᵐ[withDensityReal (Rc hd hs0 hsd hβ k θ)] qc hd hs0 hsd hβ k θ := by
  set ρ := Rc hd hs0 hsd hβ k θ with hρ
  have hprob : IsProbDensity (ρ : Torus d → ℝ) := trr_isProb_Nc _
  obtain ⟨Λ, hΛ⟩ : ∃ Λ : ℝ, ∀ x, ρ x ≤ Λ :=
    ⟨‖ρ‖, fun x => (le_abs_self _).trans (by simpa using ρ.norm_coe_le_norm x)⟩
  have : IsProbabilityMeasure (withDensityReal (ρ : Torus d → ℝ)) := isProb_withDensityReal hprob
  obtain ⟨h0, -, huniq⟩ := exists_unique_response hd hs0 hsd ρ hprob Λ hΛ β hβ.le
    (Torus.cosMode k) (trr_memLp_cont _ (cosC k))
  have hq := trr_response_q hd hs0 hsd hβ k θ
  have hex : ∃ h, IsResponse (periodicRiesz d s) (withDensityReal ρ) β (Torus.cosMode k) h :=
    ⟨_, hq⟩
  have e : responseInverse (periodicRiesz d s) (withDensityReal ρ) β (Torus.cosMode k) =
      hex.choose := by
    unfold responseInverse
    simp only [hex, dite_true]
  rw [e]
  exact (huniq _ hex.choose_spec).trans (huniq _ hq).symm


lemma trr_rho_eq_Rc {ρ : Torus d → ℝ} (θ : ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) (rateV k β θ) β ρ) :
    ρ = ⇑(Rc hd hs0 hsd hβ k θ) := trr_rho_eq hd hs0 hsd hβ k θ hρ

lemma trr_susc_eq (θ : ℝ) :
    susceptibilityCov (periodicRiesz d s) (withDensityReal (Rc hd hs0 hsd hβ k θ)) β
        (Torus.cosMode k) (Torus.cosMode k) =
      intC (cosC k * Nder (Wc hd hs0 hsd hβ k θ) (Wd hd hs0 hsd hβ k θ)) := by
  set ρ := Rc hd hs0 hsd hβ k θ with hρ
  set q := qc hd hs0 hsd hβ k θ with hq
  have hρm : Measurable (ρ : Torus d → ℝ) := ρ.continuous.measurable
  have hρ0 : ∀ x, 0 ≤ ρ x := fun x => (Rc_pos hd hs0 hsd hβ k θ x).le
  have hi : ∀ f : Cb d, Integrable (fun x => f x) := fun f =>
    f.continuous.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hpq : ∫ x, ρ x * q x = 0 := by
    have := (trr_response_q hd hs0 hsd hβ k θ).2.1
    unfold pair at this
    rwa [trr_integral_wd hρm hρ0] at this
  set pc : ℝ := ∫ x, ρ x * Torus.cosMode k x with hpc
  unfold susceptibilityCov l2Inner
  rw [integral_congr_ae ((trr_responseInverse_ae hd hs0 hsd hβ k θ).mono fun x hx => by rw [hx]),
    trr_integral_wd hρm hρ0]
  have e1 : ∀ x, ρ x * (projMean (withDensityReal ρ) (Torus.cosMode k) x * q x) =
      (cosC k * ρ * q) x - pc * (ρ x * q x) := fun x => by
    unfold projMean pair
    rw [trr_integral_wd hρm hρ0]
    simp only [ContinuousMap.mul_apply]
    show _ = Torus.cosMode k x * ρ x * q x - _
    ring
  refine Eq.trans (integral_congr_ae (Filter.Eventually.of_forall e1)) ?_
  have hiρq : Integrable (fun x => ρ x * q x) := hi (ρ * q)
  rw [integral_sub (hi _) (hiρq.const_mul pc), integral_const_mul]
  show _ = ∫ x, (cosC k * Nder (Wc hd hs0 hsd hβ k θ) (Wd hd hs0 hsd hβ k θ)) x
  have e2 : ∀ x, (cosC k * Nder (Wc hd hs0 hsd hβ k θ) (Wd hd hs0 hsd hβ k θ)) x =
      (cosC k * ρ * q) x := fun x => by
    simp only [ContinuousMap.mul_apply]
    rw [Rd_apply]; ring
  simp only [e2]
  have : ∫ x, ρ x * q x = 0 := hpq
  rw [this]; ring

include hd hs0 hsd hβ in
theorem trr_clause2 (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) (θ : ℝ) :
    IsResponse (periodicRiesz d s) (withDensityReal (ρ θ)) β (Torus.cosMode k)
      (fun x => deriv (fun θ' => ρ θ' x) θ / ρ θ x) := by
  have hρe : ∀ θ', ρ θ' = ⇑(Rc hd hs0 hsd hβ k θ') := fun θ' => trr_rho_eq_Rc hd hs0 hsd hβ k θ' (hρ θ')
  have : (fun x => deriv (fun θ' => ρ θ' x) θ / ρ θ x) = ⇑(qc hd hs0 hsd hβ k θ) := by
    funext x
    simp only [hρe]
    rw [(trr_deriv_rho hd hs0 hsd hβ k θ x).deriv]
    have := (Rc_pos hd hs0 hsd hβ k θ x).ne'
    field_simp
  rw [this, hρe θ]
  exact trr_response_q hd hs0 hsd hβ k θ

include hd hs0 hsd hβ in
theorem trr_clause3 (ρ : ℝ → Torus d → ℝ)
    (hρ : ∀ θ, IsThermalDensity (periodicRiesz d s) (rateV k β θ) β (ρ θ)) (θ : ℝ) :
    HasDerivAt (fun θ' => pair (withDensityReal (ρ θ')) (Torus.cosMode k))
      (susceptibilityCov (periodicRiesz d s) (withDensityReal (ρ θ)) β
        (Torus.cosMode k) (Torus.cosMode k)) θ := by
  have hρe : ∀ θ', ρ θ' = ⇑(Rc hd hs0 hsd hβ k θ') := fun θ' => trr_rho_eq_Rc hd hs0 hsd hβ k θ' (hρ θ')
  set ℓ : Cb d →L[ℝ] ℝ := intC.comp (ContinuousLinearMap.mul ℝ (Cb d) (cosC k)) with hℓ
  have hpair : ∀ θ', pair (withDensityReal (ρ θ')) (Torus.cosMode k) = ℓ (Rc hd hs0 hsd hβ k θ') := by
    intro θ'
    rw [hρe θ']
    unfold pair
    rw [trr_integral_wd (Rc hd hs0 hsd hβ k θ').continuous.measurable (fun x => (Rc_pos hd hs0 hsd hβ k θ' x).le)]
    simp only [hℓ, ContinuousLinearMap.coe_comp', Function.comp_apply, ContinuousLinearMap.mul_apply',
      intC_apply, ContinuousMap.mul_apply]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    show _ = Torus.cosMode k x * _
    ring
  have h1 := ℓ.hasFDerivAt.comp_hasDerivAt θ (hasDerivAt_Rc hd hs0 hsd hβ k θ)
  have e1 : (fun θ' => pair (withDensityReal (ρ θ')) (Torus.cosMode k)) =
      ℓ ∘ Rc hd hs0 hsd hβ k := funext hpair
  rw [e1]
  convert h1 using 1
  rw [hρe θ, trr_susc_eq hd hs0 hsd hβ k θ]
  rfl

end Curve
