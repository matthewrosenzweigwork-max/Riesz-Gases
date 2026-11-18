import HRS.Main.HeadlineEquilibrium
import HRS.Equilibrium.StaticLimitsAux
import HRS.Sections.Q41Aux14
import HRS.PDE.MeanFieldThermalUnique

/-!
# FamW-A: the zero-field thermal state and the cosine susceptibility covariance

For `d ≥ 2`, `0 ≤ s < d`, `β > 0`, `k ≠ 0`:

* `thermal_rateV_zero`: a thermal density for the zero-field potential `rateV k β 0 = 0` is the
  uniform density `1` (the constant `1` is thermal because the periodic Riesz kernel has mean zero,
  and thermal densities are unique).
* `susceptibilityCov_one_cos`: for the uniform measure, `C_{β,Leb}(cos_k, cos_k)
  = 1 / (2 (1 + β ĝ(k)))` (the kernel acts on `cos_k` with eigenvalue `ĝ(k)`, `∫ cos_k² = 1/2`).
* `susceptibilityCov_cos_rateV_zero`: the combined statement for any thermal `ρ` of `rateV k β 0`.

Normalisation check: for `ψ = √2 cos_{e_j}` the repository has `StaticLimitsAux.susc_cos`
(`C = 1/(1+βĝ)`); here `ψ = cos_k`, so the constant is `1/2` of that.
-/

noncomputable section

open MeasureTheory Filter Topology

namespace HRS.ME.FamW

variable {d : ℕ} {s : ℝ}

/-! ### Mode integrals -/

lemma integral_cosMode_ne (k : Lattice d) (hk : k ≠ 0) : ∫ x : Torus d, Torus.cosMode k x = 0 := by
  have h := integral_re (𝕜 := ℂ) (μ := (volume : Measure (Torus d))) (Torus.integrable_mode k)
  simp only [RCLike.re_to_complex] at h
  have h2 : ∫ x : Torus d, Torus.cosMode k x = (∫ x : Torus d, Torus.mode k x).re := h
  rw [h2, Torus.integral_mode, if_neg hk]; simp

lemma cosMode_sq (k : Lattice d) (x : Torus d) :
    Torus.cosMode k x ^ 2 = (1 + Torus.cosMode (k + k) x) / 2 := by
  have hn := Torus.norm_mode k x
  have h1 : (Torus.mode k x).re ^ 2 + (Torus.mode k x).im ^ 2 = 1 := by
    have := Complex.sq_norm (Torus.mode k x)
    rw [hn, Complex.normSq_apply] at this
    nlinarith
  have h2 : Torus.cosMode (k + k) x = (Torus.mode k x).re ^ 2 - (Torus.mode k x).im ^ 2 := by
    simp only [Torus.cosMode, Torus.mode_add, Complex.mul_re]; ring
  rw [h2]; simp only [Torus.cosMode]; nlinarith

lemma integral_cosMode_sq (k : Lattice d) (hk : k ≠ 0) :
    ∫ x : Torus d, Torus.cosMode k x ^ 2 = 1 / 2 := by
  have hk2 : k + k ≠ 0 := by
    intro h
    apply hk
    funext i
    have := congrFun h i
    simp only [Pi.add_apply, Pi.zero_apply] at this
    simp only [Pi.zero_apply]; omega
  have hint : Integrable (fun x : Torus d => Torus.cosMode (k + k) x) :=
    (Torus.continuous_cosMode _).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  simp_rw [cosMode_sq k]
  rw [integral_div, integral_add (integrable_const _) hint, integral_cosMode_ne _ hk2]
  simp

/-! ### (a) The zero-field thermal density -/

lemma rateV_zero_apply (k : Lattice d) (β : ℝ) (x : Torus d) : rateV k β 0 x = 0 := by
  simp [rateV]

lemma convFun_one (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (x : Torus d) :
    convFun (periodicRiesz d s) (fun _ => (1 : ℝ)) x = 0 := by
  have : (volume : Measure (Torus d)).IsNegInvariant :=
    MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
  unfold convFun
  simp only [mul_one]
  rw [integral_sub_left_eq_self (periodicRiesz d s) (volume : Measure (Torus d)) x]
  exact (integral_periodicRiesz hd hs0 hsd).2

lemma isThermal_one (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (k : Lattice d) (β : ℝ) :
    IsThermalDensity (periodicRiesz d s) (rateV k β 0) β (fun _ => (1 : ℝ)) := by
  refine ⟨⟨fun _ => zero_le_one, measurable_const, by simp⟩, fun x => ?_⟩
  simp [rateV_zero_apply, convFun_one hd hs0 hsd]

/-- The thermal density of the zero field is uniform. -/
theorem thermal_rateV_zero (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) (rateV k β 0) β ρ) :
    ρ = fun _ => (1 : ℝ) := by
  have hVc : Continuous (rateV k β 0) := by
    have : rateV k β 0 = fun _ => 0 := funext (rateV_zero_apply k β)
    rw [this]; exact continuous_const
  obtain ⟨hpos, hcont⟩ := Q41.q41_thermal_pos_cont hd hs0 hsd hβ hVc hρ
  exact (PDE.MFThermal.thermal_unique hd s hs0 hsd β hβ (rateV k β 0) ρ (fun _ => 1) hρ hcont hpos
    (isThermal_one hd hs0 hsd k β) continuous_const (fun _ => one_pos)).symm

/-- `ρ`-free corollary: `fun _ => 1` is the unique thermal density of the zero field. -/
theorem thermal_rateV_zero_iff (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (ρ : Torus d → ℝ) :
    IsThermalDensity (periodicRiesz d s) (rateV k β 0) β ρ ↔ ρ = fun _ => (1 : ℝ) :=
  ⟨thermal_rateV_zero hd hs0 hsd hβ k ρ, fun h => h ▸ isThermal_one hd hs0 hsd k β⟩

/-! ### (b) The covariance of `cos_k` under the uniform measure -/

theorem susceptibilityCov_one_cos (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ} (hβ : 0 < β)
    (k : Lattice d) (hk : k ≠ 0) :
    susceptibilityCov (periodicRiesz d s) (withDensityReal (fun _ : Torus d => (1 : ℝ))) β
      (Torus.cosMode k) (Torus.cosMode k) = 1 / (2 * (1 + β * rieszCoeff d s k)) := by
  set g := periodicRiesz d s with hgdef
  set ψ : Torus d → ℝ := Torus.cosMode k with hψdef
  set lam := rieszCoeff d s k with hlam
  have hlam0 : 0 ≤ lam := (rieszCoeff_pos hd hs0 hsd k hk).le
  have hψc : Continuous ψ := Torus.continuous_cosMode k
  have hψb : ∀ x, |ψ x| ≤ 1 := fun x => by
    have := Torus.norm_cosMode_le k x
    rwa [Real.norm_eq_abs] at this
  have hvol : withDensityReal (fun _ : Torus d => (1:ℝ)) = volume := by
    unfold withDensityReal; simp
  have hψm : MemLp ψ 2 (volume : Measure (Torus d)) :=
    MemLp.of_bound hψc.aestronglyMeasurable 1 (Filter.Eventually.of_forall fun x => by
      simpa using hψb x)
  have hpair : pair volume ψ = 0 := integral_cosMode_ne k hk
  have hKψ : ∀ x, ∫ y, g (x - y) * ψ y = lam * ψ x := fun x =>
    StaticLimitsAux.conv_cos hd hs0 hsd k x
  have ha : 0 < 1 + β * lam := by positivity
  set a : ℝ := 1 / (1 + β * lam) with hadef
  have ha1 : a * (1 + β * lam) = 1 := by rw [hadef]; field_simp
  set h : Torus d → ℝ := fun x => a * ψ x with hh
  have hhc : Continuous h := continuous_const.mul hψc
  have e1 : ∀ x, ∫ y, g (x - y) * h y = a * lam * ψ x := by
    intro x
    have : (fun y => g (x - y) * h y) = fun y => a * (g (x - y) * ψ y) := by
      funext y; simp only [hh]; ring
    rw [this, integral_const_mul, hKψ x]; ring
  have hKh : ∀ x, Kop g volume h x = a * lam * ψ x := by
    intro x
    unfold Kop projMean
    have e2 : pair volume (fun x => ∫ y, g (x - y) * h y ∂volume) = 0 := by
      have : (fun x => ∫ y, g (x - y) * h y ∂volume) = fun x => a * lam * ψ x := funext e1
      rw [this]; unfold pair; rw [integral_const_mul]
      have : ∫ x, ψ x = 0 := hpair
      rw [this, mul_zero]
    show (∫ y, g (x - y) * h y ∂volume) - pair volume (fun x => ∫ y, g (x - y) * h y ∂volume) = _
    rw [e2, sub_zero]; exact e1 x
  have hresp : IsResponse g volume β ψ h := by
    refine ⟨?_, ?_, Filter.Eventually.of_forall fun x => ?_⟩
    · exact MemLp.of_bound hhc.aestronglyMeasurable a (Filter.Eventually.of_forall fun x => by
        simp only [hh, Real.norm_eq_abs, abs_mul, abs_of_pos (show 0 < a by positivity)]
        exact mul_le_of_le_one_right (by positivity) (hψb x))
    · unfold pair; simp only [hh]; rw [integral_const_mul]
      have : ∫ x, ψ x = 0 := hpair
      rw [this, mul_zero]
    · rw [hKh x]; simp only [hh, projMean, hpair]
      have : a * ψ x + β * (a * lam * ψ x) = (a * (1 + β * lam)) * ψ x := by ring
      rw [this, ha1]; ring
  have hprob : IsProbDensity (fun _ : Torus d => (1:ℝ)) :=
    ⟨fun _ => zero_le_one, measurable_const, by simp⟩
  obtain ⟨h0, hh0, huniq⟩ := exists_unique_response_one_le (by omega : 1 ≤ d) hs0 hsd
    (fun _ => 1) hprob 1 (fun _ => le_rfl) β hβ.le ψ (by rw [hvol]; exact hψm)
  rw [hvol] at hh0 huniq
  have hex : ∃ h', IsResponse g volume β ψ h' := ⟨h, hresp⟩
  have hch : IsResponse g volume β ψ (responseInverse g volume β ψ) := by
    unfold responseInverse; rw [dif_pos hex]; exact hex.choose_spec
  have hae : responseInverse g volume β ψ =ᵐ[volume] h :=
    (huniq _ hch).trans (huniq _ hresp).symm
  rw [hvol]
  unfold susceptibilityCov l2Inner
  have : ∀ᵐ x ∂(volume : Measure (Torus d)), projMean volume ψ x * responseInverse g volume β ψ x
      = a * (ψ x) ^ 2 := by
    filter_upwards [hae] with x hx
    rw [hx]; simp only [projMean, hpair, hh]; ring
  rw [integral_congr_ae this, integral_const_mul]
  have h2 : ∫ x, (ψ x) ^ 2 = 1 / 2 := integral_cosMode_sq k hk
  rw [h2, hadef]; field_simp

/-! ### (c) Combined statement -/

theorem susceptibilityCov_cos_rateV_zero (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {β : ℝ}
    (hβ : 0 < β) (k : Lattice d) (hk : k ≠ 0) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) (rateV k β 0) β ρ) :
    susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β
      (Torus.cosMode k) (Torus.cosMode k) = 1 / (2 * (1 + β * rieszCoeff d s k)) := by
  rw [thermal_rateV_zero hd hs0 hsd hβ k ρ hρ]
  exact susceptibilityCov_one_cos hd hs0 hsd hβ k hk

end HRS.ME.FamW
