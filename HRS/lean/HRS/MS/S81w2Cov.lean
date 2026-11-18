import HRS.MS.S81w2Susc
import HRS.MS.ShiftFldAux28
import HRS.MS.S88BDE02

/-!
# S8.1 (worker S81W2): the spectral covariance profile of the stationary Gaussian field

For the critical thermal reference `μ = ρ dx`, spectral data `(e_l, ω_l)` whose classical orbit coefficients are
`β⟨P_μ U_tφ_α, R e_l⟩ = e^{-tω_l} a_{αl}` (hypothesis `hcoef`, the conclusion of S8.8 E02 for the retained datum), put
`Q_{αα'}(x) = β⁻¹ Σ_l a_{αl} a_{α'l} e^{-xω_l}` (`x ≥ 0`).  Then, for `t, t' ≥ 0`:

* `s81w2_susc_orbit`: `C_{β,μ}(U_tφ_α, U_{t'}φ_{α'}) = Q_{αα'}(t + t')`  (initial susceptibility covariance propagated);
* `s81w2_cov_stationary`: `C_{β,μ}(U_tφ_α, U_{t'}φ_{α'}) + noiseCov(t,t') = Q_{αα'}(|t - t'|)`  (covariance of the frozen
  stationary Gaussian field, via the Lyapunov stationarity `s79g_Kstat`; no gradient closure is needed);
* `s81w2_noiseCov_spectral`: `noiseCov(t,t') = Q_{αα'}(|t-t'|) - Q_{αα'}(t+t')`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000

noncomputable section
open MeasureTheory Filter Topology Set
open scoped ENNReal BigOperators

namespace HRS.Whole.S81W2

open HRS HRS.Whole HRS.MS.S88Breakdown HRS.MS.S79G

variable {d : ℕ}

/-- The spectral covariance profile. -/
def s81w2_Q (d : ℕ) (β : ℝ) (ρ : Euc d → ℝ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) (m : ℝ)
    (α α' : MultiIndex d) (x : ℝ) : ℝ :=
  β⁻¹ * ∑' l, u11Coef d β ρ e m α l * u11Coef d β ρ e m α' l * Real.exp (-x * om l)

theorem s81w2_memLp_of_memCb {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {f : Euc d → ℝ}
    (hf : MemCb 2 f) : MemLp f 2 μ := by
  obtain ⟨hc, hb⟩ := hf
  obtain ⟨C, hC⟩ := hb 0 (Nat.zero_le _)
  refine MemLp.of_bound (hc.continuous.aestronglyMeasurable) C (Filter.Eventually.of_forall fun x => ?_)
  have := hC ⟨x, rfl⟩
  simpa using this

section Orbit

variable {a β : ℝ} {ρ : Euc d → ℝ} {e : ℕ → Euc d → ℝ} {om : ℕ → ℝ} {m : ℝ}

/-- The orbit coefficients (the hypothesis, as produced by S8.8 E02). -/
def S81W2Coef (d : ℕ) (a β : ℝ) (ρ : Euc d → ℝ) (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ) (m : ℝ) : Prop :=
  ∀ (α : MultiIndex d) (t : ℝ), 0 ≤ t → ∀ l : ℕ,
    β * HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ)
      (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) (s88Orbit (critCoeff d a β ρ) m t α))
      (HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) (HRS.Whole.withDensityReal ρ) β (e l)) =
    Real.exp (-t * om l) * u11Coef d β ρ e m α l

theorem s81w2_susc_orbit (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) (hm : (wholeSpaceIndex d : ℝ) ≤ m)
    (hdata : IsSpectralData d β ρ e om) (hcoef : S81W2Coef d a β ρ e om m)
    (α α' : MultiIndex d) {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    Summable (fun l => u11Coef d β ρ e m α l * u11Coef d β ρ e m α' l * Real.exp (-(t + t') * om l)) ∧
      susceptibilityCov (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρ) β
        (propagatorW (critCoeff d a β ρ) 0 t (oscTestFun m α))
        (propagatorW (critCoeff d a β ρ) 0 t' (oscTestFun m α')) =
      s81w2_Q d β ρ e om m α α' (t + t') := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := Q34.isProbabilityMeasure_nu hρ.1.1
  have hreg := s88_regular_orbit hd a β ha hβ m hm ρ hρ
  have h1 : MemLp (s88Orbit (critCoeff d a β ρ) m t α) 2 (withDensityReal ρ) :=
    s81w2_memLp_of_memCb (hreg.memCb α t ht)
  have h2 : MemLp (s88Orbit (critCoeff d a β ρ) m t' α') 2 (withDensityReal ρ) :=
    s81w2_memLp_of_memCb (hreg.memCb α' t' ht')
  obtain ⟨hs, he⟩ := s81w2_susc_spectral hd ha hβ hρ hdata h1 h2
  have hfun : (fun l => s81w2_coef d β ρ e (s88Orbit (critCoeff d a β ρ) m t α) l *
      s81w2_coef d β ρ e (s88Orbit (critCoeff d a β ρ) m t' α') l) =
      fun l => u11Coef d β ρ e m α l * u11Coef d β ρ e m α' l * Real.exp (-(t + t') * om l) := by
    funext l
    have c1 := hcoef α t ht l
    have c2 := hcoef α' t' ht' l
    simp only [s81w2_coef]
    rw [c1, c2]
    have : Real.exp (-(t + t') * om l) = Real.exp (-t * om l) * Real.exp (-t' * om l) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [this]; ring
  rw [hfun] at hs he
  refine ⟨hs, ?_⟩
  exact he

theorem s81w2_Q_summable (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) (hm : (wholeSpaceIndex d : ℝ) ≤ m)
    (hdata : IsSpectralData d β ρ e om) (hcoef : S81W2Coef d a β ρ e om m)
    (α α' : MultiIndex d) {x : ℝ} (hx : 0 ≤ x) :
    Summable (fun l => u11Coef d β ρ e m α l * u11Coef d β ρ e m α' l * Real.exp (-x * om l)) := by
  have := (s81w2_susc_orbit hd ha hβ hρ hm hdata hcoef α α' hx (le_refl (0 : ℝ))).1
  simpa using this

theorem s81w2_Q_comm (α α' : MultiIndex d) (x : ℝ) :
    s81w2_Q d β ρ e om m α α' x = s81w2_Q d β ρ e om m α' α x := by
  unfold s81w2_Q
  congr 1
  refine tsum_congr fun l => ?_
  ring

theorem s81w2_noiseCov_zero {C : WholeCoeff d} {q δ : ℝ} (hδ : 0 ≤ δ) (φ ψ : Euc d → ℝ) :
    noiseCovW C q 0 δ φ ψ = 0 := by
  unfold noiseCovW
  rw [min_eq_left hδ, Set.Icc_self, setIntegral_measure_zero _ (by simp)]
  simp

theorem s81w2_cov_stationary_le (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) (hm : (wholeSpaceIndex d : ℝ) ≤ m)
    (hdata : IsSpectralData d β ρ e om) (hcoef : S81W2Coef d a β ρ e om m)
    (α α' : MultiIndex d) {t t' : ℝ} (ht : 0 ≤ t) (htt : t ≤ t') :
    susceptibilityCov (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρ) β
        (propagatorW (critCoeff d a β ρ) 0 t (oscTestFun m α))
        (propagatorW (critCoeff d a β ρ) 0 t' (oscTestFun m α')) +
      noiseCovW (critCoeff d a β ρ) β⁻¹ t t' (oscTestFun m α) (oscTestFun m α') =
    s81w2_Q d β ρ e om m α α' (t' - t) := by
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have h0 := s81w2_susc_orbit hd ha hβ hρ hm hdata hcoef α α' (le_refl (0 : ℝ)) (sub_nonneg.2 htt)
  have hρeq : ρ = thermalDensity d ((d : ℝ) / 2) a β :=
    HRS.MS.Mov0.mv0_rho_eq hd hs0.le hsd ha hβ hρ
  subst hρeq
  have K := s79g_Kstat hd hs0 hsd ha hβ hρ m α α' (τ0 := t) (δ := t' - t) ht (sub_nonneg.2 htt)
  rw [add_sub_cancel] at K
  have K' : susceptibilityCov (rieszKernel d ((d : ℝ) / 2))
        (withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)) β
        (propagatorW (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β)) 0 t (oscTestFun m α))
        (propagatorW (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β)) 0 t' (oscTestFun m α')) +
      noiseCovW (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β)) β⁻¹ t t' (oscTestFun m α)
        (oscTestFun m α') =
      susceptibilityCov (rieszKernel d ((d : ℝ) / 2))
        (withDensityReal (thermalDensity d ((d : ℝ) / 2) a β)) β
        (propagatorW (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β)) 0 0 (oscTestFun m α))
        (propagatorW (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β)) 0 (t' - t) (oscTestFun m α')) +
      noiseCovW (critCoeff d a β (thermalDensity d ((d : ℝ) / 2) a β)) β⁻¹ 0 (t' - t) (oscTestFun m α)
        (oscTestFun m α') := K
  rw [K', s81w2_noiseCov_zero (sub_nonneg.2 htt), add_zero, h0.2, zero_add]

theorem s81w2_cov_stationary (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) (hm : (wholeSpaceIndex d : ℝ) ≤ m)
    (hdata : IsSpectralData d β ρ e om) (hcoef : S81W2Coef d a β ρ e om m)
    (α α' : MultiIndex d) {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    susceptibilityCov (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρ) β
        (propagatorW (critCoeff d a β ρ) 0 t (oscTestFun m α))
        (propagatorW (critCoeff d a β ρ) 0 t' (oscTestFun m α')) +
      noiseCovW (critCoeff d a β ρ) β⁻¹ t t' (oscTestFun m α) (oscTestFun m α') =
    s81w2_Q d β ρ e om m α α' |t - t'| := by
  rcases le_total t t' with h | h
  · rw [abs_of_nonpos (by linarith), neg_sub]
    exact s81w2_cov_stationary_le hd ha hβ hρ hm hdata hcoef α α' ht h
  · have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
    have hs0 : (0 : ℝ) < (d : ℝ) / 2 := by positivity
    have hsd : (d : ℝ) / 2 < d := by linarith
    have hρeq : ρ = thermalDensity d ((d : ℝ) / 2) a β :=
      HRS.MS.Mov0.mv0_rho_eq hd hs0.le hsd ha hβ hρ
    have key := s81w2_cov_stationary_le hd ha hβ hρ hm hdata hcoef α' α ht' h
    have comm := s79g_Kcov_comm hd hs0 hsd ha hβ m α α' ht ht'
    subst hρeq
    rw [abs_of_nonneg (by linarith), s81w2_Q_comm]
    have : Kcov d ((d : ℝ) / 2) a β t t' (oscTestFun m α) (oscTestFun m α') =
        Kcov d ((d : ℝ) / 2) a β t' t (oscTestFun m α') (oscTestFun m α) := comm
    unfold Kcov at this
    exact this.trans key

theorem s81w2_noiseCov_spectral (hd : 2 ≤ d) (ha : 0 < a) (hβ : 0 < β)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) (hm : (wholeSpaceIndex d : ℝ) ≤ m)
    (hdata : IsSpectralData d β ρ e om) (hcoef : S81W2Coef d a β ρ e om m)
    (α α' : MultiIndex d) {t t' : ℝ} (ht : 0 ≤ t) (ht' : 0 ≤ t') :
    noiseCovW (critCoeff d a β ρ) β⁻¹ t t' (oscTestFun m α) (oscTestFun m α') =
      s81w2_Q d β ρ e om m α α' |t - t'| - s81w2_Q d β ρ e om m α α' (t + t') := by
  have h1 := s81w2_cov_stationary hd ha hβ hρ hm hdata hcoef α α' ht ht'
  have h2 := (s81w2_susc_orbit hd ha hβ hρ hm hdata hcoef α α' ht ht').2
  linarith

end Orbit

end HRS.Whole.S81W2
