import HRS.MS.S88BDE02
import HRS.MS.SpecAux103
import HRS.MS.S81w2Cov

/-!
# S8.1 (worker S81W2): one retained spectral datum

`s81w2_spectral_retained`: for the critical thermal reference there are spectral data `(e_l, ω_l)` (`IsSpectralData`) that
simultaneously carry
* the exact classical orbit coefficients `β⟨P_μ U_tφ_α, R e_l⟩ = e^{-tω_l} a_{αl}` (`S81W2Coef`; S8.8 E02),
* the `L⁴` gradient bound `‖∇e_l‖_{L⁴(μ)} ≤ C₄ e^{t₀ω_l}` (S8.7),
* the S8.7 adapted coupling claim `S8pCouplingClaim` for every `τ > 4t₀`.
This is the "one spectral witness" of the Pro paper: `spectral_space_proof` and `s88_classical_spectral_coefficients`
each choose their eigenvector datum separately; here both are read off the single datum `D` of `s88_spectral_witness`
(the coefficient proof of E02 is repeated verbatim for that `D`).
-/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.Whole.S81W2

open HRS HRS.Whole HRS.MS.Spec HRS.MS.MovDec HRS.MS.MovLin HRS.MS.MovAdj HRS.MS.S52B HRS.MS.S88Breakdown

local notation "𝓢R" => SchwartzMap (Euc _) ℝ

set_option maxHeartbeats 3200000 in
theorem s81w2_spectral_retained {d : ℕ} (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (m : ℝ) (hm : (wholeSpaceIndex d : ℝ) ≤ m) (ρ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) :
    ∃ (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ), IsSpectralData d β ρ e om ∧ S81W2Coef d a β ρ e om m ∧
      ∃ t₀ C4 : ℝ, 0 < t₀ ∧
        (∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 (withDensityReal ρ) ≤
          ENNReal.ofReal (C4 * Real.exp (t₀ * om l))) ∧
        ∀ τ : ℝ, 4 * t₀ < τ → S8pCouplingClaim d a β ρ e om τ := by
  obtain ⟨M, h, D, hdata⟩ := s88_spectral_witness hd a β ha hβ ρ hρ
  obtain ⟨t₀, C4, ht₀, hL4⟩ := s8p_L4_witness hd ha hβ hρ h D
  refine ⟨_, _, hdata, ?_, t₀, C4, ht₀, hL4, fun τ hτ => s8p_coupling_claim hd ha hβ hρ hdata ht₀ hL4 hτ⟩
  unfold S81W2Coef
  intro α t ht l
  have hd1 : 1 ≤ d := by omega
  have hs : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  have H : Mov2dTh d ((d : ℝ) / 2) β a ρ :=
    ⟨hd, by positivity, by linarith, hβ, ha, hρ⟩
  obtain ⟨hρ', hE, -⟩ := mov2e_thermal H.hd H.hs0 H.hsd H.hβ H.hq H.hρ
  obtain ⟨ψ0, hψ0⟩ := mov2d_sqrt_schwartz H
  have hmean : ∫ x, Real.sqrt (ρ x) * D.φ l x = 0 :=
    s8p_mean_zero H ψ0 hψ0 (D.v l) (D.φ l) (D.hv l)
  -- the classical solution and the identification of the orbit
  have hreg := s88_regular_orbit hd a β ha hβ m hm ρ hρ
  obtain ⟨f, hf⟩ := hreg.classical α t ht
  obtain ⟨θ, hO, huniq⟩ := s88_setup hd ha hβ t hρ
  rw [← s88_coeff_eq] at huniq
  have hprop : s88Orbit (critCoeff d a β ρ) m t α = f 0 := by
    have h1 := s52b_prop_isClassical (C := critCoeff d a β ρ) ⟨f, hf⟩
    have := huniq t ⟨ht, le_rfl⟩ _ _ _ h1 hf 0 ⟨le_rfl, ht⟩
    exact this
  have hr0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) t := ⟨le_rfl, ht⟩
  -- integrability of the two pairings
  have hsq : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
    rw [← hψ0]; exact ψ0.memLp 2
  have hI3 : Integrable (fun x => Real.sqrt (ρ x) * D.φ l x) := hsq.integrable_mul ((D.φ l).memLp 2)
  have hIf : Integrable (fun x => f 0 x * (Real.sqrt (ρ x) * D.φ l x)) := by
    obtain ⟨hmeas, B, hB⟩ := s67_f_aux hf hr0
    exact hI3.bdd_mul (c := B) hmeas
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hIphi : Integrable (fun x => oscTestFun m α x * (Real.sqrt (ρ x) * D.φ l x)) := by
    obtain ⟨hmeas, B, hB⟩ := s67_phi_aux hf ht
    exact hI3.bdd_mul (c := B) hmeas
      (Filter.Eventually.of_forall fun x => by rw [Real.norm_eq_abs]; exact hB x)
  have hP1 := s88_pair_eq hd1 hs H.hsd hρ' hE (fun x => h.le x) hβ (D.φ l) hmean hIf
  have hP2 := s88_pair_eq hd1 hs H.hsd hρ' hE (fun x => h.le x) hβ (D.φ l) hmean hIphi
  -- the bridge
  have hbr := s67_bridge H ψ0 hψ0 hf hr0 (D.hv l)
  rw [sub_zero, s88_T_eigen H ψ0 hψ0 D l ht] at hbr
  have hsm : ∀ᵐ x ∂(volume : Measure (Euc d)),
      movFun (Real.exp (-t * D.om l) • D.v l) x = Real.exp (-t * D.om l) * D.φ l x := by
    filter_upwards [Lp.coeFn_smul (Real.exp (-t * D.om l))
      ((D.v l : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d))), D.hv l] with x h1 h2
    change (Real.exp (-t * D.om l) • (D.v l : Lp ℝ 2 (volume : Measure (Euc d)))) x = _
    rw [h1, Pi.smul_apply, smul_eq_mul]
    change _ * movFun (D.v l) x = _
    rw [h2]
  have hL : ∫ x, f 0 x * (Real.sqrt (ρ x) * movFun (D.v l) x) =
      ∫ x, f 0 x * (Real.sqrt (ρ x) * D.φ l x) :=
    integral_congr_ae (by filter_upwards [D.hv l] with x hx; rw [hx])
  have hR : ∫ x, oscTestFun m α x * (Real.sqrt (ρ x) *
      movFun (Real.exp (-t * D.om l) • D.v l) x) =
      Real.exp (-t * D.om l) * ∫ x, oscTestFun m α x * (Real.sqrt (ρ x) * D.φ l x) := by
    rw [← integral_const_mul]
    refine integral_congr_ae ?_
    filter_upwards [hsm] with x hx
    rw [hx]; ring
  rw [hprop]
  show _ = Real.exp (-t * D.om l) * (β * HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ)
    (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) (oscTestFun m α)) _)
  rw [hP1, hP2, ← hL, hbr, hR]

/-- The one spectral witness of the Pro paper, together with the spectral form of the covariance of the frozen stationary
Gaussian field (`C₀ + noiseCov = Q(|t - t'|)`) and of its pieces. -/
theorem s81w2_witness {d : ℕ} (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (m : ℝ) (hm : (wholeSpaceIndex d : ℝ) ≤ m) (ρ : Euc d → ℝ)
    (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) :
    ∃ (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ), IsSpectralData d β ρ e om ∧
      (∃ t₀ C4 : ℝ, 0 < t₀ ∧
        (∀ l, eLpNorm (fun x => ‖gradient (e l) x‖) 4 (withDensityReal ρ) ≤
          ENNReal.ofReal (C4 * Real.exp (t₀ * om l))) ∧
        ∀ τ : ℝ, 4 * t₀ < τ → S8pCouplingClaim d a β ρ e om τ) ∧
      ∀ (α α' : MultiIndex d) (t t' : ℝ), 0 ≤ t → 0 ≤ t' →
        susceptibilityCov (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρ) β
            (propagatorW (critCoeff d a β ρ) 0 t (oscTestFun m α))
            (propagatorW (critCoeff d a β ρ) 0 t' (oscTestFun m α')) =
          s81w2_Q d β ρ e om m α α' (t + t') ∧
        susceptibilityCov (rieszKernel d ((d : ℝ) / 2)) (withDensityReal ρ) β
            (propagatorW (critCoeff d a β ρ) 0 t (oscTestFun m α))
            (propagatorW (critCoeff d a β ρ) 0 t' (oscTestFun m α')) +
          noiseCovW (critCoeff d a β ρ) β⁻¹ t t' (oscTestFun m α) (oscTestFun m α') =
          s81w2_Q d β ρ e om m α α' |t - t'| ∧
        noiseCovW (critCoeff d a β ρ) β⁻¹ t t' (oscTestFun m α) (oscTestFun m α') =
          s81w2_Q d β ρ e om m α α' |t - t'| - s81w2_Q d β ρ e om m α α' (t + t') := by
  obtain ⟨e, om, hdata, hcoef, hrest⟩ := s81w2_spectral_retained hd a β ha hβ m hm ρ hρ
  refine ⟨e, om, hdata, hrest, fun α α' t t' ht ht' => ⟨?_, ?_, ?_⟩⟩
  · exact (s81w2_susc_orbit hd ha hβ hρ hm hdata hcoef α α' ht ht').2
  · exact s81w2_cov_stationary hd ha hβ hρ hm hdata hcoef α α' ht ht'
  · exact s81w2_noiseCov_spectral hd ha hβ hρ hm hdata hcoef α α' ht ht'

end HRS.Whole.S81W2
