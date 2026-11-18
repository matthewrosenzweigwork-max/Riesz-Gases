import HRS.MS.S88BDA01
import HRS.MS.S88BDE01

/-!
# S8.8.E02: constructed spectral witnesses carried through the classical adjoint bridge

`s88_classical_spectral_coefficients`: the spectral data `e_l = s8p_E (φ_l)`, `ω_l` constructed from the Schwartz
eigenvectors `v_l` of the S6.2 semigroup (`s8p_eigData`, the same witnesses as `s8p_exists_spectralData`) satisfy
`β⟨P_μ U_t φ_α, R e_l⟩ = e^{-tω_l} β⟨P_μ φ_α, R e_l⟩`.  The semigroup evolution `T(t) v_l = e^{-tω_l} v_l` is recovered
by `s88_right_eigen_orbit` from the generator equation; the classical adjoint solution is paired with `v_l` through the
S6.7 bridge `s67_bridge`, and the `L²(μ)`-pairing is converted into the Lebesgue pairing `∫ u √ρ φ_l`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal RealInnerProductSpace ContDiff

namespace HRS.MS.S88Breakdown

open HRS HRS.Whole HRS.MS.Spec HRS.MS.MovDec HRS.MS.MovLin HRS.MS.MovAdj HRS.MS.S52B

local notation "𝓢R" => SchwartzMap (Euc _) ℝ

set_option maxHeartbeats 3200000 in
/-- The spectral data of `s8p_exists_spectralData`, with the eigenvector data `D` retained. -/
theorem s88_spectral_witness {d : ℕ} (hd : 2 ≤ d) (a β : ℝ) (ha : 0 < a) (hβ : 0 < β)
    (ρβ : Euc d → ℝ) (hρ : HRS.Whole.IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) :
    ∃ (M : ℝ) (h : S8pRho d ((d : ℝ) / 2) ρβ M) (D : S8pEigData d ((d : ℝ) / 2) β ρβ h),
      HRS.Whole.IsSpectralData d β ρβ (fun l => s8p_E d ((d : ℝ) / 2) β ρβ (D.φ l)) D.om := by
  have hd1 : 1 ≤ d := by omega
  have hdpos : (0 : ℝ) < d := by exact_mod_cast hd1
  have H : Mov2dTh d ((d : ℝ) / 2) β a ρβ :=
    ⟨hd, by positivity, by linarith, hβ, ha, hρ⟩
  have hs : (0 : ℝ) < (d : ℝ) / 2 := by positivity
  obtain ⟨M, h⟩ := s8p_rho_of_thermal H hs
  obtain ⟨hρ', hE, -⟩ := mov2e_thermal H.hd H.hs0 H.hsd H.hβ H.hq H.hρ
  obtain ⟨ψ0, hψ0⟩ := mov2d_sqrt_schwartz H
  obtain ⟨D⟩ := s8p_eigData H h
  have hmean : ∀ n, ∫ x, Real.sqrt (ρβ x) * D.φ n x = 0 := fun n =>
    s8p_mean_zero H ψ0 hψ0 (D.v n) (D.φ n) (D.hv n)
  have hsd : (d : ℝ) / 2 < d := H.hsd
  refine ⟨M, h, D, ?_⟩
  refine ⟨fun l => s8p_E_smooth hd1 H.hs0 hsd hρ' hE β (D.φ l), fun l => ?_, fun l => D.lam_pos.trans_le (D.lam_le l),
    D.mono, fun l => ?_, fun l => ?_, fun l j => ?_, fun l j => ?_, fun l j => ?_, ?_, ?_⟩
  · exact ⟨s8p_E_memLp hd1 H.hs0 hsd hρ' hE β (D.φ l), s8p_E_mean hd1 H.hs0 hsd hρ' hE β (D.φ l) (hmean l)⟩
  · exact s8p_eigen_eq hd1 H.hs0 hsd hρ' hE β (D.φ l) (D.om l) (D.hS l)
  · exact ⟨_, s8p_response hd1 H.hs0 hsd hρ' hE hβ (D.φ l) (hmean l)⟩
  · -- orth
    have hri := s8p_responseInverse_E hd1 hs hsd hρ' hE (fun x => h.le x) hβ (D.φ j) (hmean j)
    unfold HRS.Whole.l2Inner
    have h1 : ∫ x, s8p_E d ((d : ℝ) / 2) β ρβ (D.φ l) x *
        HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) (HRS.Whole.withDensityReal ρβ) β
          (s8p_E d ((d : ℝ) / 2) β ρβ (D.φ j)) x ∂(HRS.Whole.withDensityReal ρβ) =
        β⁻¹ * ∫ x, s8p_E d ((d : ℝ) / 2) β ρβ (D.φ l) x * (D.φ j x / Real.sqrt (ρβ x))
          ∂(HRS.Whole.withDensityReal ρβ) := by
      rw [← integral_const_mul]
      refine integral_congr_ae ?_
      filter_upwards [hri] with x hx
      rw [hx]; ring
    show β * (∫ x, s8p_E d ((d : ℝ) / 2) β ρβ (D.φ l) x *
        HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) (HRS.Whole.withDensityReal ρβ) β
          (s8p_E d ((d : ℝ) / 2) β ρβ (D.φ j)) x ∂(HRS.Whole.withDensityReal ρβ)) = _
    rw [h1, ← mul_assoc, mul_inv_cancel₀ hβ.ne', one_mul,
      s8p_orth_e hd1 H.hs0 hsd hρ' hE β (D.φ l) (D.φ j) (hmean j), D.pair H l j]
  · exact (s8p_grad_pair hd1 H.hs0 hsd hρ' hE β (D.φ l) (D.φ j)).1
  · rw [(s8p_grad_pair hd1 H.hs0 hsd hρ' hE β (D.φ l) (D.φ j)).2]
    have : ∫ x, mov2eW d ((d : ℝ) / 2) β ρβ (D.φ j) x * movS d ((d : ℝ) / 2) β ρβ (D.φ l) x =
        ∫ x, D.om l * (mov2eW d ((d : ℝ) / 2) β ρβ (D.φ j) x * D.φ l x) := by
      refine integral_congr_ae ?_
      filter_upwards [D.hS l] with x hx
      rw [hx]; ring
    rw [this, integral_const_mul, D.pair H j l]
    by_cases hlj : l = j
    · subst hlj; simp
    · simp [hlj, Ne.symm hlj]
  · exact s8p_growth H ψ0 hψ0 D
  · intro f hf hr
    exact s8p_complete_field hd1 hs hsd hρ' hE h hβ D.v D.φ D.hv hmean D.complete f hf hr

/-- The eigenvector evolves by the exponential of its eigenvalue. -/
theorem s88_T_eigen {d : ℕ} {s β q : ℝ} {ρ : Euc d → ℝ} (H : Mov2dTh d s β q ρ) (ψ0 : 𝓢R)
    (hψ0 : (⇑ψ0 : Euc d → ℝ) = fun x => Real.sqrt (ρ x)) {M : ℝ} {h : S8pRho d s ρ M}
    (D : S8pEigData d s β ρ h) (l : ℕ) {t : ℝ} (ht : 0 ≤ t) :
    mov2d_T H ψ0 hψ0 t (D.v l) = Real.exp (-t * D.om l) • D.v l := by
  have hTs := mov2d_isSemigroup H ψ0 hψ0
  obtain ⟨w, hw, hder⟩ := hTs.generator (D.φ l) (D.v l) (D.hv l)
  have hwv : w = D.om l • D.v l := by
    refine Subtype.ext (Lp.ext ?_)
    filter_upwards [hw, D.hS l, D.hv l,
      Lp.coeFn_smul (D.om l) ((D.v l : MovL2Zero ρ) : Lp ℝ 2 (volume : Measure (Euc d)))] with x h1 h2 h3 h4
    change movFun w x = (D.om l • (D.v l : Lp ℝ 2 (volume : Measure (Euc d)))) x
    rw [h4, Pi.smul_apply, smul_eq_mul]
    change movFun w x = D.om l * movFun (D.v l) x
    rw [h1, h2, h3]
  have hg := s88_right_eigen_orbit (fun τ => mov2d_T H ψ0 hψ0 τ (D.v l)) (D.om l)
    (hTs.cont (D.v l)) (fun τ hτ => by
      have := hder τ hτ
      rw [hwv, map_smul] at this
      simpa only [neg_smul] using this) t ht
  rw [hg, hTs.zero]
  simp only [ContinuousLinearMap.one_apply]
  rw [show -(D.om l) * t = -t * D.om l by ring]

section Pairing

variable {d : ℕ} {s β : ℝ} {ρ : Euc d → ℝ}

/-- The `L²(μ)` pairing of a centered function with the response of an eigenfunction is the Lebesgue pairing
`∫ u √ρ φ`. -/
theorem s88_pair_eq (hd1 : 1 ≤ d) (hs : 0 < s) (hsd : s < d) (hρ' : Mov2eRho d ρ)
    (hE : Mov2eEll d ρ) {M : ℝ} (hM : ∀ x, ρ x ≤ M) (hβ : 0 < β) (φ : 𝓢R)
    (hφc : ∫ x, Real.sqrt (ρ x) * φ x = 0) {u : Euc d → ℝ}
    (hu : Integrable (fun x => u x * (Real.sqrt (ρ x) * φ x))) :
    β * HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ)
        (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) u)
        (HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β
          (s8p_E d s β ρ φ)) = ∫ x, u x * (Real.sqrt (ρ x) * φ x) := by
  have hR := s8p_responseInverse_E hd1 hs hsd hρ' hE hM hβ φ hφc
  have hsq : MemLp (fun x => Real.sqrt (ρ x)) 2 (volume : Measure (Euc d)) := by
    refine (memLp_two_iff_integrable_sq (hρ'.data.sqrt_smooth.continuous.aestronglyMeasurable)).2 ?_
    exact ((hρ'.psi_GD.mul hρ'.psi_GD).integrable).congr (Filter.Eventually.of_forall fun x => by simp [sq])
  have hI3 : Integrable (fun x => Real.sqrt (ρ x) * φ x) := hsq.integrable_mul (φ.memLp 2)
  unfold HRS.Whole.l2Inner
  set c : ℝ := HRS.Whole.pair (HRS.Whole.withDensityReal ρ) u with hc
  have e1 : ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) u x *
      HRS.Whole.responseInverse (rieszKernel d s) (HRS.Whole.withDensityReal ρ) β (s8p_E d s β ρ φ) x
        ∂(HRS.Whole.withDensityReal ρ) =
      ∫ x, HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) u x * (β⁻¹ * (φ x / Real.sqrt (ρ x)))
        ∂(HRS.Whole.withDensityReal ρ) := by
    refine integral_congr_ae ?_
    filter_upwards [hR] with x hx
    rw [hx]
  rw [e1, mov2e_integral_mu hρ']
  have e2 : ∀ x, ρ x * (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ) u x *
      (β⁻¹ * (φ x / Real.sqrt (ρ x)))) =
      β⁻¹ * (u x * (Real.sqrt (ρ x) * φ x) - c * (Real.sqrt (ρ x) * φ x)) := by
    intro x
    have hp := hρ'.psi_pos x
    have hss := hρ'.psi_sq x
    unfold HRS.Whole.projMean
    rw [← hc]
    generalize Real.sqrt (ρ x) = p at hp hss ⊢
    rw [← hss]
    field_simp
  simp_rw [e2]
  rw [integral_const_mul, integral_sub hu (hI3.const_mul c), integral_const_mul, hφc]
  field_simp
  ring

end Pairing

theorem s88_classical_spectral_coefficients {d : ℕ} (hd : 2 ≤ d) (a β : ℝ)
    (ha : 0 < a) (hβ : 0 < β) (m : ℝ) (hm : (wholeSpaceIndex d : ℝ) ≤ m)
    (ρ : Euc d → ℝ) (hρ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρ) :
    ∃ (e : ℕ → Euc d → ℝ) (om : ℕ → ℝ), IsSpectralData d β ρ e om ∧
      ∀ (α : MultiIndex d) (t : ℝ), 0 ≤ t → ∀ l : ℕ,
        β * HRS.Whole.l2Inner (HRS.Whole.withDensityReal ρ)
          (HRS.Whole.projMean (HRS.Whole.withDensityReal ρ)
            (s88Orbit (critCoeff d a β ρ) m t α))
          (HRS.Whole.responseInverse (rieszKernel d ((d : ℝ) / 2)) (HRS.Whole.withDensityReal ρ) β
            (e l)) =
        Real.exp (-t * om l) * u11Coef d β ρ e m α l := by
  obtain ⟨M, h, D, hdata⟩ := s88_spectral_witness hd a β ha hβ ρ hρ
  refine ⟨_, _, hdata, ?_⟩
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

end HRS.MS.S88Breakdown
