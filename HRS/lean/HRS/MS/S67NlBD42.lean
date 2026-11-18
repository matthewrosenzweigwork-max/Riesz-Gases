import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovLinAux15
import HRS.MS.S67NlBD00
import HRS.MS.S67NlBD06
import HRS.MS.S67NlBD25
import HRS.MS.S67NlBD29
import HRS.MS.S67NlBD30
import HRS.MS.S67NlBD32
import HRS.MS.S67NlBD33
import HRS.MS.S67NlBD34
import HRS.MS.S67NlBD36
import HRS.MS.S67NlBD39
import HRS.MS.S67NlBD41

/-!
# S6.7nl.42: weighted decay of the classical adjoint solution
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Route: the finite `Σ^M` bound (packet 39) makes `Y(r) = ‖ψ_r‖_M` a bounded measurable path (packet 33).
The Duhamel identity (packet 32), the source bound at level `M - a` (packet 25) and the semigroup
smoothing `Σ^{M-a} → Σ^M` give the Volterra inequality
`Y r ≤ CT N e^{-c(T-r)} + K R0 ∫ kernel(v-r) Y v`, which packet 41 absorbs for `R0 ≤ Rstar`.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

set_option maxHeartbeats 3200000 in
theorem s67bd_weighted_decay (H : Mov2dTh d s β q ρ₀)
    (M m : ℕ) (hM : 2 ≤ M) (hm : (d : ℝ) / 2 + 7 < m) (hmM : (M : ℝ) + 4 < m) :
    ∃ Rstar C c : ℝ, 0 < Rstar ∧ 1 ≤ C ∧ 0 < c ∧
      ∀ R0 c0 : ℝ, 0 ≤ R0 → R0 ≤ Rstar → 0 ≤ c0 →
      ∀ (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ),
      MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ →
      ∀ (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ), 0 ≤ T →
      IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f →
      MemOsc (M : ℝ) (s67psi ρ₀ φ) → ∀ r ∈ Icc (0 : ℝ) T,
        MemOsc (M : ℝ) (s67psi ρ₀ (f r)) ∧
        oscNorm (M : ℝ) (s67psi ρ₀ (f r)) ≤
          C * Real.exp (-c * (T - r)) * oscNorm (M : ℝ) (s67psi ρ₀ φ) := by
  have hM2 : (2 : ℝ) ≤ M := by exact_mod_cast hM
  have ha1 : 1 ≤ movA d s := le_max_left _ _
  have ha2 : movA d s < 2 := by
    unfold movA; exact max_lt (by norm_num) (by linarith [H.hsd])
  have hAM : movA d s ≤ M := by linarith
  have hp0 : 0 ≤ (M : ℝ) - movA d s := by linarith
  have hpq : (M : ℝ) - movA d s ≤ M := by linarith
  have hgain : (M : ℝ) - ((M : ℝ) - movA d s) < 2 := by linarith
  obtain ⟨g, hg⟩ := mov2d_sqrt_schwartz H
  obtain ⟨-, -, -, c, hc, hsm⟩ := s67bd_semigroup_data H g hg
  obtain ⟨CT, hCT1, hCT⟩ := hsm M hAM
  obtain ⟨C25, hC25, h25⟩ := s67bd_projected_source_bound H m M hm hM2 (by linarith)
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  have hsqc : Continuous (fun x => Real.sqrt (ρ₀ x)) := by
    rw [← hψs]; exact ψs.continuous
  have hK : 0 ≤ CT * C25 := mul_nonneg (by linarith) hC25
  obtain ⟨c', hc'def⟩ : ∃ c' : ℝ, c' = c / 2 := ⟨_, rfl⟩
  have hc'0 : 0 < c' := by rw [hc'def]; linarith
  have hgap : c' < c := by rw [hc'def]; linarith
  obtain ⟨β0, hβ0def⟩ : ∃ β0 : ℝ, β0 = mndBeta (1 - movA d s / 2) (c - c') := ⟨_, rfl⟩
  have hβ0 : 0 ≤ β0 := hβ0def ▸ mnd_beta_nonneg _ _
  have hD : 0 < 2 * (CT * C25 + 1) * (β0 + 1) := by positivity
  refine ⟨1 / (2 * (CT * C25 + 1) * (β0 + 1)), 2 * CT, c', by positivity, by linarith, hc'0, ?_⟩
  intro R0 c0 hR0 hR0le hc0 f0 ρ hρ T φ f hT hf hφ
  -- finite bound and realizations
  obtain ⟨B, hB0, hBM⟩ := s67bd_bootstrap_finite H M m hM hm hmM R0 c0 hR0 hc0 f0 ρ hρ T φ f hT hf hφ
  obtain ⟨Ψ, R, hrep⟩ := s67bd_classical_realizations H m hm R0 c0 f0 ρ hρ T φ f hT hf
  obtain ⟨hΨc, hRc, -⟩ := s67bd_source_continuity H m hm R0 c0 f0 ρ hρ T φ f hT hf Ψ R hrep
  obtain ⟨Bψ, -, hBψ⟩ := s67bd_classical_sigma2 H ρ T φ f hT hf
  obtain ⟨Y, hY⟩ : ∃ Y : ℝ → ℝ, Y = fun r => oscNorm (M : ℝ) (s67psi ρ₀ (f r)) := ⟨_, rfl⟩
  obtain ⟨N, hN⟩ : ∃ N : ℝ, N = oscNorm (M : ℝ) (s67psi ρ₀ φ) := ⟨_, rfl⟩
  have hYnn : ∀ r, 0 ≤ Y r := fun r => by
    rw [hY]; exact HRS.MS.MovC1.movc1_osc_nonneg _ _
  have hN0 : 0 ≤ N := hN ▸ HRS.MS.MovC1.movc1_osc_nonneg _ _
  have hYM : ∀ r ∈ Icc (0 : ℝ) T, MemOsc (M : ℝ) (s67psi ρ₀ (f r)) ∧ Y r ≤ B := by
    intro r hr; rw [hY]; exact hBM r hr
  -- the source bound at level `M - a`
  have hsrc : ∀ v ∈ Icc (0 : ℝ) T, MemOsc ((M : ℝ) - movA d s) (movFun (R v)) ∧
      oscNorm ((M : ℝ) - movA d s) (movFun (R v)) ≤ C25 * R0 * Y v := by
    intro v hv
    have hvc : Continuous (movV ρ₀ ρ v) := by
      show Continuous (fun x => (ρ v x - ρ₀ x) / Real.sqrt (ρ₀ x))
      exact ((hρ.regular v hv.1).sub hρsm.continuous).div hsqc
        (fun x => (Real.sqrt_pos.2 (hρpos x)).ne')
    obtain ⟨-, -, hψ2, hD'⟩ := hBψ v hv
    obtain ⟨hmem, -, -, hn⟩ := h25 _ _ hvc (hρ.weighted v hv.1).1 hψ2 (hYM v hv).1 hD'
    have hae : movFun (R v) =ᵐ[volume] _ := (hrep v hv).2
    refine ⟨HRS.MS.MovLin.mov2b_memOsc_congr hae.symm _ hmem, ?_⟩
    rw [HRS.MS.MovLin.mov2b_oscNorm_congr hae]
    refine hn.trans ?_
    have h1 : oscNorm (m : ℝ) (movV ρ₀ ρ v) ≤ R0 := by
      refine (hρ.weighted v hv.1).2.trans ?_
      have : Real.exp (-c0 * v) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hv.1])
      nlinarith
    have h3 := HRS.MS.MovC1.movc1_osc_nonneg (m : ℝ) (movV ρ₀ ρ v)
    have h4 := hYnn v
    rw [hY] at h4 ⊢
    exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left h1 hC25) h4
  -- the path `Y`
  have hΨmem : ∀ v ∈ Icc (0 : ℝ) T, MemOsc (M : ℝ) (movFun (Ψ v)) := fun v hv =>
    HRS.MS.MovLin.mov2b_memOsc_congr (show movFun (Ψ v) =ᵐ[volume] _ from (hrep v hv).1).symm _
      (hYM v hv).1
  have hYn : ∀ v ∈ Icc (0 : ℝ) T, Y v = ‖OscSpace.ofFun (M : ℝ) (movFun (Ψ v))‖ := by
    intro v hv
    rw [OscSpace.norm_ofFun _ (hΨmem v hv), hY]
    exact (HRS.MS.MovLin.mov2b_oscNorm_congr (show movFun (Ψ v) =ᵐ[volume] _ from (hrep v hv).1) _).symm
  have hYmeas : AEStronglyMeasurable Y (volume.restrict (Icc (0 : ℝ) T)) := by
    have h33 := s67bd_higher_measurable ρ₀ (M : ℝ) T (by linarith) hT Ψ hΨc hΨmem
    exact h33.norm.congr ((ae_restrict_iff' measurableSet_Icc).2
      (Eventually.of_forall fun v hv => (hYn v hv).symm))
  -- terminal data
  have hfT : f T = φ := hf.terminal
  have hΨT : movFun (Ψ T) =ᵐ[volume] s67psi ρ₀ φ := by
    have := (hrep T ⟨hT, le_rfl⟩).1
    rw [hfT] at this; exact this
  have hΨTm : MemOsc (M : ℝ) (movFun (Ψ T)) :=
    HRS.MS.MovLin.mov2b_memOsc_congr hΨT.symm _ hφ
  have hΨTn : oscNorm (M : ℝ) (movFun (Ψ T)) = N := by
    rw [hN]; exact HRS.MS.MovLin.mov2b_oscNorm_congr hΨT _
  -- the Volterra inequality
  have hvol : ∀ r ∈ Icc (0 : ℝ) T, Y r ≤ CT * N * Real.exp (-c * (T - r)) +
      (CT * C25 * R0) * ∫ v in Icc r T, s67bd_kernel (movA d s) c (v - r) * Y v := by
    intro r hr
    -- homogeneous term
    obtain ⟨hAm, hAn⟩ := hCT.1 (T - r) (sub_nonneg.2 hr.2) (Ψ T) hΨTm
    rw [hΨTn] at hAn
    -- the kernel-weighted integrand
    have hker := s67bd_kernel_integrableOn (a := movA d s) ha2 hc (r := r) (T := T) hr.2
    have hYbdd : ∀ v ∈ Icc (0 : ℝ) T, Y v ≤ max B 0 := fun v hv =>
      (hYM v hv).2.trans (le_max_left _ _)
    have hkY : IntegrableOn (fun v => s67bd_kernel (movA d s) c (v - r) * Y v) (Icc r T) volume := by
      have hmeas : AEStronglyMeasurable Y (volume.restrict (Icc r T)) :=
        hYmeas.mono_measure (Measure.restrict_mono (Icc_subset_Icc hr.1 le_rfl) le_rfl)
      refine Integrable.mul_bdd (c := max B 0) hker hmeas ?_
      filter_upwards [ae_restrict_mem measurableSet_Icc] with v hv
      have hv0 : v ∈ Icc (0 : ℝ) T := ⟨le_trans hr.1 hv.1, hv.2⟩
      rw [Real.norm_eq_abs, abs_of_nonneg (hYnn v)]
      exact hYbdd v hv0
    set ψ : ℝ → ℝ := fun v => (CT * C25 * R0) *
      (s67bd_kernel (movA d s) c (v - r) * Y v) with hψ
    have hψint : IntegrableOn ψ (Ioc r T) :=
      IntegrableOn.mono_set (Integrable.const_mul hkY (CT * C25 * R0)) Ioc_subset_Icc_self
    have hRm : ∀ v ∈ Icc (0 : ℝ) T, MemOsc ((M : ℝ) - movA d s) (movFun (R v)) :=
      fun v hv => (hsrc v hv).1
    obtain ⟨hmem, hmeas⟩ := s67bd_lift_measurable H g hg ((M : ℝ) - movA d s) M T hp0 hpq hgain
      hT R hRc hRm r hr
    have hbd : ∀ v ∈ Ioc r T, ‖s67bd_lift H g hg (M : ℝ) r R v‖ ≤ ψ v := by
      intro v hv
      have hτ : 0 < v - r := sub_pos.2 hv.1
      have hv' : v ∈ Icc (0 : ℝ) T := ⟨hr.1.trans hv.1.le, hv.2⟩
      obtain ⟨-, hnorm⟩ := hCT.2 (v - r) hτ (R v) (hRm v hv')
      have hl : s67bd_lift H g hg (M : ℝ) r R v =
          OscSpace.ofFun (M : ℝ) (movFun (s67bd_Tdag H g hg (v - r) (R v))) := by
        simp only [s67bd_lift, hv.1, ↓reduceIte]
      rw [hl, OscSpace.norm_ofFun _ (hmem v hv)]
      refine hnorm.trans ?_
      have hk := s67bd_kernel_nonneg (movA d s) c hτ.le
      have hs := (hsrc v hv').2
      have e : CT * (1 + (v - r) ^ (-(movA d s) / 2)) * Real.exp (-c * (v - r)) =
          CT * s67bd_kernel (movA d s) c (v - r) := by
        unfold s67bd_kernel; ring
      calc CT * (1 + (v - r) ^ (-(movA d s) / 2)) * Real.exp (-c * (v - r)) *
            oscNorm ((M : ℝ) - movA d s) (movFun (R v))
          = CT * s67bd_kernel (movA d s) c (v - r) *
              oscNorm ((M : ℝ) - movA d s) (movFun (R v)) := by rw [e]
        _ ≤ CT * s67bd_kernel (movA d s) c (v - r) * (C25 * R0 * Y v) :=
            mul_le_mul_of_nonneg_left hs (mul_nonneg (by linarith) hk)
        _ = ψ v := by rw [hψ]; ring
    have hae : ∀ᵐ v ∂(volume.restrict (Ioc r T)), ‖s67bd_lift H g hg (M : ℝ) r R v‖ ≤ ψ v :=
      (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall hbd)
    have hmeasI : AEStronglyMeasurable (s67bd_lift H g hg (M : ℝ) r R)
        (volume.restrict (Ioc r T)) := hmeas.mono_set Ioc_subset_Icc_self
    have hI : IntegrableOn (s67bd_lift H g hg (M : ℝ) r R) (Icc r T) volume := by
      have : IntegrableOn (s67bd_lift H g hg (M : ℝ) r R) (Ioc r T) :=
        Integrable.mono' hψint hmeasI hae
      exact this.congr_set_ae Ioc_ae_eq_Icc.symm
    obtain ⟨-, hL, heq⟩ := s67bd_duhamel_l2 H g hg m hm R0 c0 f0 ρ hρ T φ f hT hf Ψ R hrep r hr
    obtain ⟨hcomp1, hcomp2⟩ :=
      s67bd_lift_compatibility H g hg (M : ℝ) r T (by linarith) hr.2 R hmem hI hL
    have hf2 : MemLp (movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (R v)))
        2 (volume : Measure (Euc d)) := Lp.memLp _
    have hcoe : (∫ v in Icc r T, ((s67bd_Tdag H g hg (v - r) (R v) : MovL2Zero ρ₀) :
        Lp ℝ 2 (volume : Measure (Euc d)))) =
        ((∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (R v) : MovL2Zero ρ₀) :
          Lp ℝ 2 (volume : Measure (Euc d))) :=
      (MovL2Zero ρ₀).subtypeL.integral_comp_comm hL
    have hz : mov2d_j (by linarith : (0 : ℝ) ≤ M) (∫ v in Icc r T, s67bd_lift H g hg (M : ℝ) r R v) =
        OscSpace.ofFun 0 (movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (R v))) := by
      apply (mov2d_Phi d).injective
      rw [hcomp1, mov2d_Phi_ofFun hf2, hcoe]
      exact (Lp.toLp_coeFn _ hf2).symm
    obtain ⟨-, hofs⟩ := movlin_memOsc_of_lev (by linarith : (0 : ℝ) ≤ M) hf2 hz
    have hIn : oscNorm (M : ℝ) (movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (R v))) ≤
        (CT * C25 * R0) * ∫ v in Icc r T, s67bd_kernel (movA d s) c (v - r) * Y v := by
      rw [← OscSpace.norm_ofFun (movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (R v)))
        hcomp2, hofs]
      refine (norm_integral_le_integral_norm _).trans ?_
      rw [integral_Icc_eq_integral_Ioc, integral_Icc_eq_integral_Ioc, ← integral_const_mul]
      exact integral_mono_of_nonneg (Eventually.of_forall fun v => norm_nonneg _) hψint hae
    -- assemble
    have hsumae : movFun (Ψ r) =ᵐ[volume] fun x =>
        movFun (s67bd_Tdag H g hg (T - r) (Ψ T)) x +
          movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (R v)) x := by
      rw [heq]; exact Lp.coeFn_add _ _
    have hψae : s67psi ρ₀ (f r) =ᵐ[volume] fun x =>
        movFun (s67bd_Tdag H g hg (T - r) (Ψ T)) x +
          movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (R v)) x :=
      (show movFun (Ψ r) =ᵐ[volume] _ from (hrep r hr).1).symm.trans hsumae
    obtain ⟨-, hS2⟩ := HRS.MS.MovC1.movc1_osc_add (M : ℝ) hAm hcomp2
    have hYr : Y r = oscNorm (M : ℝ) (fun x =>
        movFun (s67bd_Tdag H g hg (T - r) (Ψ T)) x +
          movFun (∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (R v)) x) := by
      rw [hY]; exact HRS.MS.MovLin.mov2b_oscNorm_congr hψae _
    rw [hYr]
    refine hS2.trans (add_le_add ?_ hIn)
    refine hAn.trans ?_
    have : Real.exp (-c * (T - r)) = Real.exp (-c * (T - r)) := rfl
    nlinarith [hN0]
  -- absorption
  have hsmall : (CT * C25 * R0) * mndBeta (1 - movA d s / 2) (c - c') ≤ 1 / 2 := by
    rw [← hβ0def]
    have h1 : R0 * (2 * (CT * C25 + 1) * (β0 + 1)) ≤ 1 := (le_div_iff₀ hD).1 hR0le
    have h2 : R0 * (2 * (CT * C25 + 1) * (β0 + 1)) - 2 * (CT * C25 * R0 * β0) =
        2 * R0 * (CT * C25 + β0 + 1) := by ring
    have h3 : 0 ≤ 2 * R0 * (CT * C25 + β0 + 1) := by positivity
    linarith
  obtain ⟨-, habs⟩ := s67bd_volterra_absorb T (CT * N) (CT * C25 * R0) (movA d s) c c'
    hT (mul_nonneg (by linarith) hN0) (by positivity) (by linarith) ha2 hc'0 hgap Y hYmeas
    (fun r _ => hYnn r) ⟨B, fun r hr => (hYM r hr).2⟩ hvol hsmall
  intro r hr
  refine ⟨(hYM r hr).1, ?_⟩
  have := habs r hr
  rw [hY] at this
  rw [← hN]
  nlinarith [this]

end HRS.MS.BreakdownS67
