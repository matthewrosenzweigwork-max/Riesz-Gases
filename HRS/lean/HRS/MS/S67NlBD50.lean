import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.Mov63Aux3
import HRS.MS.MovAdjAux21
import HRS.MS.UniqFAux4
import HRS.MS.S67NlBD14
import HRS.MS.S67NlBD26
import HRS.MS.S67NlBD39
import HRS.MS.S67NlBD47
import HRS.MS.S67NlBD48
import HRS.MS.S67NlBD49

/-!
# S6.7nl.50: the one-body Duhamel data of the nonlinear source
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Owned definition: `s67bd_source`.
Route: reversed and scaled time `u(σ) = f(T - βσ)` as in the stationary template `s67_duhData`; the
generator identity `β 𝓛_ρ - kolmL = β (J(ρ_r) u - F(v)·∇u)` uses additivity of the cancellation force
(`v = (ρ_r - ρ₀)/√ρ₀`, `C¹ ∩ L¹`); the source is bounded by packets 39 and 47 and the force bound
`mn_force_bound`, and jointly continuous by packet 48.
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

/-- The nonlinear source: `J(ρ_r) f_r - F[v_r] · ∇ f_r`. -/
def s67bd_source (d : ℕ) (s : ℝ) (ρ₀ : Euc d → ℝ)
    (ρ : ℝ → Euc d → ℝ) (f : ℝ → Euc d → ℝ) (r : ℝ) (x : Euc d) : ℝ :=
  s67J d s (ρ r) (f r) x - inner ℝ (s67bd_F d s ρ₀ (movV ρ₀ ρ r) x) (gradient (f r) x)

lemma s67bd50_reparam {T β : ℝ} (hβ : 0 < β) {E : Type*} [TopologicalSpace E] {G : ℝ → Euc d → E}
    (hc : ContinuousOn (fun p : ℝ × Euc d => G p.1 p.2) (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d)))) :
    ContinuousOn (fun p : ℝ × Euc d => G (T - β * p.1) p.2)
      (Icc (0 : ℝ) (T / β) ×ˢ (univ : Set (Euc d))) := by
  have h1 : ContinuousOn (fun p : ℝ × Euc d => ((T - β * p.1, p.2) : ℝ × Euc d))
      (Icc (0 : ℝ) (T / β) ×ˢ (univ : Set (Euc d))) := by fun_prop
  exact hc.comp h1 (fun p hp => ⟨s67_hmem hβ hp.1, mem_univ _⟩)

/-- the generator identity `β 𝓛_ρ u - kolmL = β (J(ρ_r) u - F · ∇u)` -/
lemma s67bd50_aL (hβ : 0 < β) (ρ : ℝ → Euc d → ℝ) (r : ℝ) (u : Euc d → ℝ) (v : Euc d → ℝ)
    (hF : ∀ x, movForce d s (ρ r) x = movForce d s ρ₀ x + s67bd_F d s ρ₀ v x) (x : Euc d) :
    β * generatorW ((quadraticGradientDyn d s q β).coeff ρ) r u x -
      kolmL (β * q) (s67bd_oneBodyB d s β ρ₀) u x =
    β * (s67J d s (ρ r) u x - inner ℝ (s67bd_F d s ρ₀ v x) (gradient u x)) := by
  have e1 : generatorW ((quadraticGradientDyn d s q β).coeff ρ) r u x =
      generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ r)) r u x := by
    rw [HRS.MH.DualityRd.generatorW_coeff, HRS.MH.DualityRd.generatorW_coeff]
  rw [e1, s67_gen_eq s q β (ρ r) r u x, hF x]
  unfold kolmL s67bd_oneBodyB
  simp only [inner_sub_left, inner_add_left, inner_neg_left, real_inner_smul_left]
  have hb : β * β⁻¹ = 1 := mul_inv_cancel₀ hβ.ne'
  linear_combination (Laplacian.laplacian u x) * hb

set_option maxHeartbeats 3200000 in
theorem s67bd_onebody_data (H : Mov2dTh d s β q ρ₀)
    (j M m : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M)
    (hm : (d : ℝ) / 2 + 7 < m) (hmM : (M : ℝ) + 4 < m)
    (R0 c0 : ℝ) (hR0 : 0 ≤ R0) (hR1 : R0 ≤ 1) (hc0 : 0 ≤ c0)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ)
    (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f)
    (hφ : MemOsc (M : ℝ) (s67psi ρ₀ φ)) :
    S67DuhData (β * q) (s67bd_oneBodyB d s β ρ₀) (T / β)
      (fun σ x => f (T - β * σ) x)
      (fun σ x => β * generatorW ((quadraticGradientDyn d s q β).coeff ρ)
        (T - β * σ) (f (T - β * σ)) x)
      (fun σ x => β * s67bd_source d s ρ₀ ρ f (T - β * σ) x) := by
  have hβ := H.hβ
  have hd := H.hd
  have hs0 := H.hs0
  have hsd := H.hsd
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hM2 : 2 ≤ M := by exact_mod_cast (show (2 : ℝ) ≤ M by linarith)
  have hmem : ∀ σ ∈ Icc (0 : ℝ) (T / β), T - β * σ ∈ Icc (0 : ℝ) T :=
    fun σ hσ => s67_hmem hβ hσ
  -- thermal data
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  have hsqsm : ContDiff ℝ ∞ (fun x => Real.sqrt (ρ₀ x)) := by
    rw [← hψs]; exact ψs.smooth _
  have hsq2 : MemLp (fun x => Real.sqrt (ρ₀ x)) 2 (volume : Measure (Euc d)) := by
    have := (memOsc_schwartz 0 ψs).1
    rwa [hψs] at this
  have hρ0I : Integrable ρ₀ volume := by
    by_contra hni
    have h1 := H.hρ.2.1.integral_one
    rw [integral_undef hni] at h1
    exact zero_ne_one h1
  have hρ0c1 : ContDiff ℝ 1 ρ₀ := hρsm.of_le (by simp)
  -- constants
  obtain ⟨CJ, hCJ0, hCJ⟩ := s67bd_J_bound H j M m hM hm hmM
  obtain ⟨Cf, hCf0, hCf⟩ := mn_force_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ₀ H.hρ 0 m
    (by push_cast; linarith)
  obtain ⟨Bf, hBf0, hBf⟩ := s67bd_bootstrap_finite H M m hM2 hm hmM R0 c0 hR0 hc0 f0 ρ hρ T φ f
    hT hf hφ
  obtain ⟨hFc, hJc⟩ := s67bd_source_joint_cont H m hm R0 c0 f0 ρ hρ T φ f hT hf
  obtain ⟨Mb, -, hMb⟩ := s67bd_onebody_drift H 0
  have hBc : Continuous (s67bd_oneBodyB d s β ρ₀) := hMb.1.continuous
  obtain ⟨K0, K1, K2, hK⟩ := s67_bd_all hf
  -- per-time facts
  have hvcont : ∀ r ∈ Icc (0 : ℝ) T, Continuous (movV ρ₀ ρ r) := by
    intro r hr
    show Continuous (fun x => (ρ r x - ρ₀ x) / Real.sqrt (ρ₀ x))
    exact ((hρ.regular r hr.1).sub hρsm.continuous).div hsqsm.continuous
      (fun x => (Real.sqrt_pos.2 (hρpos x)).ne')
  have hFadd : ∀ r ∈ Icc (0 : ℝ) T, ∀ x, movForce d s (ρ r) x =
      movForce d s ρ₀ x + s67bd_F d s ρ₀ (movV ρ₀ ρ r) x := by
    intro r hr x
    have hρr : ∀ x, ρ r x = ρ₀ x + Real.sqrt (ρ₀ x) * movV ρ₀ ρ r x := by
      intro x
      have : Real.sqrt (ρ₀ x) ≠ 0 := (Real.sqrt_pos.2 (hρpos x)).ne'
      simp only [movV]
      field_simp
      ring
    obtain ⟨hvm, -⟩ := hρ.weighted r hr.1
    have hvC2 : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) (movV ρ₀ ρ r) :=
      ((hCf _ (hvcont r hr) hvm).1)
    have hvC1 : ContDiff ℝ 1 (movV ρ₀ ρ r) := hvC2.of_le (by norm_num)
    have hg1 : ContDiff ℝ 1 (fun x => Real.sqrt (ρ₀ x) * movV ρ₀ ρ r x) :=
      (hsqsm.of_le (by simp)).mul hvC1
    have hgI : Integrable (fun x => Real.sqrt (ρ₀ x) * movV ρ₀ ρ r x) volume :=
      hsq2.integrable_mul hvm.1
    have := s67bd26_force_add hd hs0 hsd hρ0c1 hg1 hρ0I hgI x
    have e : (fun y => ρ₀ y + Real.sqrt (ρ₀ y) * movV ρ₀ ρ r y) = ρ r := by
      funext y; exact (hρr y).symm
    rw [e] at this
    exact this
  have hFbd : ∀ r ∈ Icc (0 : ℝ) T, ∀ x, ‖s67bd_F d s ρ₀ (movV ρ₀ ρ r) x‖ ≤ Cf := by
    intro r hr x
    obtain ⟨hvm, hvn⟩ := hρ.weighted r hr.1
    have h5 := (hCf _ (hvcont r hr) hvm).2.2.2.2
    have h6 := HRS.MS.UniqF.uniqf_drift_bound (le_trans le_self_add h5) x
    have hosc : oscNorm (m : ℝ) (movV ρ₀ ρ r) ≤ 1 := by
      refine hvn.trans ?_
      have : Real.exp (-c0 * r) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hr.1])
      nlinarith
    have hosc0 := HRS.MS.MovC1.movc1_osc_nonneg (m : ℝ) (movV ρ₀ ρ r)
    refine h6.trans (max_le ?_ hCf0)
    nlinarith
  have hmemcb : ∀ r ∈ Icc (0 : ℝ) T, MemCb 2 (f r) := by
    intro r hr
    refine ⟨hf.c2 r hr, fun j' hj' => ?_⟩
    obtain ⟨B, hB⟩ := hf.bdd j' hj'
    exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB r hr x⟩
  -- the bound on the source
  have hsrcb : ∀ r ∈ Icc (0 : ℝ) T, ∀ y, |s67bd_source d s ρ₀ ρ f r y| ≤ CJ * Bf + K1 * Cf := by
    intro r hr y
    have hJb : |s67J d s (ρ r) (f r) y| ≤ CJ * Bf := by
      have h1 := (hCJ R0 c0 hR0 hR1 hc0 f0 ρ hρ r hr.1 (f r) (hmemcb r hr) (hBf r hr).1).2 0
        (by omega) y
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1
      exact h1.trans (mul_le_mul_of_nonneg_left (hBf r hr).2 hCJ0)
    have hIb : |inner ℝ (s67bd_F d s ρ₀ (movV ρ₀ ρ r) y) (gradient (f r) y)| ≤ K1 * Cf := by
      rw [kl_inner_gradient, ← Real.norm_eq_abs]
      refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
      have h1 := (hK r hr y).2.1
      exact mul_le_mul h1 (hFbd r hr y) (norm_nonneg _) ((norm_nonneg _).trans h1)
    unfold s67bd_source
    exact (abs_sub _ _).trans (add_le_add hJb hIb)
  refine ⟨fun σ hσ => hf.c2 _ (hmem σ hσ), ?_,
    s67_reparam (G := fun r y => f r y) hβ (s67_cont_val hf),
    s67_reparam (G := fun r y => fderiv ℝ (f r) y) hβ (s67_cont_fderiv hf),
    continuousOn_const.mul (s67_reparam (G := fun r y => generatorW
      ((quadraticGradientDyn d s q β).coeff ρ) r (f r) y) hβ hf.cont_time_deriv),
    ?_, ?_, ?_, fun σ hσ s0 hs0' y => s67_ftc hf hβ y hs0' hσ, ?_⟩
  · exact ⟨K0, K1, K2, fun σ hσ y => hK _ (hmem σ hσ) y⟩
  · obtain ⟨Bt, hBt⟩ := hf.bdd_time_deriv
    refine ⟨|β| * |Bt|, fun σ hσ y => ?_⟩
    rw [abs_mul]
    have h1 := hBt _ (hmem σ hσ) y
    have h2 : |β| * |generatorW ((quadraticGradientDyn d s q β).coeff ρ) (T - β * σ)
        (f (T - β * σ)) y| ≤ |β| * (|Bt| * (1 + ‖y‖)) :=
      mul_le_mul_of_nonneg_left (h1.trans (mul_le_mul_of_nonneg_right (le_abs_self _)
        (by positivity))) (abs_nonneg _)
    simpa [mul_assoc] using h2
  · -- Scont
    have hJr := s67bd50_reparam (T := T) (G := fun r y => s67J d s (ρ r) (f r) y) hβ hJc
    have hFr := s67bd50_reparam (T := T) (G := fun r y => s67bd_F d s ρ₀ (movV ρ₀ ρ r) y) hβ hFc
    have hgr := s67_reparam (G := fun r y => fderiv ℝ (f r) y) hβ (s67_cont_fderiv hf)
    refine continuousOn_const.mul ((hJr.sub (hgr.clm_apply hFr)).congr fun p hp => ?_)
    show s67bd_source d s ρ₀ ρ f (T - β * p.1) p.2 = _
    unfold s67bd_source
    rw [kl_inner_gradient]
    rfl
  · refine ⟨|β| * |CJ * Bf + K1 * Cf|, fun σ hσ y => ?_⟩
    rw [abs_mul]
    exact mul_le_mul_of_nonneg_left ((hsrcb _ (hmem σ hσ) y).trans (le_abs_self _))
      (abs_nonneg _)
  · intro σ hσ y
    exact s67bd50_aL hβ ρ _ _ _ (hFadd _ (hmem σ hσ)) y

end HRS.MS.BreakdownS67
