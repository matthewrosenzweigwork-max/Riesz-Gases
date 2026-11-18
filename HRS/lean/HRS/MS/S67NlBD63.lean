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
import HRS.MS.S67NlBD40
import HRS.MS.S67NlBD47
import HRS.MS.S67NlBD48
import HRS.MS.S67NlBD49
import HRS.MS.S67NlBD55

/-!
# S6.7nl.63: parabolic data of the actual reversed classical adjoint solution
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Route: `u(τ) = f(T-τ)`, `a(τ) = 𝓛_ρ f(T-τ)`; the equation is the literal generator split
`𝓛_ρ u = β⁻¹Δu + ⟨-q x - F_* - F[v], ∇u⟩ + J(ρ_r)u` (additivity of the cancellation force on `C¹ ∩ L¹`);
regularity of `f` from packet 40; the bounds `Mb`, `MJ` come from the one-body drift (packet 49),
`mn_force_bound` and packet 47 with the finite weighted bound of packet 39.
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

/-- every derivative order up to `K` of a vector field with `cbNormVecE K v ≤ Λ` is bounded -/
lemma s67bd63_cb_le {K : ℕ} {Λ : ℝ} {v : Euc d → Euc d} (h : cbNormVecE K v ≤ ENNReal.ofReal Λ)
    {i : ℕ} (hi : i ≤ K) (x : Euc d) : ‖iteratedFDeriv ℝ i v x‖ ≤ max Λ 0 := by
  unfold cbNormVecE at h
  have h0 : i ∈ Finset.range (K + 1) := Finset.mem_range.2 (by omega)
  have h1 : (⨆ z : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ i v z‖) ≤ ENNReal.ofReal Λ :=
    (Finset.single_le_sum (f := fun j => ⨆ z : Euc d, ENNReal.ofReal ‖iteratedFDeriv ℝ j v z‖)
      (fun _ _ => bot_le) h0).trans h
  have h2 : ENNReal.ofReal ‖iteratedFDeriv ℝ i v x‖ ≤ ENNReal.ofReal Λ :=
    (le_iSup (fun z : Euc d => ENNReal.ofReal ‖iteratedFDeriv ℝ i v z‖) x).trans h1
  have := ENNReal.toReal_mono ENNReal.ofReal_ne_top h2
  rwa [ENNReal.toReal_ofReal (norm_nonneg _), ENNReal.toReal_ofReal'] at this

set_option maxHeartbeats 3200000 in
theorem s67bd_classical_parabolic_data (H : Mov2dTh d s β q ρ₀)
    (j M m : ℕ) (hM : (d : ℝ) / 2 + j + 5 < M)
    (hm : (d : ℝ) / 2 + 7 < m) (hmM : (M : ℝ) + 4 < m)
    (R0 c0 : ℝ) (hR0 : 0 ≤ R0) (hR1 : R0 ≤ 1) (hc0 : 0 ≤ c0)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ)
    (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f)
    (hφ : MemOsc (M : ℝ) (s67psi ρ₀ φ)) :
    s67bd_ParabolicData β⁻¹ q T
      (fun τ x => f (T - τ) x)
      (fun τ x => generatorW ((quadraticGradientDyn d s q β).coeff ρ) (T - τ) (f (T - τ)) x)
      (fun τ x => -movForce d s ρ₀ x - s67bd_F d s ρ₀ (movV ρ₀ ρ (T - τ)) x)
      (fun τ x => s67J d s (ρ (T - τ)) (f (T - τ)) x) ∧
    (∀ τ ∈ Icc (0 : ℝ) T, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞) (f (T - τ))) ∧
    ∃ Mb MJ : ℝ, 0 ≤ Mb ∧ 0 ≤ MJ ∧
      (∀ τ ∈ Icc (0 : ℝ) T,
        ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞)
          (fun x => -movForce d s ρ₀ x - s67bd_F d s ρ₀ (movV ρ₀ ρ (T - τ)) x) ∧
        ∀ i ≤ j + 1, ∀ x, ‖iteratedFDeriv ℝ i
          (fun y => -movForce d s ρ₀ y - s67bd_F d s ρ₀ (movV ρ₀ ρ (T - τ)) y) x‖ ≤ Mb) ∧
      ∀ τ ∈ Icc (0 : ℝ) T,
        ContDiff ℝ (j : WithTop ℕ∞) (s67J d s (ρ (T - τ)) (f (T - τ))) ∧
        ∀ i ≤ j, ∀ x, ‖iteratedFDeriv ℝ i (s67J d s (ρ (T - τ)) (f (T - τ))) x‖ ≤ MJ := by
  have hβ := H.hβ
  have hd := H.hd
  have hs0 := H.hs0
  have hsd := H.hsd
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hM2 : 2 ≤ M := by exact_mod_cast (show (2 : ℝ) ≤ M by linarith)
  have hmem : ∀ τ ∈ Icc (0 : ℝ) T, T - τ ∈ Icc (0 : ℝ) T := fun τ hτ =>
    ⟨by linarith [hτ.2], by linarith [hτ.1]⟩
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
  obtain ⟨Cf, hCf0, hCf⟩ := mn_force_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ₀ H.hρ j m
    (by linarith)
  obtain ⟨Bf, hBf0, hBf⟩ := s67bd_bootstrap_finite H M m hM2 hm hmM R0 c0 hR0 hc0 f0 ρ hρ T φ f
    hT hf hφ
  obtain ⟨hFc, hJc⟩ := s67bd_source_joint_cont H m hm R0 c0 f0 ρ hρ T φ f hT hf
  obtain ⟨Mb1, hMb1, hMb⟩ := s67bd_onebody_drift H (j + 1)
  have hBc : Continuous (s67bd_oneBodyB d s β ρ₀) := hMb.1.continuous
  have hmf : ∀ x, -movForce d s ρ₀ x = β⁻¹ • s67bd_oneBodyB d s β ρ₀ x := by
    intro x
    unfold s67bd_oneBodyB
    have : β⁻¹ * -β = -1 := by field_simp
    rw [smul_smul, this, neg_one_smul]
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
    have hvC2 := (hCf _ (hvcont r hr) hvm).1
    have hvC1 : ContDiff ℝ 1 (movV ρ₀ ρ r) := hvC2.of_le (by
      exact_mod_cast (show (1 : ℕ) ≤ j + 2 by omega))
    have hg1 : ContDiff ℝ 1 (fun x => Real.sqrt (ρ₀ x) * movV ρ₀ ρ r x) :=
      (hsqsm.of_le (by simp)).mul hvC1
    have hgI : Integrable (fun x => Real.sqrt (ρ₀ x) * movV ρ₀ ρ r x) volume :=
      hsq2.integrable_mul hvm.1
    have := s67bd26_force_add hd hs0 hsd hρ0c1 hg1 hρ0I hgI x
    have e : (fun y => ρ₀ y + Real.sqrt (ρ₀ y) * movV ρ₀ ρ r y) = ρ r := by
      funext y; exact (hρr y).symm
    rw [e] at this
    exact this
  have hosc : ∀ r ∈ Icc (0 : ℝ) T, oscNorm (m : ℝ) (movV ρ₀ ρ r) ≤ 1 := by
    intro r hr
    refine (hρ.weighted r hr.1).2.trans ?_
    have : Real.exp (-c0 * r) ≤ 1 := Real.exp_le_one_iff.2 (by nlinarith [hr.1])
    nlinarith
  have hmemcb : ∀ r ∈ Icc (0 : ℝ) T, MemCb 2 (f r) := by
    intro r hr
    refine ⟨hf.c2 r hr, fun j' hj' => ?_⟩
    obtain ⟨B, hB⟩ := hf.bdd j' hj'
    exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB r hr x⟩
  have hFrep : ∀ r ∈ Icc (0 : ℝ) T, ContDiff ℝ ((j + 1 : ℕ) : WithTop ℕ∞)
      (s67bd_F d s ρ₀ (movV ρ₀ ρ r)) := by
    intro r hr
    obtain ⟨hvm, -⟩ := hρ.weighted r hr.1
    have := (hCf _ (hvcont r hr) hvm).2.2.1
    exact_mod_cast this
  refine ⟨⟨fun t ht => hf.c2 _ (hmem t ht), ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩, ?_, ?_⟩
  · -- bdd_c2
    obtain ⟨B0, h0⟩ := hf.bdd 0 (by norm_num)
    obtain ⟨B1, h1⟩ := hf.bdd 1 (by norm_num)
    obtain ⟨B2, h2⟩ := hf.bdd 2 (by norm_num)
    refine ⟨max (max B0 B1) B2, fun t ht k hk x => ?_⟩
    interval_cases k
    · exact (h0 _ (hmem t ht) x).trans ((le_max_left _ _).trans (le_max_left _ _))
    · exact (h1 _ (hmem t ht) x).trans ((le_max_right _ _).trans (le_max_left _ _))
    · exact (h2 _ (hmem t ht) x).trans (le_max_right _ _)
  · -- cont_c2
    intro k hk
    have := s67_reparam (t := T) (β := 1) one_pos
      (G := fun r y => iteratedFDeriv ℝ k (f r) y) (hf.cont_c2 k hk)
    simpa using this
  · -- acont
    have := s67_reparam (t := T) (β := 1) one_pos
      (G := fun r y => generatorW ((quadraticGradientDyn d s q β).coeff ρ) r (f r) y)
      hf.cont_time_deriv
    simpa using this
  · -- agrow
    obtain ⟨Bt, hBt⟩ := hf.bdd_time_deriv
    exact ⟨Bt, fun t ht x => hBt _ (hmem t ht) x⟩
  · -- Bcont
    have h1 : ContinuousOn (fun p : ℝ × Euc d => ((T - p.1, p.2) : ℝ × Euc d))
        (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := by fun_prop
    have hFr : ContinuousOn (fun p : ℝ × Euc d =>
        s67bd_F d s ρ₀ (movV ρ₀ ρ (T - p.1)) p.2) (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) :=
      hFc.comp h1 (fun p hp => ⟨hmem _ hp.1, mem_univ _⟩)
    have hmfc : Continuous (movForce d s ρ₀) := by
      have : movForce d s ρ₀ = fun x => -(β⁻¹ • s67bd_oneBodyB d s β ρ₀ x) := by
        funext x; rw [← hmf x]; simp
      rw [this]; exact (hBc.const_smul β⁻¹).neg
    exact ((hmfc.comp continuous_snd).neg.continuousOn).sub hFr
  · -- Jcont
    have h1 : ContinuousOn (fun p : ℝ × Euc d => ((T - p.1, p.2) : ℝ × Euc d))
        (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := by fun_prop
    exact hJc.comp h1 (fun p hp => ⟨hmem _ hp.1, mem_univ _⟩)
  · -- hint
    intro t ht t0 ht0 x
    have := s67_ftc hf (β := 1) one_pos x (s0 := t0) (σ := t)
      (by simpa using ht0) (by simpa using ht)
    simpa using this
  · -- equation
    intro t ht x
    have hr := hmem t ht
    have e1 : generatorW ((quadraticGradientDyn d s q β).coeff ρ) (T - t) (f (T - t)) x =
        generatorW ((quadraticGradientDyn d s q β).coeff (fun _ => ρ (T - t))) (T - t)
          (f (T - t)) x := by
      rw [HRS.MH.DualityRd.generatorW_coeff, HRS.MH.DualityRd.generatorW_coeff]
    beta_reduce
    rw [e1, s67_gen_eq s q β (ρ (T - t)) (T - t) (f (T - t)) x, hFadd _ hr x]
    have hv : (-(q • x) - (movForce d s ρ₀ x + s67bd_F d s ρ₀ (movV ρ₀ ρ (T - t)) x)) =
        (-q) • x + (-movForce d s ρ₀ x - s67bd_F d s ρ₀ (movV ρ₀ ρ (T - t)) x) := by
      rw [neg_smul]; abel
    rw [hv]
  · intro τ hτ
    have hr := hmem τ hτ
    exact ((s67bd_qualitative_regular H j M hM (f (T - τ)) (hf.c2 _ hr) (hBf _ hr).1).1).of_le
      (by exact_mod_cast (by omega : j + 1 ≤ j + 5))
  · refine ⟨|β⁻¹| * Mb1 + Cf, CJ * Bf, add_nonneg (mul_nonneg (abs_nonneg _) hMb1) hCf0,
      mul_nonneg hCJ0 hBf0, fun τ hτ => ?_, fun τ hτ => ?_⟩
    · have hr := hmem τ hτ
      have hfun : (fun x => -movForce d s ρ₀ x - s67bd_F d s ρ₀ (movV ρ₀ ρ (T - τ)) x) =
          fun y => β⁻¹ • s67bd_oneBodyB d s β ρ₀ y - s67bd_F d s ρ₀ (movV ρ₀ ρ (T - τ)) y := by
        funext x; rw [hmf x]
      rw [hfun]
      refine ⟨(hMb.1.const_smul β⁻¹).sub (hFrep _ hr), fun i hi x => ?_⟩
      obtain ⟨hvm, -⟩ := hρ.weighted (T - τ) hr.1
      have h5 := (hCf _ (hvcont _ hr) hvm).2.2.2.2
      have hF1 := s67bd63_cb_le (v := s67bd_F d s ρ₀ (movV ρ₀ ρ (T - τ)))
        (le_trans le_self_add h5) hi x
      have hCfo : max (Cf * oscNorm (m : ℝ) (movV ρ₀ ρ (T - τ))) 0 ≤ Cf := by
        refine max_le ?_ hCf0
        have := hosc _ hr
        nlinarith [HRS.MS.MovC1.movc1_osc_nonneg (m : ℝ) (movV ρ₀ ρ (T - τ))]
      have hiC : (i : WithTop ℕ∞) ≤ ((j + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hi
      have hA : ContDiffAt ℝ (i : WithTop ℕ∞) (fun y => β⁻¹ • s67bd_oneBodyB d s β ρ₀ y) x :=
        ((hMb.1.const_smul β⁻¹).of_le hiC).contDiffAt
      have hB : ContDiffAt ℝ (i : WithTop ℕ∞) (s67bd_F d s ρ₀ (movV ρ₀ ρ (T - τ))) x :=
        ((hFrep _ hr).of_le hiC).contDiffAt
      have hoB : ContDiffAt ℝ (i : WithTop ℕ∞) (s67bd_oneBodyB d s β ρ₀) x :=
        (hMb.1.of_le hiC).contDiffAt
      have e : iteratedFDeriv ℝ i (fun y => β⁻¹ • s67bd_oneBodyB d s β ρ₀ y -
          s67bd_F d s ρ₀ (movV ρ₀ ρ (T - τ)) y) x =
          β⁻¹ • iteratedFDeriv ℝ i (s67bd_oneBodyB d s β ρ₀) x -
            iteratedFDeriv ℝ i (s67bd_F d s ρ₀ (movV ρ₀ ρ (T - τ))) x := by
        rw [show (fun y => β⁻¹ • s67bd_oneBodyB d s β ρ₀ y -
          s67bd_F d s ρ₀ (movV ρ₀ ρ (T - τ)) y) = (fun y => β⁻¹ • s67bd_oneBodyB d s β ρ₀ y) -
            s67bd_F d s ρ₀ (movV ρ₀ ρ (T - τ)) from rfl,
          iteratedFDeriv_sub_apply hA hB, iteratedFDeriv_const_smul_apply' hoB]
      rw [e]
      refine (norm_sub_le _ _).trans (add_le_add ?_ (hF1.trans hCfo))
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left (hMb.2 i hi x) (abs_nonneg _)
    · have hr := hmem τ hτ
      have hJ := hCJ R0 c0 hR0 hR1 hc0 f0 ρ hρ _ hr.1 (f (T - τ)) (hmemcb _ hr) (hBf _ hr).1
      refine ⟨hJ.1.of_le (by exact_mod_cast (by omega : j ≤ j + 2)), fun i hi x => ?_⟩
      exact (hJ.2 i (by omega) x).trans (mul_le_mul_of_nonneg_left (hBf _ hr).2 hCJ0)

end HRS.MS.BreakdownS67
