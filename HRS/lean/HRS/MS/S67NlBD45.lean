import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovOpAux1
import HRS.MS.MovThermAux1
import HRS.MS.MovThermAux2
import HRS.MS.S67NlBD03
import HRS.MS.S67NlBD08
import HRS.MS.S67NlBD13
import HRS.MS.S67NlBD20
import HRS.MS.S67NlBD40

/-!
# S6.7nl.45: moving `J` product in `L¹` and `H^{M-1}`, high source regularity

`s67bd_J_product`.  Route: `η = √ρ₀` is a Gaussian-class function (Schwartz), so `η + v ∈ Σ^m` with
`‖η + v‖ ≤ ‖η‖ + 1`; packet 20 applies to `η + v`, `Ψ = s67psi ρ₀ u`, `σ = M`, the derivative `L²` hypothesis
being discharged from `u ∈ C_b²` and the Gaussian bounds; packet 40 gives `Ψ ∈ C^{j+5}`, the embedding gives
`v ∈ C^{j+4}` (`v` continuous), and `W_i Ψ = D_iΨ - (D_i log ρ₀) Ψ / 2` is `C^{j+4}`.
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

theorem s67bd45_D_contDiff {f : Euc d → ℝ} {n : ℕ} (hf : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f)
    (i : Fin d) : ContDiff ℝ (n : WithTop ℕ∞) (s67bd_D i f) := by
  unfold s67bd_D
  exact (hf.fderiv_right (m := (n : WithTop ℕ∞)) (by exact_mod_cast le_refl (n + 1))).clm_apply
    contDiff_const

theorem s67bd45_memLp_mul_bdd {f h : Euc d → ℝ} (hf : MemLp f 2 (volume : Measure (Euc d)))
    (hh : AEStronglyMeasurable h (volume : Measure (Euc d))) {K : ℝ} (hK : ∀ x, |h x| ≤ K) :
    MemLp (fun x => f x * h x) 2 (volume : Measure (Euc d)) := by
  refine hf.of_le_mul (c := K) (hf.aestronglyMeasurable.mul hh) (Eventually.of_forall fun x => ?_)
  simpa [Real.norm_eq_abs, abs_mul, mul_comm] using mul_le_mul_of_nonneg_right (hK x) (abs_nonneg (f x))

theorem s67bd_J_product (H : Mov2dTh d s β q ρ₀) (j M m : ℕ)
    (hM : (d : ℝ) / 2 + j + 5 < M) (hm : (d : ℝ) / 2 + 7 < m)
    (hmM : (M : ℝ) + 4 < m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ v u : Euc d → ℝ,
      Continuous v → MemOsc (m : ℝ) v → oscNorm (m : ℝ) v ≤ 1 →
      MemCb 2 u → MemOsc (M : ℝ) (s67psi ρ₀ u) → ∀ i : Fin d,
      ContDiff ℝ ((j + 4 : ℕ) : WithTop ℕ∞)
        (fun x => (Real.sqrt (ρ₀ x) + v x) * s67bd_W ρ₀ i (s67psi ρ₀ u) x) ∧
      Integrable (fun x => (Real.sqrt (ρ₀ x) + v x) * s67bd_W ρ₀ i (s67psi ρ₀ u) x) volume ∧
      HRS.PDE.ToolboxRd.MemSobolev ((M : ℝ) - 1)
        (fun x => (Real.sqrt (ρ₀ x) + v x) * s67bd_W ρ₀ i (s67psi ρ₀ u) x) ∧
      (∫ x, |(Real.sqrt (ρ₀ x) + v x) * s67bd_W ρ₀ i (s67psi ρ₀ u) x|) +
        s67bd_Hnorm ((M : ℝ) - 1)
          (fun x => (Real.sqrt (ρ₀ x) + v x) * s67bd_W ρ₀ i (s67psi ρ₀ u) x) ≤
            C * oscNorm (M : ℝ) (s67psi ρ₀ u) := by
  obtain ⟨B, -, hR, -⟩ := HRS.MS.Mov0.mv0_gapref H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  have hpos : ∀ x, 0 < ρ₀ x := hR.pos
  obtain ⟨hsq, -, c, hc, hk⟩ :=
    HRS.MS.Mov0.mv0_sqrt_gauss_thermal H.hd H.hs0 H.hsd H.hq H.hβ H.hρ
  have hG : HRS.MS.MovC1.MovcG (fun x => Real.sqrt (ρ₀ x)) := ⟨hsq, c, hc, hk⟩
  obtain ⟨φ, hφ⟩ := HRS.MS.MovC1.movc1_G_schwartz hG
  have hηm : MemOsc (m : ℝ) (fun x => Real.sqrt (ρ₀ x)) := by
    rw [← hφ]; exact memOsc_schwartz _ φ
  have hρs : ContDiff ℝ ∞ ρ₀ := (HRS.MS.Mov0.mv0_hgauss H.hd H.hs0 H.hsd H.hq H.hβ H.hρ).1
  have hlog : ContDiff ℝ ∞ (fun y => Real.log (ρ₀ y)) := hρs.log (fun x => (hpos x).ne')
  have hd0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hj0 : (0 : ℝ) ≤ j := Nat.cast_nonneg j
  obtain ⟨C20, hC20, h20⟩ := s67bd_product_source H m (M : ℝ) hm (by linarith) hmM
  obtain ⟨C0, -, hemb⟩ := HRS.MS.Mov63.mn_sobolev_emb_gen (d := d) (j + 4) m
    (by push_cast; linarith)
  refine ⟨C20 * (oscNorm (m : ℝ) (fun x => Real.sqrt (ρ₀ x)) + 1),
    mul_nonneg hC20 (add_nonneg (Real.sqrt_nonneg _) zero_le_one),
    fun v u hvc hv hv1 hu hΨ i => ?_⟩
  have hu2 : ContDiff ℝ 2 u := by exact_mod_cast hu.1
  obtain ⟨hcu, hcΨ, -⟩ := s67bd_qualitative_regular H j M hM u hu2 hΨ
  -- regularity of `v`
  obtain ⟨g, hg, hfg, -⟩ := hemb v hv
  have hveq : v = g := HRS.MS.Mov63.mn_ae_eq_cont hvc hg.continuous hfg
  have hv4 : ContDiff ℝ ((j + 4 : ℕ) : WithTop ℕ∞) v := by rw [hveq]; exact hg
  have hη4 : ContDiff ℝ ((j + 4 : ℕ) : WithTop ℕ∞) (fun x => Real.sqrt (ρ₀ x) + v x) :=
    (hsq.of_le (by first | exact WithTop.coe_le_coe.2 le_top | (simp; done) | (norm_cast; done))).add hv4
  -- regularity of `W_i Ψ`
  have hcΨ' : ContDiff ℝ ((j + 4 + 1 : ℕ) : WithTop ℕ∞) (s67psi ρ₀ u) := hcΨ
  have hDΨ := s67bd45_D_contDiff hcΨ' i
  have hlog5 : ContDiff ℝ ((j + 4 + 1 : ℕ) : WithTop ℕ∞) (fun y => Real.log (ρ₀ y)) :=
    hlog.of_le (by first | exact WithTop.coe_le_coe.2 le_top | (simp; done) | (norm_cast; done))
  have hDlog := s67bd45_D_contDiff hlog5 i
  have hW4 : ContDiff ℝ ((j + 4 : ℕ) : WithTop ℕ∞) (s67bd_W ρ₀ i (s67psi ρ₀ u)) := by
    unfold s67bd_W
    exact hDΨ.sub ((hDlog.mul (hcΨ'.of_le (by exact_mod_cast Nat.le_succ _))).div_const 2)
  -- derivative `L²` hypothesis
  have hD : ∀ i : Fin d, MemLp (s67bd_D i (s67psi ρ₀ u)) 2 (volume : Measure (Euc d)) := by
    intro i
    obtain ⟨K0, hK0⟩ := hu.2 0 (Nat.zero_le _)
    obtain ⟨K1, hK1⟩ := hu.2 1 (by norm_num)
    have hb0 : ∀ x, |u x| ≤ K0 := fun x => by
      have := hK0 ⟨x, rfl⟩
      simpa using this
    have hb1 : ∀ x, |s67bd_D i u x| ≤ K1 := fun x => by
      have h1 := hK1 ⟨x, rfl⟩
      simp only [norm_iteratedFDeriv_one] at h1
      unfold s67bd_D
      calc |fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))| =
          ‖fderiv ℝ u x (EuclideanSpace.single i (1 : ℝ))‖ := (Real.norm_eq_abs _).symm
        _ ≤ ‖fderiv ℝ u x‖ * ‖(EuclideanSpace.single i (1 : ℝ) : Euc d)‖ :=
            (fderiv ℝ u x).le_opNorm _
        _ ≤ K1 := by simpa using h1
    set c0 : ℝ := ∫ y, u y * ρ₀ y with hc0
    obtain ⟨φ', hφ'⟩ := HRS.MS.MovC1.movc1_G_schwartz (HRS.MS.MovC1.movc1_G_Dj hG i)
    have hηd : Differentiable ℝ (fun x => Real.sqrt (ρ₀ x)) := hsq.differentiable (by simp)
    have hud : Differentiable ℝ u := hu2.differentiable (by norm_num)
    have hform : s67bd_D i (s67psi ρ₀ u) = fun x =>
        mova3b1_Dj i (fun x => Real.sqrt (ρ₀ x)) x * (u x - c0) +
          Real.sqrt (ρ₀ x) * s67bd_D i u x := by
      funext x
      have h : HasFDerivAt (fun x => Real.sqrt (ρ₀ x) * (u x - c0)) _ x :=
        (hηd x).hasFDerivAt.mul ((hud x).hasFDerivAt.sub_const c0)
      unfold s67bd_D mova3b1_Dj
      have e : s67psi ρ₀ u = fun x => Real.sqrt (ρ₀ x) * (u x - c0) := rfl
      rw [e, h.fderiv]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      ring
    rw [hform]
    refine MemLp.add ?_ ?_
    · refine s67bd45_memLp_mul_bdd (K := K0 + |c0|) (by rw [← hφ']; exact φ'.memLp 2)
        (hu2.continuous.sub continuous_const).aestronglyMeasurable (fun x => ?_)
      calc |u x - c0| ≤ |u x| + |c0| := abs_sub _ _
        _ ≤ K0 + |c0| := by linarith [hb0 x]
    · have hm2 : MemLp (fun x => Real.sqrt (ρ₀ x)) 2 (volume : Measure (Euc d)) := by
        rw [← hφ]; exact φ.memLp 2
      exact s67bd45_memLp_mul_bdd hm2
        (((hu2.continuous_fderiv (by norm_num)).clm_apply continuous_const).aestronglyMeasurable)
        (K := K1) hb1
  have hΨ1 : ContDiff ℝ 1 (s67psi ρ₀ u) := (hcΨ.of_le (by exact_mod_cast (by omega : 1 ≤ j + 5)))
  have hηv : MemOsc (m : ℝ) (fun x => Real.sqrt (ρ₀ x) + v x) := (HRS.MS.MovC1.movc1_osc_add _ hηm hv).1
  obtain ⟨hI, hS, hbound⟩ := h20 (fun x => Real.sqrt (ρ₀ x) + v x) (s67psi ρ₀ u) hηv hΨ1 hΨ hD i
  refine ⟨hη4.mul hW4, hI, hS, hbound.trans ?_⟩
  have hn : oscNorm (m : ℝ) (fun x => Real.sqrt (ρ₀ x) + v x) ≤
      oscNorm (m : ℝ) (fun x => Real.sqrt (ρ₀ x)) + 1 :=
    (HRS.MS.MovC1.movc1_osc_add _ hηm hv).2.trans (by linarith)
  exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hn hC20) (Real.sqrt_nonneg _)

end HRS.MS.BreakdownS67
