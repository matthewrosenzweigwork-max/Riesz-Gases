import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.Mov63Aux3
import HRS.MS.S67NlBD06
import HRS.MS.S67NlBD07
import HRS.MS.S67NlBD20
import HRS.MS.S67NlBD24
import HRS.MS.S67NlBD25
import HRS.MS.S67NlBD26
import HRS.MS.S67NlBD28
import HRS.MS.S67NlBD29

/-!
# S6.7nl.30: `L²` source continuity from `Σ²` continuity
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Route: `R(v₁,ψ₁) - R(v₂,ψ₂) = R(v₁-v₂,ψ₁) + R(v₂,ψ₁-ψ₂)` pointwise (additivity of the cancellation
force on `C¹ ∩ L¹`, linearity of `W`, integrability of `√ρ₀ K` from packet 25), then packet 25 at
`σ = 2` on both terms; the `L²` norm of a represented element is the `Σ⁰` norm of its representative.
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

lemma s67bd30_D_sub {u w : Euc d → ℝ} (hu : Differentiable ℝ u) (hw : Differentiable ℝ w)
    (i : Fin d) (y : Euc d) :
    s67bd_D i (fun z => u z - w z) y = s67bd_D i u y - s67bd_D i w y := by
  unfold s67bd_D
  rw [fderiv_fun_sub (hu y) (hw y)]
  rfl

lemma s67bd30_W_sub {u w : Euc d → ℝ} (hu : Differentiable ℝ u) (hw : Differentiable ℝ w)
    (i : Fin d) (y : Euc d) :
    s67bd_W ρ₀ i (fun z => u z - w z) y = s67bd_W ρ₀ i u y - s67bd_W ρ₀ i w y := by
  unfold s67bd_W
  rw [s67bd30_D_sub hu hw i y]
  ring

/-- the `L²` norm of an element with a given representative -/
lemma s67bd30_norm_of_ae {z : MovL2Zero ρ₀} {g : Euc d → ℝ}
    (hg : MemLp g 2 (volume : Measure (Euc d)))
    (h : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun z x = g x) : ‖z‖ = oscNorm 0 g := by
  have e : ((z : Lp ℝ 2 (volume : Measure (Euc d)))) = hg.toLp g := by
    apply Lp.ext
    filter_upwards [h, hg.coeFn_toLp] with x h1 h2
    exact h1.trans h2.symm
  rw [← s67bd24_l2norm hg, ← e]
  rfl

lemma s67bd30_norm_sub_of_ae {z1 z2 : MovL2Zero ρ₀} {g1 g2 : Euc d → ℝ}
    (hg1 : MemLp g1 2 (volume : Measure (Euc d))) (hg2 : MemLp g2 2 (volume : Measure (Euc d)))
    (h1 : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun z1 x = g1 x)
    (h2 : ∀ᵐ x ∂(volume : Measure (Euc d)), movFun z2 x = g2 x) :
    ‖z1 - z2‖ = oscNorm 0 (fun x => g1 x - g2 x) := by
  refine s67bd30_norm_of_ae (hg1.sub hg2) ?_
  have := Lp.coeFn_sub (z1 : Lp ℝ 2 (volume : Measure (Euc d))) (z2 : Lp ℝ 2 (volume : Measure (Euc d)))
  filter_upwards [this, h1, h2] with x e a b
  have e' : movFun (z1 - z2) x = movFun z1 x - movFun z2 x := e
  rw [e', a, b]

/-- the projection of two pieces -/
lemma s67bd30_Q_diff {k1 k2 ka kb : Euc d → ℝ}
    (i1 : Integrable (fun x => Real.sqrt (ρ₀ x) * k1 x) volume)
    (i2 : Integrable (fun x => Real.sqrt (ρ₀ x) * k2 x) volume)
    (ia : Integrable (fun x => Real.sqrt (ρ₀ x) * ka x) volume)
    (ib : Integrable (fun x => Real.sqrt (ρ₀ x) * kb x) volume)
    (h : ∀ x, k1 x - k2 x = ka x + kb x) (x : Euc d) :
    s67bd_Q ρ₀ k1 x - s67bd_Q ρ₀ k2 x = s67bd_Q ρ₀ ka x + s67bd_Q ρ₀ kb x := by
  have hint : (∫ y, Real.sqrt (ρ₀ y) * k1 y) - (∫ y, Real.sqrt (ρ₀ y) * k2 y) =
      (∫ y, Real.sqrt (ρ₀ y) * ka y) + ∫ y, Real.sqrt (ρ₀ y) * kb y := by
    rw [← integral_sub i1 i2, ← integral_add ia ib]
    refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
    show Real.sqrt (ρ₀ y) * k1 y - Real.sqrt (ρ₀ y) * k2 y =
      Real.sqrt (ρ₀ y) * ka y + Real.sqrt (ρ₀ y) * kb y
    rw [← mul_sub, ← mul_add, h y]
  unfold s67bd_Q
  linear_combination h x - Real.sqrt (ρ₀ x) * hint

/-- regularity / integrability data of a good pair `(v, ψ)` -/
lemma s67bd30_good (H : Mov2dTh d s β q ρ₀) (m : ℕ) (hm : (d : ℝ) / 2 + 7 < m)
    {v ψ : Euc d → ℝ} (hv : Continuous v) (hvm : MemOsc (m : ℝ) v) (hψ2 : ContDiff ℝ 2 ψ)
    (hψm : MemOsc 2 ψ) (hψD : ∀ i : Fin d, MemLp (s67bd_D i ψ) 2 volume) :
    (ContDiff ℝ 1 (fun x => Real.sqrt (ρ₀ x) * v x) ∧
      Integrable (fun x => Real.sqrt (ρ₀ x) * v x) volume) ∧
    (∀ i : Fin d, ContDiff ℝ 1 (fun x => v x * s67bd_W ρ₀ i ψ x) ∧
      Integrable (fun x => v x * s67bd_W ρ₀ i ψ x) volume) ∧
    Integrable (fun x => Real.sqrt (ρ₀ x) * s67bd_K d s ρ₀ v ψ x) volume := by
  have hm6 : (2 : ℝ) + 4 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  have hsq2 : MemLp (fun x => Real.sqrt (ρ₀ x)) 2 (volume : Measure (Euc d)) := by
    have := (memOsc_schwartz 0 ψs).1
    rwa [hψs] at this
  have hsqsm : ContDiff ℝ ∞ (fun x => Real.sqrt (ρ₀ x)) := by
    rw [← hψs]; exact ψs.smooth _
  have hlog : ContDiff ℝ ∞ (fun y => Real.log (ρ₀ y)) :=
    hρsm.log (fun x => (hρpos x).ne')
  have hψ1 : ContDiff ℝ 1 ψ := hψ2.of_le (by norm_num)
  have hvC2 : ContDiff ℝ ((0 + 2 : ℕ) : WithTop ℕ∞) v :=
    (mn_force_bound H.hd H.hs0 H.hsd β q H.hβ H.hq ρ₀ H.hρ 0 m (by linarith)).choose_spec.2 v
      hv hvm |>.1
  have hvC1 : ContDiff ℝ 1 v := hvC2.of_le (by norm_num)
  have hD1 : ∀ (u : Euc d → ℝ), ContDiff ℝ 2 u → ∀ i : Fin d, ContDiff ℝ 1 (s67bd_D i u) := by
    intro u hu i
    unfold s67bd_D
    exact (hu.fderiv_right (m := 1) (by norm_num)).clm_apply contDiff_const
  have hW1 : ∀ i : Fin d, ContDiff ℝ 1 (s67bd_W ρ₀ i ψ) := fun i =>
    (hD1 ψ hψ2 i).sub (((hD1 _ (hlog.of_le (by simp)) i).mul hψ1).div_const 2)
  obtain ⟨C20, -, h20⟩ := s67bd_product_source H m 2 hm le_rfl hm6
  refine ⟨⟨(hsqsm.of_le (by simp)).mul hvC1, hsq2.integrable_mul hvm.1⟩,
    fun i => ⟨hvC1.mul (hW1 i), (h20 v ψ hvm hψ1 hψm hψD i).1⟩, ?_⟩
  -- integrability of `√ρ₀ K` from packet 25
  obtain ⟨C, -, hC⟩ := s67bd_projected_source_bound (ρ₀ := ρ₀) H m 2 hm le_rfl hm6
  have h25 := (hC v ψ hv hvm hψ2 hψm hψD).2.1
  by_contra hni
  have h0 : (∫ x, Real.sqrt (ρ₀ x) * s67bd_K d s ρ₀ v ψ x) = 0 := integral_undef hni
  have hR : s67bd_R d s ρ₀ v ψ = s67bd_K d s ρ₀ v ψ := by
    funext x
    unfold s67bd_R s67bd_Q
    rw [h0, mul_zero, sub_zero]
  rw [hR] at h25
  exact hni h25

/-- additivity identity for `K` -/
lemma s67bd30_K_diff (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {v1 v2 ψ1 ψ2 : Euc d → ℝ}
    (hψ1d : Differentiable ℝ ψ1) (hψ2d : Differentiable ℝ ψ2)
    (sa : ContDiff ℝ 1 (fun x => Real.sqrt (ρ₀ x) * (v1 x - v2 x)) ∧
      Integrable (fun x => Real.sqrt (ρ₀ x) * (v1 x - v2 x)) volume)
    (s2 : ContDiff ℝ 1 (fun x => Real.sqrt (ρ₀ x) * v2 x) ∧
      Integrable (fun x => Real.sqrt (ρ₀ x) * v2 x) volume)
    (wa : ∀ i : Fin d, ContDiff ℝ 1 (fun x => (v1 x - v2 x) * s67bd_W ρ₀ i ψ1 x) ∧
      Integrable (fun x => (v1 x - v2 x) * s67bd_W ρ₀ i ψ1 x) volume)
    (wb : ∀ i : Fin d, ContDiff ℝ 1
        (fun x => v2 x * s67bd_W ρ₀ i (fun y => ψ1 y - ψ2 y) x) ∧
      Integrable (fun x => v2 x * s67bd_W ρ₀ i (fun y => ψ1 y - ψ2 y) x) volume)
    (w2 : ∀ i : Fin d, ContDiff ℝ 1 (fun x => v2 x * s67bd_W ρ₀ i ψ2 x) ∧
      Integrable (fun x => v2 x * s67bd_W ρ₀ i ψ2 x) volume) (x : Euc d) :
    s67bd_K d s ρ₀ v1 ψ1 x - s67bd_K d s ρ₀ v2 ψ2 x =
      s67bd_K d s ρ₀ (fun y => v1 y - v2 y) ψ1 x +
        s67bd_K d s ρ₀ v2 (fun y => ψ1 y - ψ2 y) x := by
  have hF : s67bd_F d s ρ₀ v1 x =
      s67bd_F d s ρ₀ (fun y => v1 y - v2 y) x + s67bd_F d s ρ₀ v2 x := by
    unfold s67bd_F
    have := s67bd26_force_add hd hs0 hsd sa.1 s2.1 sa.2 s2.2 x
    rw [← this]
    have hfun : (fun y => Real.sqrt (ρ₀ y) * v1 y) =
        fun y => Real.sqrt (ρ₀ y) * (v1 y - v2 y) + Real.sqrt (ρ₀ y) * v2 y := by
      funext y; ring
    rw [hfun]
  have hB : ∀ i : Fin d, movForce d s (fun y => v1 y * s67bd_W ρ₀ i ψ1 y) x i =
      movForce d s (fun y => (v1 y - v2 y) * s67bd_W ρ₀ i ψ1 y) x i +
      movForce d s (fun y => v2 y * s67bd_W ρ₀ i (fun z => ψ1 z - ψ2 z) y) x i +
      movForce d s (fun y => v2 y * s67bd_W ρ₀ i ψ2 y) x i := by
    intro i
    have e1 := s67bd26_force_add hd hs0 hsd (wb i).1 (w2 i).1 (wb i).2 (w2 i).2 x
    have e2 := s67bd26_force_add hd hs0 hsd (wa i).1 ((wb i).1.add (w2 i).1) (wa i).2
      ((wb i).2.add (w2 i).2) x
    have hfun : (fun y => v1 y * s67bd_W ρ₀ i ψ1 y) =
        fun y => (v1 y - v2 y) * s67bd_W ρ₀ i ψ1 y +
          (v2 y * s67bd_W ρ₀ i (fun z => ψ1 z - ψ2 z) y + v2 y * s67bd_W ρ₀ i ψ2 y) := by
      funext y
      rw [s67bd30_W_sub hψ1d hψ2d i y]; ring
    rw [hfun, e2, e1]
    simp only [PiLp.add_apply]
    ring
  have hW : ∀ i : Fin d, ∀ y, s67bd_W ρ₀ i ψ1 y =
      s67bd_W ρ₀ i (fun z => ψ1 z - ψ2 z) y + s67bd_W ρ₀ i ψ2 y := by
    intro i y
    rw [s67bd30_W_sub hψ1d hψ2d i y]; ring
  have hS1 : (∑ i, s67bd_F d s ρ₀ v1 x i * s67bd_W ρ₀ i ψ1 x) -
      (∑ i, s67bd_F d s ρ₀ v2 x i * s67bd_W ρ₀ i ψ2 x) =
      (∑ i, s67bd_F d s ρ₀ (fun y => v1 y - v2 y) x i * s67bd_W ρ₀ i ψ1 x) +
      ∑ i, s67bd_F d s ρ₀ v2 x i * s67bd_W ρ₀ i (fun z => ψ1 z - ψ2 z) x := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hF, hW i x]
    simp only [PiLp.add_apply]
    ring
  have hS2 : (∑ i, movForce d s (fun y => v1 y * s67bd_W ρ₀ i ψ1 y) x i) -
      (∑ i, movForce d s (fun y => v2 y * s67bd_W ρ₀ i ψ2 y) x i) =
      (∑ i, movForce d s (fun y => (v1 y - v2 y) * s67bd_W ρ₀ i ψ1 y) x i) +
      ∑ i, movForce d s (fun y => v2 y * s67bd_W ρ₀ i (fun z => ψ1 z - ψ2 z) y) x i := by
    rw [← Finset.sum_sub_distrib, ← Finset.sum_add_distrib]
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [hB i]
    ring
  unfold s67bd_K
  linear_combination (-1 : ℝ) * hS1 + Real.sqrt (ρ₀ x) * hS2


lemma s67bd30_core (H : Mov2dTh d s β q ρ₀) (m : ℕ) (hm : (d : ℝ) / 2 + 7 < m) :
    ∃ C : ℝ, 0 ≤ C ∧
      (∀ v ψ : Euc d → ℝ, Continuous v → MemOsc (m : ℝ) v → ContDiff ℝ 2 ψ → MemOsc 2 ψ →
        (∀ i : Fin d, MemLp (s67bd_D i ψ) 2 volume) →
        MemOsc (2 - movA d s) (s67bd_R d s ρ₀ v ψ) ∧
        oscNorm (2 - movA d s) (s67bd_R d s ρ₀ v ψ) ≤ C * oscNorm (m : ℝ) v * oscNorm 2 ψ) ∧
      ∀ v1 v2 ψ1 ψ2 : Euc d → ℝ,
        Continuous v1 → MemOsc (m : ℝ) v1 → ContDiff ℝ 2 ψ1 → MemOsc 2 ψ1 →
        (∀ i : Fin d, MemLp (s67bd_D i ψ1) 2 volume) →
        Continuous v2 → MemOsc (m : ℝ) v2 → ContDiff ℝ 2 ψ2 → MemOsc 2 ψ2 →
        (∀ i : Fin d, MemLp (s67bd_D i ψ2) 2 volume) →
        MemOsc (2 - movA d s) (fun x => s67bd_R d s ρ₀ v1 ψ1 x - s67bd_R d s ρ₀ v2 ψ2 x) ∧
        oscNorm (2 - movA d s) (fun x => s67bd_R d s ρ₀ v1 ψ1 x - s67bd_R d s ρ₀ v2 ψ2 x) ≤
          C * oscNorm (m : ℝ) (fun x => v1 x - v2 x) * oscNorm 2 ψ1 +
          C * oscNorm (m : ℝ) v2 * oscNorm 2 (fun x => ψ1 x - ψ2 x) := by
  have hm6 : (2 : ℝ) + 4 < m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  obtain ⟨C, hC0, hC⟩ := s67bd_projected_source_bound (ρ₀ := ρ₀) H m 2 hm le_rfl hm6
  refine ⟨C, hC0, fun v ψ hv hvm hψ2 hψm hψD =>
    ⟨(hC v ψ hv hvm hψ2 hψm hψD).1, (hC v ψ hv hvm hψ2 hψm hψD).2.2.2⟩, ?_⟩
  intro v1 v2 ψ1 ψ2 hv1 hvm1 hψ21 hψm1 hψD1 hv2 hvm2 hψ22 hψm2 hψD2
  have hψ1d : Differentiable ℝ ψ1 := hψ21.differentiable (by norm_num)
  have hψ2d : Differentiable ℝ ψ2 := hψ22.differentiable (by norm_num)
  have hvA : Continuous (fun x => v1 x - v2 x) := hv1.sub hv2
  have hvmA : MemOsc (m : ℝ) (fun x => v1 x - v2 x) := mov2d_memOsc_sub hvm1 hvm2
  have hψ2B : ContDiff ℝ 2 (fun x => ψ1 x - ψ2 x) := hψ21.sub hψ22
  have hψmB : MemOsc 2 (fun x => ψ1 x - ψ2 x) := mov2d_memOsc_sub hψm1 hψm2
  have hψDB : ∀ i : Fin d, MemLp (s67bd_D i (fun x => ψ1 x - ψ2 x)) 2 volume := by
    intro i
    have e : s67bd_D i (fun x => ψ1 x - ψ2 x) = fun y => s67bd_D i ψ1 y - s67bd_D i ψ2 y :=
      funext (s67bd30_D_sub hψ1d hψ2d i)
    rw [e]
    exact (hψD1 i).sub (hψD2 i)
  have g1 := s67bd30_good H m hm hv1 hvm1 hψ21 hψm1 hψD1
  have g2 := s67bd30_good H m hm hv2 hvm2 hψ22 hψm2 hψD2
  have gA := s67bd30_good H m hm hvA hvmA hψ21 hψm1 hψD1
  have gB := s67bd30_good H m hm hv2 hvm2 hψ2B hψmB hψDB
  have hK : ∀ x, s67bd_K d s ρ₀ v1 ψ1 x - s67bd_K d s ρ₀ v2 ψ2 x =
      s67bd_K d s ρ₀ (fun y => v1 y - v2 y) ψ1 x +
        s67bd_K d s ρ₀ v2 (fun y => ψ1 y - ψ2 y) x :=
    fun x => s67bd30_K_diff H.hd H.hs0 H.hsd hψ1d hψ2d gA.1 g2.1 gA.2.1 gB.2.1 g2.2.1 x
  have hR : (fun x => s67bd_R d s ρ₀ v1 ψ1 x - s67bd_R d s ρ₀ v2 ψ2 x) =
      fun x => s67bd_R d s ρ₀ (fun y => v1 y - v2 y) ψ1 x +
        s67bd_R d s ρ₀ v2 (fun y => ψ1 y - ψ2 y) x := by
    funext x
    exact s67bd30_Q_diff g1.2.2 g2.2.2 gA.2.2 gB.2.2 hK x
  have hRA := hC (fun x => v1 x - v2 x) ψ1 hvA hvmA hψ21 hψm1 hψD1
  have hRB := hC v2 (fun x => ψ1 x - ψ2 x) hv2 hvm2 hψ2B hψmB hψDB
  rw [hR]
  obtain ⟨hmem, hn⟩ := HRS.MS.MovC1.movc1_osc_add (2 - movA d s) hRA.1 hRB.1
  refine ⟨hmem, hn.trans (add_le_add hRA.2.2.2 hRB.2.2.2)⟩

theorem s67bd_source_continuity (H : Mov2dTh d s β q ρ₀)
    (m : ℕ) (hm : (d : ℝ) / 2 + 7 < m) (R0 c0 : ℝ)
    (f0 : Euc d → ℝ) (ρ : ℝ → Euc d → ℝ)
    (hρ : MovInSmallClass d s q β ρ₀ m R0 c0 f0 ρ)
    (T : ℝ) (φ : Euc d → ℝ) (f : ℝ → Euc d → ℝ) (hT : 0 ≤ T)
    (hf : IsClassicalAdjointW ((quadraticGradientDyn d s q β).coeff ρ) T φ f)
    (Ψ R : ℝ → MovL2Zero ρ₀)
    (hrep : ∀ r ∈ Icc (0 : ℝ) T,
      (∀ᵐ x ∂(volume : Measure (Euc d)), movFun (Ψ r) x = s67psi ρ₀ (f r) x) ∧
      (∀ᵐ x ∂(volume : Measure (Euc d)), movFun (R r) x =
        s67bd_R d s ρ₀ (movV ρ₀ ρ r) (s67psi ρ₀ (f r)) x)) :
    ContinuousOn Ψ (Icc (0 : ℝ) T) ∧ ContinuousOn R (Icc (0 : ℝ) T) ∧
    ∃ B : ℝ, 0 ≤ B ∧ ∀ r ∈ Icc (0 : ℝ) T, ‖Ψ r‖ + ‖R r‖ ≤ B := by
  obtain ⟨hρsm, hρpos⟩ := mov2d_rho_data H
  obtain ⟨ψs, hψs⟩ := mov2d_sqrt_schwartz H
  have hsqc : Continuous (fun x => Real.sqrt (ρ₀ x)) := by
    rw [← hψs]; exact ψs.continuous
  have ha1 : 1 ≤ movA d s := le_max_left _ _
  have ha2 : movA d s < 2 := by
    unfold movA; exact max_lt (by norm_num) (by linarith [H.hsd])
  have hr0 : (0 : ℝ) ≤ 2 - movA d s := by linarith
  obtain ⟨C, hC0, hC1, hC2⟩ := s67bd30_core H m hm
  obtain ⟨Bψ, hBψ0, hBψ⟩ := s67bd_classical_sigma2 H ρ T φ f hT hf
  have h07 := s67bd_classical_sigma2_cont H ρ T φ f hT hf
  have hvc : ∀ t ∈ Icc (0 : ℝ) T, Continuous (movV ρ₀ ρ t) := by
    intro t ht
    show Continuous (fun x => (ρ t x - ρ₀ x) / Real.sqrt (ρ₀ x))
    exact ((hρ.regular t ht.1).sub hρsm.continuous).div hsqc
      (fun x => (Real.sqrt_pos.2 (hρpos x)).ne')
  set Mo : ℝ := |R0| * Real.exp (|c0| * T) with hMo
  have hMo0 : 0 ≤ Mo := by positivity
  have hosc : ∀ t ∈ Icc (0 : ℝ) T, oscNorm (m : ℝ) (movV ρ₀ ρ t) ≤ Mo := by
    intro t ht
    refine (hρ.weighted t ht.1).2.trans ?_
    calc R0 * Real.exp (-c0 * t) ≤ |R0| * Real.exp (-c0 * t) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (Real.exp_pos _).le
      _ ≤ |R0| * Real.exp (|c0| * T) := by
          apply mul_le_mul_of_nonneg_left _ (abs_nonneg _)
          apply Real.exp_le_exp.2
          calc -c0 * t ≤ |c0| * t := mul_le_mul_of_nonneg_right (neg_le_abs c0) ht.1
            _ ≤ |c0| * T := mul_le_mul_of_nonneg_left ht.2 (abs_nonneg _)
  have hcontv : ContinuousOn (fun t => OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ t))
      (Icc (0 : ℝ) T) := hρ.cont.mono Icc_subset_Ici_self
  -- good data of the actual pair
  have hg : ∀ r ∈ Icc (0 : ℝ) T,
      MemOsc 2 (s67psi ρ₀ (f r)) ∧ oscNorm 2 (s67psi ρ₀ (f r)) ≤ Bψ ∧
      ContDiff ℝ 2 (s67psi ρ₀ (f r)) ∧
      ∀ i : Fin d, MemLp (s67bd_D i (s67psi ρ₀ (f r))) 2 volume := hBψ
  have hRr : ∀ r ∈ Icc (0 : ℝ) T,
      MemOsc (2 - movA d s) (s67bd_R d s ρ₀ (movV ρ₀ ρ r) (s67psi ρ₀ (f r))) ∧
      oscNorm (2 - movA d s) (s67bd_R d s ρ₀ (movV ρ₀ ρ r) (s67psi ρ₀ (f r))) ≤
        C * oscNorm (m : ℝ) (movV ρ₀ ρ r) * oscNorm 2 (s67psi ρ₀ (f r)) := fun r hr =>
    hC1 _ _ (hvc r hr) (hρ.weighted r hr.1).1 (hg r hr).2.2.1 (hg r hr).1 (hg r hr).2.2.2
  -- norms of the represented elements
  have hΨn : ∀ r ∈ Icc (0 : ℝ) T, ‖Ψ r‖ ≤ Bψ := by
    intro r hr
    rw [s67bd30_norm_of_ae (hg r hr).1.1 (hrep r hr).1]
    exact ((mo_mono (by norm_num : (0 : ℝ) ≤ 2) (hg r hr).1).2).trans (hg r hr).2.1
  have hRn : ∀ r ∈ Icc (0 : ℝ) T, ‖R r‖ ≤ C * Mo * Bψ := by
    intro r hr
    rw [s67bd30_norm_of_ae (hRr r hr).1.1 (hrep r hr).2]
    refine ((mo_mono hr0 (hRr r hr).1).2).trans ((hRr r hr).2.trans ?_)
    have h1 := hosc r hr
    have h2 := (hg r hr).2.1
    have h3 : 0 ≤ oscNorm (m : ℝ) (movV ρ₀ ρ r) := Real.sqrt_nonneg _
    have h4 : 0 ≤ oscNorm 2 (s67psi ρ₀ (f r)) := Real.sqrt_nonneg _
    exact mul_le_mul (mul_le_mul_of_nonneg_left h1 hC0) h2 h4 (mul_nonneg hC0 hMo0)
  -- distances of differences
  have hΨd : ∀ r ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, dist (Ψ r) (Ψ u) ≤
      dist (OscSpace.ofFun (d := d) 2 (s67psi ρ₀ (f r))) (OscSpace.ofFun (d := d) 2 (s67psi ρ₀ (f u))) := by
    intro r hr u hu
    rw [dist_eq_norm, s67bd30_norm_sub_of_ae (hg r hr).1.1 (hg u hu).1.1 (hrep r hr).1 (hrep u hu).1,
      dist_eq_norm, ← mov2d_ofFun_sub (hg r hr).1 (hg u hu).1,
      OscSpace.norm_ofFun _ (mov2d_memOsc_sub (hg r hr).1 (hg u hu).1)]
    exact (mo_mono (by norm_num : (0 : ℝ) ≤ 2) (mov2d_memOsc_sub (hg r hr).1 (hg u hu).1)).2
  have hRd : ∀ r ∈ Icc (0 : ℝ) T, ∀ u ∈ Icc (0 : ℝ) T, dist (R r) (R u) ≤
      C * Bψ * dist (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ r))
        (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ u)) +
      C * Mo * dist (OscSpace.ofFun (d := d) 2 (s67psi ρ₀ (f r)))
        (OscSpace.ofFun (d := d) 2 (s67psi ρ₀ (f u))) := by
    intro r hr u hu
    obtain ⟨hmem, hn⟩ := hC2 _ _ _ _ (hvc r hr) (hρ.weighted r hr.1).1 (hg r hr).2.2.1
      (hg r hr).1 (hg r hr).2.2.2 (hvc u hu) (hρ.weighted u hu.1).1 (hg u hu).2.2.1
      (hg u hu).1 (hg u hu).2.2.2
    rw [dist_eq_norm, s67bd30_norm_sub_of_ae (hRr r hr).1.1 (hRr u hu).1.1 (hrep r hr).2 (hrep u hu).2]
    refine ((mo_mono hr0 hmem).2).trans (hn.trans (add_le_add ?_ ?_))
    · have e : oscNorm (m : ℝ) (fun x => movV ρ₀ ρ r x - movV ρ₀ ρ u x) =
          dist (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ r))
            (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ u)) := by
        rw [dist_eq_norm, ← mov2d_ofFun_sub (hρ.weighted r hr.1).1 (hρ.weighted u hu.1).1,
          OscSpace.norm_ofFun _ (mov2d_memOsc_sub (hρ.weighted r hr.1).1 (hρ.weighted u hu.1).1)]
      rw [e]
      have h1 := (hg r hr).2.1
      have h2 : 0 ≤ oscNorm 2 (s67psi ρ₀ (f r)) := Real.sqrt_nonneg _
      have h3 : 0 ≤ dist (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ r))
            (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ u)) := dist_nonneg
      calc C * dist (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ r))
            (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ u)) * oscNorm 2 (s67psi ρ₀ (f r))
          ≤ C * dist (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ r))
            (OscSpace.ofFun (d := d) (m : ℝ) (movV ρ₀ ρ u)) * Bψ :=
            mul_le_mul_of_nonneg_left h1 (mul_nonneg hC0 h3)
        _ = C * Bψ * _ := by ring
    · have e : oscNorm 2 (fun x => s67psi ρ₀ (f r) x - s67psi ρ₀ (f u) x) =
          dist (OscSpace.ofFun (d := d) 2 (s67psi ρ₀ (f r)))
            (OscSpace.ofFun (d := d) 2 (s67psi ρ₀ (f u))) := by
        rw [dist_eq_norm, ← mov2d_ofFun_sub (hg r hr).1 (hg u hu).1,
          OscSpace.norm_ofFun _ (mov2d_memOsc_sub (hg r hr).1 (hg u hu).1)]
      rw [e]
      exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left (hosc u hu) hC0) dist_nonneg
  refine ⟨?_, ?_, Bψ + C * Mo * Bψ, by positivity, fun r hr => add_le_add (hΨn r hr) (hRn r hr)⟩
  · intro u hu
    rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
    have hlI : ∀ᶠ r in 𝓝[Icc (0 : ℝ) T] u, r ∈ Icc (0 : ℝ) T := self_mem_nhdsWithin
    have tdψ := tendsto_iff_dist_tendsto_zero.1 (h07 u hu)
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg)
      (hlI.mono fun r hr => hΨd r hr u hu) tdψ
  · intro u hu
    rw [ContinuousWithinAt, tendsto_iff_dist_tendsto_zero]
    have hlI : ∀ᶠ r in 𝓝[Icc (0 : ℝ) T] u, r ∈ Icc (0 : ℝ) T := self_mem_nhdsWithin
    have tdψ := tendsto_iff_dist_tendsto_zero.1 (h07 u hu)
    have tdv := tendsto_iff_dist_tendsto_zero.1 (hcontv u hu)
    have := (tdv.const_mul (C * Bψ)).add (tdψ.const_mul (C * Mo))
    rw [mul_zero, mul_zero, add_zero] at this
    exact squeeze_zero' (Filter.Eventually.of_forall fun _ => dist_nonneg)
      (hlI.mono fun r hr => hRd r hr u hu) this

end HRS.MS.BreakdownS67
