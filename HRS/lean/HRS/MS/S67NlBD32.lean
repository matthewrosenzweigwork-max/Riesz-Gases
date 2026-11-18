import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovAdjAux11
import HRS.MS.S67NlBD00
import HRS.MS.S67NlBD24
import HRS.MS.S67NlBD30
import HRS.MS.S67NlBD31

/-!
# S6.7nl.32: actual weighted `L²` source Duhamel and integrability
Source pin `b66ab61cf3f03a9c6f5a899ef5de61f2b34c5e44`.
Route: the source path `v ↦ T†(v-r) R_v` is weakly continuous on `[r,T]` (packet 30 plus strong
continuity of the constructed semigroup), hence strongly measurable in the separable Hilbert space
`L²_0`, and bounded by a uniform operator bound (Banach-Steinhaus); the scalar pairing identity
from the fundamental theorem for right derivatives (packet 31) holds for every Schwartz-realized core
element, and `s67_eq_of_core` upgrades it to the displayed equation.
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

/-- a weakly measurable map into a separable Hilbert space is measurable -/
lemma s67bd32_meas_of_weak {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SecondCountableTopology E] [MeasurableSpace E] [BorelSpace E] {α : Type*} [MeasurableSpace α]
    {c : α → E} (hw : ∀ z : E, Measurable (fun v => inner ℝ (c v) z)) : Measurable c := by
  classical
  -- a dense sequence in the closed unit ball
  obtain ⟨u, hu⟩ := TopologicalSpace.exists_dense_seq (Metric.closedBall (0 : E) 1)
  have hnorm : ∀ y : E, ‖y‖ = ⨆ n, inner ℝ y (u n : E) := by
    intro y
    have hle : ∀ n, inner ℝ y (u n : E) ≤ ‖y‖ := fun n => by
      have h1 := real_inner_le_norm y (u n : E)
      have h2 : ‖(u n : E)‖ ≤ 1 := mem_closedBall_zero_iff.1 (u n).2
      calc inner ℝ y (u n : E) ≤ ‖y‖ * ‖(u n : E)‖ := h1
        _ ≤ ‖y‖ * 1 := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = ‖y‖ := mul_one _
    have hbdd : BddAbove (Set.range fun n => inner ℝ y (u n : E)) := ⟨‖y‖, by
      rintro _ ⟨n, rfl⟩; exact hle n⟩
    rcases eq_or_ne y 0 with rfl | hy0
    · simp
    refine le_antisymm ?_ (ciSup_le hle)
    by_contra hlt
    push Not at hlt
    set M : ℝ := ⨆ n, inner ℝ y (u n : E) with hM
    have hypos : 0 < ‖y‖ := norm_pos_iff.2 hy0
    set w : E := ‖y‖⁻¹ • y with hw
    have hwn : ‖w‖ = 1 := by
      rw [hw, norm_smul, norm_inv, norm_norm, inv_mul_cancel₀ hypos.ne']
    have hwb : w ∈ Metric.closedBall (0 : E) 1 := by simp [hwn]
    set δ : ℝ := (‖y‖ - M) / (2 * ‖y‖) with hδ
    have hδpos : 0 < δ := by
      apply div_pos (by linarith) (by positivity)
    obtain ⟨n, hn⟩ := hu.exists_dist_lt (⟨w, hwb⟩ : Metric.closedBall (0 : E) 1) hδpos
    have hn' : ‖w - (u n : E)‖ < δ := by
      rw [← dist_eq_norm]; exact hn
    have hyw : inner ℝ y w = ‖y‖ := by
      rw [hw, real_inner_smul_right, real_inner_self_eq_norm_sq]
      field_simp
    have h3 : inner ℝ y (u n : E) = inner ℝ y w - inner ℝ y (w - (u n : E)) := by
      rw [inner_sub_right]; ring
    have h4 : inner ℝ y (w - (u n : E)) ≤ ‖y‖ * δ :=
      (real_inner_le_norm _ _).trans (mul_le_mul_of_nonneg_left hn'.le (norm_nonneg _))
    have h5 : ‖y‖ * δ = (‖y‖ - M) / 2 := by
      rw [hδ]; field_simp
    have h6 := le_ciSup hbdd n
    linarith
  have hnm : ∀ a : E, Measurable (fun v => ‖c v - a‖) := by
    intro a
    have : (fun v => ‖c v - a‖) = fun v => ⨆ n, inner ℝ (c v - a) (u n : E) :=
      funext fun v => hnorm _
    rw [this]
    refine Measurable.iSup fun n => ?_
    simp_rw [inner_sub_left]
    exact (hw _).sub measurable_const
  obtain ⟨dd, hdd⟩ := TopologicalSpace.exists_dense_seq E
  refine measurable_of_isOpen fun U hU => ?_
  have hunion : c ⁻¹' U = ⋃ (k : ℕ) (q : ℚ) (_ : Metric.ball (dd k) (q : ℝ) ⊆ U),
      {v | ‖c v - dd k‖ < (q : ℝ)} := by
    ext v
    simp only [mem_preimage, mem_iUnion, mem_setOf_eq]
    constructor
    · intro hv
      obtain ⟨ε, hε, hεU⟩ := Metric.isOpen_iff.1 hU _ hv
      obtain ⟨q, hq0, hq1⟩ := exists_rat_btwn (show (0 : ℝ) < ε / 2 by positivity)
      obtain ⟨k, hk⟩ := hdd.exists_dist_lt (c v) (show (0 : ℝ) < q from hq0)
      refine ⟨k, q, ?_, ?_⟩
      · intro z hz
        apply hεU
        rw [Metric.mem_ball] at hz ⊢
        have := dist_triangle z (dd k) (c v)
        rw [dist_comm (dd k) (c v)] at this
        linarith
      · rw [← dist_eq_norm]; exact hk
    · rintro ⟨k, q, hsub, hk⟩
      apply hsub
      rw [Metric.mem_ball, dist_eq_norm]
      exact hk
  rw [hunion]
  exact MeasurableSet.iUnion fun k => MeasurableSet.iUnion fun q => MeasurableSet.iUnion fun _ =>
    measurableSet_lt (hnm _) measurable_const

lemma s67bd32_aesm {E : Type*} [NormedAddCommGroup E] [InnerProductSpace ℝ E]
    [SecondCountableTopology E] {S : Set ℝ} (hS : MeasurableSet S) {c : ℝ → E}
    (hc : ∀ z : E, ContinuousOn (fun v => inner ℝ (c v) z) S) :
    AEStronglyMeasurable c (volume.restrict S) := by
  classical
  letI : MeasurableSpace E := borel E
  haveI : BorelSpace E := ⟨rfl⟩
  have hw : ∀ z : E, Measurable (fun v => inner ℝ (S.piecewise c (fun _ => (0 : E)) v) z) := by
    intro z
    have : (fun v => inner ℝ (S.piecewise c (fun _ => (0 : E)) v) z) =
        S.piecewise (fun v => inner ℝ (c v) z) (fun _ => (0 : ℝ)) := by
      funext v
      by_cases hv : v ∈ S <;> simp [Set.piecewise, hv]
    rw [this]
    exact (hc z).measurable_piecewise continuousOn_const hS
  have hm := s67bd32_meas_of_weak hw
  have hae : c =ᵐ[volume.restrict S] S.piecewise c (fun _ => (0 : E)) := by
    filter_upwards [ae_restrict_mem hS] with v hv
    simp [Set.piecewise, hv]
  exact hm.aestronglyMeasurable.congr hae.symm

set_option maxHeartbeats 1600000 in
theorem s67bd_duhamel_l2 (H : Mov2dTh d s β q ρ₀)
    (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x))
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
    ∀ r ∈ Icc (0 : ℝ) T,
      AEStronglyMeasurable (fun v => s67bd_Tdag H g hg (v - r) (R v))
        (volume.restrict (Icc r T)) ∧
      IntegrableOn (fun v => s67bd_Tdag H g hg (v - r) (R v)) (Icc r T) volume ∧
      Ψ r = s67bd_Tdag H g hg (T - r) (Ψ T) +
        ∫ v in Icc r T, s67bd_Tdag H g hg (v - r) (R v) := by
  intro r hr
  obtain ⟨hΨc, hRc, B, hB0, hB⟩ :=
    s67bd_source_continuity H m hm R0 c0 f0 ρ hρ T φ f hT hf Ψ R hrep
  have hr0 := hr.1
  have hrT := hr.2
  have hTc : ∀ z : MovL2Zero ρ₀, ContinuousOn (fun t => mov2d_T H g hg t z) (Ici 0) :=
    fun z => mov2d_T_cont H g hg z
  -- a uniform operator bound on `[0,T]`
  obtain ⟨M, hM⟩ : ∃ M : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ‖mov2d_T H g hg t‖ ≤ M := by
    have h := banach_steinhaus (g := fun t : Icc (0 : ℝ) T => mov2d_T H g hg t.1) (fun v => by
      obtain ⟨C, hC⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := T)).exists_bound_of_continuousOn
        ((hTc v).mono (fun t ht => ht.1))
      exact ⟨C, fun t => hC t.1 t.2⟩)
    obtain ⟨C, hC⟩ := h
    exact ⟨C, fun t ht => hC ⟨t, ht⟩⟩
  have hM0 : 0 ≤ M := (norm_nonneg (mov2d_T H g hg 0)).trans (hM 0 ⟨le_rfl, hT⟩)
  set F : ℝ → MovL2Zero ρ₀ := fun v => s67bd_Tdag H g hg (v - r) (R v) with hF
  -- weak continuity of the source path
  have hFw : ∀ z : MovL2Zero ρ₀, ContinuousOn (fun v => inner ℝ (F v) z) (Icc r T) := by
    intro z
    have e : ∀ v, inner ℝ (F v) z = inner ℝ (R v) (mov2d_T H g hg (v - r) z) := fun v =>
      ContinuousLinearMap.adjoint_inner_left _ _ _
    simp_rw [e]
    exact (hRc.mono (Icc_subset_Icc hr0 le_rfl)).inner
      ((hTc z).comp (continuousOn_id.sub continuousOn_const) (fun v hv => sub_nonneg.2 hv.1))
  have hAEM : AEStronglyMeasurable F (volume.restrict (Icc r T)) :=
    s67bd32_aesm measurableSet_Icc hFw
  have hFb : ∀ v ∈ Icc r T, ‖F v‖ ≤ M * B := by
    intro v hv
    have hv0 : v ∈ Icc (0 : ℝ) T := ⟨hr0.trans hv.1, hv.2⟩
    calc ‖F v‖ ≤ ‖s67bd_Tdag H g hg (v - r)‖ * ‖R v‖ := ContinuousLinearMap.le_opNorm _ _
      _ ≤ M * B := by
          have h1 : ‖s67bd_Tdag H g hg (v - r)‖ ≤ M := by
            unfold s67bd_Tdag
            rw [ContinuousLinearMap.adjoint.norm_map]
            exact hM _ ⟨sub_nonneg.2 hv.1, by linarith [hv.2]⟩
          have h2 : ‖R v‖ ≤ B := by linarith [hB v hv0, norm_nonneg (Ψ v)]
          exact mul_le_mul h1 h2 (norm_nonneg _) hM0
  have hInt : IntegrableOn F (Icc r T) volume := by
    refine Integrable.mono' (g := fun _ => M * B) (integrableOn_const (by simp)) hAEM ?_
    exact (ae_restrict_iff' measurableSet_Icc).2 (Filter.Eventually.of_forall hFb)
  refine ⟨hAEM, hInt, ?_⟩
  -- the identity, tested against the core
  refine s67_eq_of_core H g hg _ _ (fun z hz => ?_)
  set L : ℝ := T - r with hL
  have hL0 : 0 ≤ L := sub_nonneg.2 hrT
  have hrL : r + L = T := by rw [hL]; ring
  have hmaps : ∀ u ∈ Icc (0 : ℝ) L, r + u ∈ Icc (0 : ℝ) T := fun u hu =>
    ⟨by linarith [hu.1], by linarith [hu.2]⟩
  have hcomp : ContinuousOn (fun u : ℝ => r + u) (Icc (0 : ℝ) L) :=
    continuousOn_const.add continuousOn_id
  have hpc : ContinuousOn (fun u => inner ℝ (Ψ (r + u)) (mov2d_T H g hg u z)) (Icc 0 L) :=
    (hΨc.comp hcomp hmaps).inner ((hTc z).mono (fun u hu => hu.1))
  have hkc : ContinuousOn (fun u => inner ℝ (R (r + u)) (mov2d_T H g hg u z)) (Icc 0 L) :=
    (hRc.comp hcomp hmaps).inner ((hTc z).mono (fun u hu => hu.1))
  have hder : ∀ τ ∈ Ioo (0 : ℝ) L, HasDerivWithinAt
      (fun u => inner ℝ (Ψ (r + u)) (mov2d_T H g hg u z))
      (-(inner ℝ (R (r + τ)) (mov2d_T H g hg τ z))) (Ioi τ) τ := fun τ hτ =>
    (s67bd_core_pairing_derivative H g hg m hm R0 c0 f0 ρ hρ T φ f hT hf Ψ R hrep z hz r hr τ
      hτ).mono Ioi_subset_Ici_self
  have hftc := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hL0 hpc hder
    (hkc.neg.intervalIntegrable_of_Icc hL0)
  rw [intervalIntegral.integral_neg] at hftc
  have hp0 : inner ℝ (Ψ (r + 0)) (mov2d_T H g hg 0 z) = inner ℝ (Ψ r) z := by
    rw [add_zero, mov2d_T_zero H g hg]; rfl
  have hpL : inner ℝ (Ψ (r + L)) (mov2d_T H g hg L z) = inner ℝ (Ψ T) (mov2d_T H g hg L z) := by
    rw [hrL]
  -- the source integral
  have hconv : ∫ v in Icc r T, inner ℝ (R v) (mov2d_T H g hg (v - r) z) =
      ∫ u in (0 : ℝ)..L, inner ℝ (R (r + u)) (mov2d_T H g hg u z) := by
    rw [MeasureTheory.integral_Icc_eq_integral_Ioc, ← intervalIntegral.integral_of_le hrT]
    have := intervalIntegral.integral_comp_add_left
      (fun v => inner ℝ (R v) (mov2d_T H g hg (v - r) z)) r (a := 0) (b := L)
    simp only [add_zero, hrL, add_sub_cancel_left] at this
    exact this.symm
  have hin : inner ℝ (∫ v in Icc r T, F v) z =
      ∫ v in Icc r T, inner ℝ (R v) (mov2d_T H g hg (v - r) z) := by
    rw [real_inner_comm, ← integral_inner hInt]
    refine integral_congr_ae (Filter.Eventually.of_forall fun v => ?_)
    show inner ℝ z (F v) = _
    rw [real_inner_comm]
    exact ContinuousLinearMap.adjoint_inner_left _ _ _
  have hTd : inner ℝ (s67bd_Tdag H g hg L (Ψ T)) z = inner ℝ (Ψ T) (mov2d_T H g hg L z) :=
    ContinuousLinearMap.adjoint_inner_left _ _ _
  rw [inner_add_left, hin, hconv, hTd, ← hpL, ← hp0]
  rw [hp0, hpL] at hftc
  linarith

end HRS.MS.BreakdownS67
