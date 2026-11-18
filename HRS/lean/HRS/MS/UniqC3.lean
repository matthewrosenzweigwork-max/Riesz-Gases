import HRS.MS.BilipV
import HRS.Whole.AppendixBKernel

/-!
# Packet C3, part 1: facts about the flow `Ψ` and its inverse `Function.invFun (Ψ τ)`

Setting: `IsAdvectingDrift m Cb t b` (`HRS.Whole`), `IsNegDriftFlow t b Ψ` (with `bij`).  Collected here
(`FlowFacts`): inverse identities, Lipschitz bounds `e^{Cb τ}`, `C^{m+1}` regularity of the inverse and joint
continuity in `(τ,x)` of `Ψ`, of `Ψ_τ^{-1}` and of the spatial derivatives `fderiv (Ψ τ)`, `fderiv (Ψ_τ^{-1})`
(the latter via the parametrisation `Ξ : ℝ^d → ℝ →ᵇ ℝ^d` of `FlowC` and inversion of the Jacobian).
-/

noncomputable section

open Set MeasureTheory Filter Topology
open scoped ENNReal ContDiff
open HRS HRS.Whole

namespace HRS.MS.UniqC3

variable {d : ℕ}

/-- Adaptor: `IsAdvectingDrift` gives the drift bounds of Appendix S.A. -/
theorem uc3_drift {m : ℕ} {Cb T : ℝ} {b : ℝ → Euc d → Euc d} (hb : IsAdvectingDrift m Cb T b) :
    AppendixALemmas.IsDriftBounds T m Cb b where
  cont := hb.cont
  smooth τ hτ := by
    have h := hb.smooth τ hτ
    push_cast
    exact h
  deriv_bound := hb.deriv_bdd
  growth := hb.growth

/-- Adaptor: the flow of Appendix S.B (with `bij`) is a flow of Appendix S.A. -/
theorem uc3_flow {T : ℝ} {b : ℝ → Euc d → Euc d} {Ψ : ℝ → Euc d → Euc d}
    (hΨ : IsNegDriftFlow T b Ψ) : AppendixALemmas.IsNegDriftFlow T b Ψ :=
  ⟨hΨ.init, hΨ.ode⟩

theorem uc3_Cb_nonneg {m : ℕ} {Cb T : ℝ} (hT : 0 ≤ T) {b : ℝ → Euc d → Euc d}
    (hb : IsAdvectingDrift m Cb T b) : 0 ≤ Cb :=
  HRS.MS.FlowD.Λ_nonneg' hT (uc3_drift hb)

/-- The facts about `Ψ` and `Ψ_τ^{-1} := Function.invFun (Ψ τ)` used by the cutoff packet. -/
structure FlowFacts (m : ℕ) (Cb t : ℝ) (Ψ : ℝ → Euc d → Euc d) : Prop where
  inv_left : ∀ τ ∈ Icc (0 : ℝ) t, ∀ x, Function.invFun (Ψ τ) (Ψ τ x) = x
  inv_right : ∀ τ ∈ Icc (0 : ℝ) t, ∀ y, Ψ τ (Function.invFun (Ψ τ) y) = y
  lip : ∀ τ ∈ Icc (0 : ℝ) t, ∀ x y, ‖Ψ τ x - Ψ τ y‖ ≤ Real.exp (Cb * τ) * ‖x - y‖
  lip_inv : ∀ τ ∈ Icc (0 : ℝ) t, ∀ x y,
    ‖Function.invFun (Ψ τ) x - Function.invFun (Ψ τ) y‖ ≤ Real.exp (Cb * τ) * ‖x - y‖
  contDiff : ∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Ψ τ)
  contDiff_inv : ∀ τ ∈ Icc (0 : ℝ) t, ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) (Function.invFun (Ψ τ))
  cont : ContinuousOn (fun p : ℝ × Euc d => Ψ p.1 p.2) (Icc (0 : ℝ) t ×ˢ univ)
  cont_inv : ContinuousOn (fun p : ℝ × Euc d => Function.invFun (Ψ p.1) p.2) (Icc (0 : ℝ) t ×ˢ univ)
  cont_fderiv : ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (Ψ p.1) p.2) (Icc (0 : ℝ) t ×ˢ univ)
  cont_fderiv_inv :
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (Function.invFun (Ψ p.1)) p.2) (Icc (0 : ℝ) t ×ˢ univ)

section Proofs

variable {m : ℕ} {Cb T : ℝ} {b : ℝ → Euc d → Euc d} {Ψ : ℝ → Euc d → Euc d}

theorem uc3_hinv (hΨ : IsNegDriftFlow T b Ψ) :
    ∀ τ ∈ Icc (0 : ℝ) T, (∀ x, Function.invFun (Ψ τ) (Ψ τ x) = x) ∧
      (∀ y, Ψ τ (Function.invFun (Ψ τ) y) = y) := fun τ hτ =>
  ⟨fun x => Function.leftInverse_invFun (hΨ.bij τ hτ).1 x,
    fun y => Function.rightInverse_invFun (hΨ.bij τ hτ).2 y⟩

/-- Joint continuity of the inverse flow. -/
theorem uc3_cont_inv (hT : 0 ≤ T) (hbD : AppendixALemmas.IsDriftBounds T m Cb b)
    (hΨ : IsNegDriftFlow T b Ψ) :
    ContinuousOn (fun p : ℝ × Euc d => Function.invFun (Ψ p.1) p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  have hΨA := uc3_flow hΨ
  have hinv := uc3_hinv hΨ
  have hlip := HRS.MS.FlowD.inv_lip hT hbD hΨA (fun τ => Function.invFun (Ψ τ)) hinv
  refine continuousOn_prod_of_continuousOn_lipschitzOnWith'
    (f := fun p : ℝ × Euc d => Function.invFun (Ψ p.1) p.2) (s := Icc (0 : ℝ) T) (t := univ)
    (Real.exp (Cb * T)).toNNReal ?_ ?_
  · intro a ha
    refine LipschitzOnWith.of_dist_le_mul fun x _ y _ => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (Real.exp_pos _).le]
    refine (hlip a ha x y).trans ?_
    have hC := HRS.MS.FlowD.Λ_nonneg' hT hbD
    gcongr
    exact ha.2
  · intro y _
    obtain ⟨L, hL0, hL⟩ := HRS.MS.FlowD.inv_time_lip hT hbD hΨA (fun τ => Function.invFun (Ψ τ))
      hinv y
    have : LipschitzOnWith L.toNNReal (fun τ => Function.invFun (Ψ τ) y) (Icc (0 : ℝ) T) :=
      LipschitzOnWith.of_dist_le_mul fun τ' hτ' τ hτ => by
        rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0]
        exact hL τ hτ τ' hτ'
    exact this.continuousOn

/-- Joint continuity of the spatial derivative of the flow, through the parametrisation `Ξ`. -/
theorem uc3_cont_fderiv (hT : 0 ≤ T) (hbD : AppendixALemmas.IsDriftBounds T m Cb b)
    (hΨ : IsNegDriftFlow T b Ψ) :
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (Ψ p.1) p.2) (Icc (0 : ℝ) T ×ˢ univ) := by
  have hΨA := uc3_flow hΨ
  obtain ⟨Ξ, hΞ, -, hΞΨ⟩ := HRS.MS.FlowC.fc_exists_param hT (HRS.MS.FlowB.db_of_drift hbD)
    hΨA.init (fun x => HRS.MS.FlowA.sol_of_flow hΨA x)
  have hΞd : Differentiable ℝ Ξ := hΞ.differentiable (by exact_mod_cast Nat.succ_ne_zero m)
  have hfd : ∀ τ ∈ Icc (0 : ℝ) T, ∀ x, fderiv ℝ (Ψ τ) x =
      (BoundedContinuousFunction.evalCLM ℝ τ).comp (fderiv ℝ Ξ x) := by
    intro τ hτ x
    have hfun : Ψ τ = (BoundedContinuousFunction.evalCLM (β := Euc d) ℝ τ) ∘ Ξ :=
      funext fun y => (hΞΨ y τ hτ).symm
    rw [hfun]
    exact ((BoundedContinuousFunction.evalCLM (β := Euc d) ℝ τ).hasFDerivAt.comp x
      (hΞd x).hasFDerivAt).fderiv
  have hcf : Continuous (fderiv ℝ Ξ) := by
    refine hΞ.continuous_fderiv ?_
    exact_mod_cast Nat.succ_ne_zero m
  refine continuousOn_clm_apply.2 fun v => ?_
  have hc : Continuous fun p : ℝ × Euc d => (fderiv ℝ Ξ p.2 v) p.1 :=
    ((hcf.clm_apply continuous_const).comp continuous_snd).eval continuous_fst
  refine hc.continuousOn.congr fun p hp => ?_
  rw [hfd p.1 hp.1 p.2]
  rfl

set_option synthInstance.maxHeartbeats 400000 in
/-- Joint continuity of the derivative of the inverse flow, from the inverse-Jacobian formula. -/
theorem uc3_cont_fderiv_inv (hT : 0 ≤ T) (hbD : AppendixALemmas.IsDriftBounds T m Cb b)
    (hΨ : IsNegDriftFlow T b Ψ) :
    ContinuousOn (fun p : ℝ × Euc d => fderiv ℝ (Function.invFun (Ψ p.1)) p.2)
      (Icc (0 : ℝ) T ×ˢ univ) := by
  have hΨA := uc3_flow hΨ
  have hinv := uc3_hinv hΨ
  have hA := uc3_cont_fderiv hT hbD hΨ
  have hΦ := uc3_cont_inv hT hbD hΨ
  have hg : ContinuousOn (fun p : ℝ × Euc d =>
      fderiv ℝ (Ψ p.1) (Function.invFun (Ψ p.1) p.2)) (Icc (0 : ℝ) T ×ˢ univ) :=
    hA.comp (continuousOn_fst.prodMk hΦ) (fun p hp => ⟨hp.1, mem_univ _⟩)
  intro p hp
  have hτ := hp.1
  obtain ⟨hl, hr⟩ := hinv p.1 hτ
  have hΨd : Differentiable ℝ (Ψ p.1) :=
    (HRS.MS.FlowB.flow_contDiff hT hbD hΨA p.1 hτ).differentiable
      (by exact_mod_cast Nat.succ_ne_zero m)
  have hΦd : Differentiable ℝ (Function.invFun (Ψ p.1)) :=
    ((HRS.MS.FlowB.flow_inv_contDiff hT hbD hΨA p.1 hτ _ hl hr).1).differentiable
      (by exact_mod_cast Nat.succ_ne_zero m)
  -- both products of the Jacobians are the identity at every point of the slice
  have key : ∀ q ∈ Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d)),
      (fderiv ℝ (Function.invFun (Ψ q.1)) q.2) *
        (fderiv ℝ (Ψ q.1) (Function.invFun (Ψ q.1) q.2)) = 1 ∧
      (fderiv ℝ (Ψ q.1) (Function.invFun (Ψ q.1) q.2)) *
        (fderiv ℝ (Function.invFun (Ψ q.1) ) q.2) = 1 := by
    intro q hq
    obtain ⟨hl', hr'⟩ := hinv q.1 hq.1
    have hΨd' : Differentiable ℝ (Ψ q.1) :=
      (HRS.MS.FlowB.flow_contDiff hT hbD hΨA q.1 hq.1).differentiable
        (by exact_mod_cast Nat.succ_ne_zero m)
    have hΦd' : Differentiable ℝ (Function.invFun (Ψ q.1)) :=
      ((HRS.MS.FlowB.flow_inv_contDiff hT hbD hΨA q.1 hq.1 _ hl' hr').1).differentiable
        (by exact_mod_cast Nat.succ_ne_zero m)
    set x := Function.invFun (Ψ q.1) q.2 with hx
    have hy : Ψ q.1 x = q.2 := hr' q.2
    constructor
    · have h1 : HasFDerivAt (Function.invFun (Ψ q.1) ∘ Ψ q.1)
          ((fderiv ℝ (Function.invFun (Ψ q.1)) q.2).comp (fderiv ℝ (Ψ q.1) x)) x := by
        have := (hΦd' (Ψ q.1 x)).hasFDerivAt.comp x (hΨd' x).hasFDerivAt
        rwa [hy] at this
      have h2 : HasFDerivAt (Function.invFun (Ψ q.1) ∘ Ψ q.1) (ContinuousLinearMap.id ℝ (Euc d)) x :=
        (hasFDerivAt_id x).congr_of_eventuallyEq
          (Eventually.of_forall fun y => hl' y)
      exact h1.unique h2
    · have h1 : HasFDerivAt (Ψ q.1 ∘ Function.invFun (Ψ q.1))
          ((fderiv ℝ (Ψ q.1) x).comp (fderiv ℝ (Function.invFun (Ψ q.1)) q.2)) q.2 := by
        have := (hΨd' x).hasFDerivAt.comp q.2 (hΦd' q.2).hasFDerivAt
        exact this
      have h2 : HasFDerivAt (Ψ q.1 ∘ Function.invFun (Ψ q.1)) (ContinuousLinearMap.id ℝ (Euc d)) q.2 :=
        (hasFDerivAt_id q.2).congr_of_eventuallyEq
          (Eventually.of_forall fun y => hr' y)
      exact h1.unique h2
  obtain ⟨k1, k2⟩ := key p hp
  let u : (Euc d →L[ℝ] Euc d)ˣ := ⟨fderiv ℝ (Ψ p.1) (Function.invFun (Ψ p.1) p.2),
    fderiv ℝ (Function.invFun (Ψ p.1)) p.2, k2, k1⟩
  have hi : ContinuousAt Ring.inverse
      (fderiv ℝ (Ψ p.1) (Function.invFun (Ψ p.1) p.2)) := NormedRing.inverse_continuousAt u
  have hc := ContinuousAt.comp_continuousWithinAt (g := Ring.inverse)
    (f := fun q : ℝ × Euc d => fderiv ℝ (Ψ q.1) (Function.invFun (Ψ q.1) q.2)) hi (hg p hp)
  refine hc.congr (fun q hq => ?_) ?_
  · obtain ⟨j1, j2⟩ := key q hq
    let u' : (Euc d →L[ℝ] Euc d)ˣ := ⟨fderiv ℝ (Ψ q.1) (Function.invFun (Ψ q.1) q.2),
      fderiv ℝ (Function.invFun (Ψ q.1)) q.2, j2, j1⟩
    exact (Ring.inverse_unit u').symm
  · exact (Ring.inverse_unit u).symm

theorem uc3_flowFacts (hT : 0 ≤ T) (hb : IsAdvectingDrift m Cb T b) (hΨ : IsNegDriftFlow T b Ψ) :
    FlowFacts m Cb T Ψ := by
  have hbD := uc3_drift hb
  have hΨA := uc3_flow hΨ
  have hinv := uc3_hinv hΨ
  exact
  { inv_left := fun τ hτ => (hinv τ hτ).1
    inv_right := fun τ hτ => (hinv τ hτ).2
    lip := fun τ hτ x y => HRS.MS.FlowA.flow_lipschitz hT hbD hΨA τ hτ x y
    lip_inv := fun τ hτ x y =>
      HRS.MS.FlowD.inv_lip hT hbD hΨA (fun τ => Function.invFun (Ψ τ)) hinv τ hτ x y
    contDiff := fun τ hτ => HRS.MS.FlowB.flow_contDiff hT hbD hΨA τ hτ
    contDiff_inv := fun τ hτ =>
      (HRS.MS.FlowB.flow_inv_contDiff hT hbD hΨA τ hτ _ (hinv τ hτ).1 (hinv τ hτ).2).1
    cont := HRS.MS.FlowA.flow_continuous hT hbD hΨA
    cont_inv := uc3_cont_inv hT hbD hΨ
    cont_fderiv := uc3_cont_fderiv hT hbD hΨ
    cont_fderiv_inv := uc3_cont_fderiv_inv hT hbD hΨ }

end Proofs

end HRS.MS.UniqC3
