import HRS.MS.FlowC

/-!
# S.A.16 E1: path-independent derivative bounds of flows with separated growth constant

Copies of `FlowCAux2` (`fc_V_bound`, `fc_tay_norm`, `fc_base`, `fc_step`) and `FlowC` (`fc_induction`,
`fc_flow_bound`) in which the derivative bound `Λ` (`hdb`) is decoupled from the growth constant `Λg` of `DB`.
The growth constant enters only qualitatively (existence), never in the constants.
-/

open MeasureTheory Filter Topology Set Metric
open scoped BoundedContinuousFunction

namespace HRS.MS.SA16E1

open HRS.MS.FlowB

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [FiniteDimensional ℝ E]
  [CompleteSpace E]

theorem fc_V_bound {S : ℝ} (hS : 0 ≤ S) {m : ℕ} {Λ Λg : ℝ} {b : ℝ → E → E} (hb : DB S m Λg b)
    (hdb : ∀ τ ∈ Icc (0 : ℝ) S, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : E, ‖iteratedFDeriv ℝ j (b τ) x‖ ≤ Λ)
    (α : ℝ →ᵇ E) (γ : ℝ →ᵇ E) (t : ℝ) :
    ‖continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay S b α 1) γ t‖ ≤
      ∫ s in (0 : ℝ)..HRS.MS.FlowB.clampT S t, Λ * ‖γ s‖ := by
  have hct := HRS.MS.FlowB.clampT_nonneg S t
  have hB : HasB (fun s => iteratedFDeriv ℝ 1 (bt S b s) (α s)) :=
    (hb.good hS (by omega)).hasB α
  have hint0 := (hB.goodInt (fun _ => γ)).integrable 0 (HRS.MS.FlowB.clampT S t)
  have hint : IntervalIntegrable (fun s => fderiv ℝ (b (HRS.MS.FlowB.clampT S s)) (α s) (γ s)) volume 0
      (HRS.MS.FlowB.clampT S t) := by
    have e : (fun s => fderiv ℝ (b (HRS.MS.FlowB.clampT S s)) (α s) (γ s)) =
        intg 1 (fun s => iteratedFDeriv ℝ 1 (bt S b s) (α s)) (fun _ => γ) := by
      funext s; simp [intg, iteratedFDeriv_one_apply, bt]
    rw [e]; exact hint0
  rw [dnem_apply hS hb]
  refine (intervalIntegral.norm_integral_le_integral_norm hct).trans ?_
  refine intervalIntegral.integral_mono_on hct hint.norm ?_ fun s _ => ?_
  · exact ((γ.continuous.norm.const_mul Λ)).intervalIntegrable _ _
  · refine (ContinuousLinearMap.le_opNorm _ _).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
    rw [← norm_iteratedFDeriv_one (𝕜 := ℝ)]
    exact hdb (HRS.MS.FlowB.clampT S s) (HRS.MS.FlowB.clampT_mem hS s) 1 le_rfl (by omega) _

theorem fc_tay_norm {S : ℝ} (hS : 0 ≤ S) {m : ℕ} {Λ Λg : ℝ} {b : ℝ → E → E} (hb : DB S m Λg b)
    (hdb : ∀ τ ∈ Icc (0 : ℝ) S, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : E, ‖iteratedFDeriv ℝ j (b τ) x‖ ≤ Λ)
    (α : ℝ →ᵇ E) {k : ℕ} (hk1 : 1 ≤ k) (hkm : k ≤ m + 1) : ‖tay S b α k‖ ≤ Λ * S := by
  have hB : HasB (fun s => iteratedFDeriv ℝ k (bt S b s) (α s)) := (hb.good hS hkm).hasB α
  unfold tay
  refine (norm_Vop_le hS hB).trans ?_
  have h := intervalIntegral.norm_integral_le_of_norm_le_const (a := 0) (b := S) (C := Λ)
    (f := fun s => ‖iteratedFDeriv ℝ k (bt S b s) (α s)‖) (fun s _ => by
      rw [norm_norm]
      exact hdb (HRS.MS.FlowB.clampT S s) (HRS.MS.FlowB.clampT_mem hS s) k hk1 hkm (α s))
  calc _ ≤ ‖∫ s in (0 : ℝ)..S, ‖iteratedFDeriv ℝ k (bt S b s) (α s)‖‖ := Real.le_norm_self _
    _ ≤ Λ * |S - 0| := h
    _ = Λ * S := by rw [sub_zero, abs_of_nonneg hS]

section Step

variable {S : ℝ} {m : ℕ} {Λ Λg : ℝ} {b : ℝ → E → E} {Ξ : E → (ℝ →ᵇ E)}

theorem fc_base (hS : 0 ≤ S) (hb : DB S m Λg b)
    (hdb : ∀ τ ∈ Icc (0 : ℝ) S, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : E, ‖iteratedFDeriv ℝ j (b τ) x‖ ≤ Λ) (hΛ : 0 ≤ Λ)
    (hΞ : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Ξ) (hG : ∀ x, Gmap S b (Ξ x) = constCLM E x)
    (x0 : E) : ‖fderiv ℝ Ξ x0‖ ≤ Real.exp (Λ * S) := by
  have hn1 : ((m + 1 : ℕ) : WithTop ℕ∞) ≠ 0 := by exact_mod_cast Nat.succ_ne_zero m
  have hd : HasFDerivAt Ξ (fderiv ℝ Ξ x0) x0 := ((hΞ.differentiable hn1) x0).hasFDerivAt
  have hcomp := (hasFDerivAt_Gmap hS hb (Ξ x0)).comp x0 hd
  have hconst : HasFDerivAt (fun x => Gmap S b (Ξ x)) (constCLM E) x0 :=
    (constCLM E).hasFDerivAt.congr_of_eventuallyEq (Eventually.of_forall fun x => hG x)
  have huniq := hcomp.unique hconst
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  have hv := congrArg (fun L : E →L[ℝ] (ℝ →ᵇ E) => L v) huniq
  simp only [ContinuousLinearMap.comp_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.one_apply] at hv
  have := HRS.MS.FlowC.sup_gronwall hS hΛ
    (continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay S b (Ξ x0) 1))
    (fc_V_bound hS hb hdb (Ξ x0)) (fderiv ℝ Ξ x0 v) (constCLM E v) hv
  have hc : ‖constCLM E v‖ = ‖v‖ := BoundedContinuousFunction.norm_const_eq v
  rw [hc] at this
  exact this

theorem fc_ccl_zero {j : ℕ} (hj : 2 ≤ j) (x0 : E) :
    iteratedFDeriv ℝ j (⇑(constCLM E)) x0 = 0 := by
  obtain ⟨k, rfl⟩ : ∃ k, j = k + 2 := ⟨j - 2, by omega⟩
  ext v
  rw [iteratedFDeriv_succ_apply_right]
  have : (fun y => fderiv ℝ (⇑(constCLM E)) y) = fun _ => constCLM E := funext fun y =>
    (constCLM E).fderiv
  rw [this, iteratedFDeriv_succ_const]
  simp

theorem fc_step (hS : 0 ≤ S) (hb : DB S m Λg b)
    (hdb : ∀ τ ∈ Icc (0 : ℝ) S, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : E, ‖iteratedFDeriv ℝ j (b τ) x‖ ≤ Λ) (hΛ : 0 ≤ Λ)
    (hΞ : ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Ξ) (hG : ∀ x, Gmap S b (Ξ x) = constCLM E x)
    {j : ℕ} (hj2 : 2 ≤ j) (hjm : j ≤ m + 1) (x0 : E) {K : ℝ} (hK : 1 ≤ K)
    (hlow : ∀ i, 1 ≤ i → i < j → ‖iteratedFDeriv ℝ i Ξ x0‖ ≤ K) :
    ‖iteratedFDeriv ℝ j Ξ x0‖ ≤
      Real.exp (Λ * S) * (Fintype.card (OrderedFinpartition j) * (Λ * S) * K ^ j) := by
  set n : WithTop ℕ∞ := ((m + 1 : ℕ) : WithTop ℕ∞) with hn_def
  have hnem : HasFTaylorSeriesUpTo n (nem S b) (tay S b) := by
    have := hasFTaylor hS hb
    exact_mod_cast this
  have hjn : (j : WithTop ℕ∞) ≤ n := by rw [hn_def]; exact_mod_cast hjm
  have hcomp : HasFTaylorSeriesUpTo n (nem S b ∘ Ξ)
      (fun x => (tay S b (Ξ x)).taylorComp (ftaylorSeries ℝ Ξ x)) :=
    hasFTaylorSeriesUpToOn_univ_iff.1
      (HasFTaylorSeriesUpToOn.comp (hasFTaylorSeriesUpToOn_univ_iff.2 hnem)
        (hasFTaylorSeriesUpToOn_univ_iff.2 hΞ.ftaylorSeries) (mapsTo_univ _ _))
  have hD := hcomp.eq_iteratedFDeriv hjn x0
  have hident : (fun x => Ξ x + nem S b (Ξ x)) = ⇑(constCLM E) := funext fun x => hG x
  have hΞj : ContDiffAt ℝ (j : ℕ) Ξ x0 := (hΞ.of_le hjn).contDiffAt
  have hNj : ContDiffAt ℝ (j : ℕ) (nem S b ∘ Ξ) x0 :=
    (((contDiff_nem hS hb).comp hΞ).of_le hjn).contDiffAt
  have hdiff : iteratedFDeriv ℝ j (fun x => Ξ x + nem S b (Ξ x)) x0 =
      iteratedFDeriv ℝ j Ξ x0 + iteratedFDeriv ℝ j (nem S b ∘ Ξ) x0 :=
    iteratedFDeriv_add_apply hΞj hNj
  rw [hident, fc_ccl_zero hj2] at hdiff
  have hsum : iteratedFDeriv ℝ j Ξ x0 +
      (tay S b (Ξ x0)).taylorComp (ftaylorSeries ℝ Ξ x0) j = 0 := by
    rw [hD, ← hdiff]
  obtain ⟨R, hR, hRb⟩ := HRS.MS.FlowC.fc_fdb_split (n := j) (by omega) (tay S b (Ξ x0))
    (ftaylorSeries ℝ Ξ x0)
  have hRn := hRb (Λ * S) K hK (fun k hk1 hkj => fc_tay_norm hS hb hdb (Ξ x0) hk1 (hkj.trans hjm))
    (fun k hk1 hkj => hlow k hk1 hkj)
  set M : ℝ := Real.exp (Λ * S) * (Fintype.card (OrderedFinpartition j) * (Λ * S) * K ^ j)
    with hM
  have hM0 : 0 ≤ M := by positivity
  refine ContinuousMultilinearMap.opNorm_le_bound hM0 fun v => ?_
  have hv := congrArg (fun M : ContinuousMultilinearMap ℝ (fun _ : Fin j => E) (ℝ →ᵇ E) => M v) hsum
  rw [hR] at hv
  simp only [ContinuousMultilinearMap.add_apply, ContinuousMultilinearMap.zero_apply,
    ContinuousLinearMap.compContinuousMultilinearMap_coe, Function.comp_apply] at hv
  set η := iteratedFDeriv ℝ j Ξ x0 v with hη
  have h2 : η + continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay S b (Ξ x0) 1) η =
      -(R v) := by
    have : η + (continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay S b (Ξ x0) 1) η + R v) = 0 :=
      hv
    rw [← add_assoc] at this
    exact eq_neg_of_add_eq_zero_left this
  have h3 := HRS.MS.FlowC.sup_gronwall hS hΛ
    (continuousMultilinearCurryFin1 ℝ (ℝ →ᵇ E) (ℝ →ᵇ E) (tay S b (Ξ x0) 1))
    (fc_V_bound hS hb hdb (Ξ x0)) η (-(R v)) h2
  rw [norm_neg] at h3
  refine h3.trans ?_
  calc Real.exp (Λ * S) * ‖R v‖ ≤ Real.exp (Λ * S) * (‖R‖ * ∏ i, ‖v i‖) :=
        mul_le_mul_of_nonneg_left (R.le_opNorm v) (Real.exp_pos _).le
    _ ≤ Real.exp (Λ * S) * ((Fintype.card (OrderedFinpartition j) * (Λ * S) * K ^ j) *
          ∏ i, ‖v i‖) := by
        gcongr
    _ = M * ∏ i, ‖v i‖ := by rw [hM]; ring


end Step

/-- The induction on the order. -/
theorem fc_induction (m : ℕ) (T Λ : ℝ) (hΛ0 : 0 ≤ Λ) :
    ∀ n : ℕ, n ≤ m + 1 → ∃ K : ℝ, 1 ≤ K ∧ ∀ S : ℝ, 0 ≤ S → S ≤ T → ∀ Λg : ℝ, ∀ b : ℝ → E → E,
      DB S m Λg b → (∀ τ ∈ Icc (0 : ℝ) S, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : E, ‖iteratedFDeriv ℝ j (b τ) x‖ ≤ Λ) → ∀ Ξ : E → (ℝ →ᵇ E), ContDiff ℝ ((m + 1 : ℕ) : WithTop ℕ∞) Ξ →
      (∀ x, Gmap S b (Ξ x) = constCLM E x) →
      ∀ x : E, ∀ i : ℕ, 1 ≤ i → i ≤ n → ‖iteratedFDeriv ℝ i Ξ x‖ ≤ K := by
  intro n
  induction n with
  | zero => exact fun _ => ⟨1, le_rfl, fun _ _ _ _ _ _ _ _ _ _ i h1 h2 => by omega⟩
  | succ n ih =>
    intro hn
    obtain ⟨K, hK1, hK⟩ := ih (by omega)
    set K' : ℝ := max K (Real.exp (Λ * T) * (Fintype.card (OrderedFinpartition (n + 1)) *
      (Λ * T) * K ^ (n + 1))) with hK'
    set K'' : ℝ := max K' (Real.exp (Λ * T)) with hK''
    refine ⟨K'', hK1.trans ((le_max_left _ _).trans (le_max_left _ _)), ?_⟩
    intro S hS0 hST Λg b hb hdb Ξ hΞ hG x i hi1 hi2
    have hΛ := hΛ0
    have hexp : Real.exp (Λ * S) ≤ Real.exp (Λ * T) := Real.exp_le_exp.2 (by gcongr)
    by_cases hin : i ≤ n
    · exact (hK S hS0 hST Λg b hb hdb Ξ hΞ hG x i hi1 hin).trans
        ((le_max_left _ _).trans (le_max_left _ _))
    · have hi : i = n + 1 := by omega
      subst hi
      by_cases hn0 : n = 0
      · subst hn0
        rw [norm_iteratedFDeriv_one (𝕜 := ℝ)]
        exact ((fc_base hS0 hb hdb hΛ hΞ hG x).trans hexp).trans (le_max_right _ _)
      · have hlow : ∀ i, 1 ≤ i → i < n + 1 → ‖iteratedFDeriv ℝ i Ξ x‖ ≤ K := fun i h1 h2 =>
          hK S hS0 hST Λg b hb hdb Ξ hΞ hG x i h1 (by omega)
        refine (fc_step hS0 hb hdb hΛ hΞ hG (j := n + 1) (by omega) hn x hK1 hlow).trans ?_
        refine le_trans ?_ ((le_max_right K _).trans (le_max_left _ _))
        have hK0 : 0 ≤ K := by linarith
        have hcard : (0 : ℝ) ≤ Fintype.card (OrderedFinpartition (n + 1)) := by positivity
        have hΛS : Λ * S ≤ Λ * T := by gcongr
        calc Real.exp (Λ * S) * (Fintype.card (OrderedFinpartition (n + 1)) * (Λ * S) * K ^ (n + 1))
            ≤ Real.exp (Λ * T) * (Fintype.card (OrderedFinpartition (n + 1)) * (Λ * T) *
              K ^ (n + 1)) := by
              gcongr

/-- Uniform bound on all derivatives of the flow map, growth constant decoupled. -/
theorem fc_flow_bound (m : ℕ) (T Λ : ℝ) (hΛ0 : 0 ≤ Λ) :
    ∃ K : ℝ, 1 ≤ K ∧ ∀ S : ℝ, 0 ≤ S → S ≤ T → ∀ Λg : ℝ, ∀ b : ℝ → E → E, DB S m Λg b →
      (∀ τ ∈ Icc (0 : ℝ) S, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : E,
        ‖iteratedFDeriv ℝ j (b τ) x‖ ≤ Λ) →
      ∀ Ψ : ℝ → E → E, (∀ x, Ψ 0 x = x) → (∀ x, FlowA.Sol S b (fun τ => Ψ τ x)) →
      ∀ τ ∈ Icc (0 : ℝ) S, ∀ j : ℕ, 1 ≤ j → j ≤ m + 1 → ∀ x : E,
        ‖iteratedFDeriv ℝ j (Ψ τ) x‖ ≤ K := by
  obtain ⟨K, hK1, hK⟩ := fc_induction (E := E) m T Λ hΛ0 (m + 1) le_rfl
  refine ⟨K, hK1, fun S hS0 hST Λg b hb hdb Ψ h0 hs τ hτ j hj1 hjm x => ?_⟩
  obtain ⟨Ξ, hΞ, hG, hΞΨ⟩ := HRS.MS.FlowC.fc_exists_param hS0 hb h0 hs
  have hfun : Ψ τ = (BoundedContinuousFunction.evalCLM (β := E) ℝ τ) ∘ Ξ :=
    funext fun y => (hΞΨ y τ hτ).symm
  have hjn : (j : WithTop ℕ∞) ≤ ((m + 1 : ℕ) : WithTop ℕ∞) := by exact_mod_cast hjm
  have hL : ‖BoundedContinuousFunction.evalCLM (β := E) ℝ τ‖ ≤ 1 :=
    ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun γ => by
      simpa using γ.norm_coe_le_norm τ
  rw [hfun]
  refine (ContinuousLinearMap.norm_iteratedFDeriv_comp_left _ (hΞ.contDiffAt) hjn).trans ?_
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ j Ξ x‖ := mul_le_mul_of_nonneg_right hL (norm_nonneg _)
    _ ≤ K := by rw [one_mul]; exact hK S hS0 hST Λg b hb hdb Ξ hΞ hG x j hj1 hjm

end HRS.MS.SA16E1
