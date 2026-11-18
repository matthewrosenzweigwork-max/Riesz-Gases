import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovAdjAux19

/-!
# S6.7 nonlinear, packet S6.7nl.53: a.e. singular-time parameter differentiation

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4835-4841, row
`S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions: none.
Adaptation of `HRS.MS.MovAdj.s67_param_deriv` to an a.e.-regular family: the induction on the
order carries integrability and the evaluation formula; the difference quotients are a.e.
strongly measurable as differences of integrable functions, dominated by `g t * prod ‖w‖` off a
null set (mean value theorem on the good set), and converge pointwise on the good set.
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
theorem s67bd_param_deriv_ae (d K : ℕ) (hK : 1 ≤ K) (τ : ℝ) (hτ : 0 ≤ τ)
    (G : ℝ → Euc d → ℝ) (g : ℝ → ℝ)
    (hGI : ∀ x, IntegrableOn (fun t => G t x) (Icc (0 : ℝ) τ) volume)
    (hgI : IntegrableOn g (Icc (0 : ℝ) τ) volume)
    (hae : ∀ᵐ t ∂(volume.restrict (Icc (0 : ℝ) τ)),
      ContDiff ℝ (K : WithTop ℕ∞) (G t) ∧ 0 ≤ g t ∧
      ∀ i, 1 ≤ i → i ≤ K → ∀ x, ‖iteratedFDeriv ℝ i (G t) x‖ ≤ g t)
    (Φ : Euc d → ℝ) (hΦ : ∀ x, Φ x = ∫ t in Icc (0 : ℝ) τ, G t x)
    (hΦK : ContDiff ℝ (K : WithTop ℕ∞) Φ) :
    (∀ i ≤ K, ∀ (x : Euc d) (w : Fin i → Euc d),
      IntegrableOn (fun t => iteratedFDeriv ℝ i (G t) x w) (Icc (0 : ℝ) τ) volume ∧
      iteratedFDeriv ℝ i Φ x w = ∫ t in Icc (0 : ℝ) τ, iteratedFDeriv ℝ i (G t) x w) ∧
    ∀ i, 1 ≤ i → i ≤ K → ∀ x,
      ‖iteratedFDeriv ℝ i Φ x‖ ≤ ∫ t in Icc (0 : ℝ) τ, g t := by
  have key : ∀ i ≤ K, ∀ (x : Euc d) (w : Fin i → Euc d),
      IntegrableOn (fun t => iteratedFDeriv ℝ i (G t) x w) (Icc (0 : ℝ) τ) volume ∧
      iteratedFDeriv ℝ i Φ x w = ∫ t in Icc (0 : ℝ) τ, iteratedFDeriv ℝ i (G t) x w := by
    intro i
    induction i with
    | zero =>
      intro _ x w
      refine ⟨?_, ?_⟩
      · simpa [iteratedFDeriv_zero_apply] using hGI x
      · simp only [iteratedFDeriv_zero_apply]
        exact hΦ x
    | succ i ih =>
      intro hi x w
      obtain ⟨v, w', rfl⟩ : ∃ (v : Euc d) (w' : Fin i → Euc d), w = Fin.cons v w' :=
        ⟨w 0, Fin.tail w, (Fin.cons_self_tail w).symm⟩
      have hiK : i ≤ K := (Nat.le_succ i).trans hi
      set Pw : ℝ := ∏ l : Fin (i + 1), ‖(Fin.cons v w' : Fin (i + 1) → Euc d) l‖ with hPw
      have hPw0 : 0 ≤ Pw := Finset.prod_nonneg fun l _ => norm_nonneg _
      -- mean value bound on the good set
      have hmv : ∀ t, (ContDiff ℝ (K : WithTop ℕ∞) (G t) ∧ 0 ≤ g t ∧
          ∀ i, 1 ≤ i → i ≤ K → ∀ x, ‖iteratedFDeriv ℝ i (G t) x‖ ≤ g t) →
          ∀ h : ℝ, |iteratedFDeriv ℝ i (G t) (x + h • v) w' -
            iteratedFDeriv ℝ i (G t) x w'| ≤ g t * Pw * |h| := by
        intro t ht h
        set lam : ℝ → ℝ := fun h => iteratedFDeriv ℝ i (G t) (x + h • v) w' with hlam
        have hd : ∀ h' : ℝ, HasDerivAt lam
            (iteratedFDeriv ℝ (i + 1) (G t) (x + h' • v) (Fin.cons v w')) h' :=
          fun h' => s67_iter_hasDeriv_at ht.1 hi x v w' h'
        have hbound : ∀ h' : ℝ, ‖deriv lam h'‖ ≤ g t * Pw := by
          intro h'
          rw [(hd h').deriv]
          refine ((iteratedFDeriv ℝ (i + 1) (G t) (x + h' • v)).le_opNorm _).trans ?_
          exact mul_le_mul_of_nonneg_right (ht.2.2 (i + 1) (Nat.succ_pos _) hi _) hPw0
        have := Convex.norm_image_sub_le_of_norm_deriv_le (f := lam) (s := Set.univ)
          (fun h' _ => (hd h').differentiableAt) (fun h' _ => hbound h') convex_univ
          (Set.mem_univ 0) (Set.mem_univ h)
        simp only [hlam, zero_smul, add_zero, Real.norm_eq_abs, sub_zero] at this
        exact this
      set Fh : ℝ → ℝ → ℝ := fun h t => h⁻¹ * (iteratedFDeriv ℝ i (G t) (x + h • v) w' -
        iteratedFDeriv ℝ i (G t) x w') with hFh
      have hFint : ∀ h : ℝ, IntegrableOn (Fh h) (Icc (0 : ℝ) τ) volume := by
        intro h
        exact ((ih hiK (x + h • v) w').1.sub (ih hiK x w').1).const_mul h⁻¹
      have hslope : ∀ h : ℝ, h⁻¹ * (iteratedFDeriv ℝ i Φ (x + h • v) w' -
          iteratedFDeriv ℝ i Φ x w') = ∫ t in Icc (0 : ℝ) τ, Fh h t := by
        intro h
        rw [(ih hiK (x + h • v) w').2, (ih hiK x w').2, ← integral_sub
          (ih hiK (x + h • v) w').1 (ih hiK x w').1, ← integral_const_mul]
      have hlimF : ∀ t, ContDiff ℝ (K : WithTop ℕ∞) (G t) → Tendsto (fun h => Fh h t) (𝓝[≠] 0)
          (𝓝 (iteratedFDeriv ℝ (i + 1) (G t) x (Fin.cons v w'))) := by
        intro t ht
        have := (s67_iter_hasDeriv ht hi x v w')
        have h2 := hasDerivAt_iff_tendsto_slope_zero.1 this
        refine h2.congr (fun h => ?_)
        simp [hFh]
      have hlimΦ : Tendsto (fun h : ℝ => h⁻¹ * (iteratedFDeriv ℝ i Φ (x + h • v) w' -
          iteratedFDeriv ℝ i Φ x w')) (𝓝[≠] 0)
          (𝓝 (iteratedFDeriv ℝ (i + 1) Φ x (Fin.cons v w'))) := by
        have := hasDerivAt_iff_tendsto_slope_zero.1 (s67_iter_hasDeriv hΦK hi x v w')
        refine this.congr (fun h => ?_)
        simp
      have hgv : IntegrableOn (fun t => g t * Pw) (Icc (0 : ℝ) τ) volume := hgI.mul_const Pw
      have hDCT : Tendsto (fun h : ℝ => ∫ t in Icc (0 : ℝ) τ, Fh h t) (𝓝[≠] 0)
          (𝓝 (∫ t in Icc (0 : ℝ) τ, iteratedFDeriv ℝ (i + 1) (G t) x (Fin.cons v w'))) := by
        refine tendsto_integral_filter_of_dominated_convergence
          (μ := volume.restrict (Icc (0 : ℝ) τ)) (fun t => g t * Pw) ?_ ?_ hgv ?_
        · exact Eventually.of_forall fun h => (hFint h).aestronglyMeasurable
        · refine Eventually.of_forall fun h => ?_
          filter_upwards [hae] with t ht
          by_cases hh : h = 0
          · have hgn : 0 ≤ g t := ht.2.1
            subst hh; simp [hFh]; exact mul_nonneg hgn hPw0
          · have := hmv t ht h
            simp only [hFh, Real.norm_eq_abs, abs_mul, abs_inv]
            rw [inv_mul_le_iff₀ (abs_pos.2 hh)]
            calc _ ≤ g t * Pw * |h| := this
              _ = |h| * (g t * Pw) := by ring
              _ = _ := by ring
        · filter_upwards [hae] with t ht
          exact hlimF t ht.1
      haveI : (𝓝[≠] (0 : ℝ)).NeBot := inferInstance
      have hEq : iteratedFDeriv ℝ (i + 1) Φ x (Fin.cons v w') =
          ∫ t in Icc (0 : ℝ) τ, iteratedFDeriv ℝ (i + 1) (G t) x (Fin.cons v w') := by
        refine tendsto_nhds_unique hlimΦ ?_
        refine hDCT.congr (fun h => ?_)
        exact (hslope h).symm
      refine ⟨?_, hEq⟩
      have hmeas : AEStronglyMeasurable (fun t => iteratedFDeriv ℝ (i + 1) (G t) x (Fin.cons v w'))
          (volume.restrict (Icc (0 : ℝ) τ)) := by
        refine aestronglyMeasurable_of_tendsto_ae (u := 𝓝[≠] (0 : ℝ)) (f := fun h t => Fh h t) ?_ ?_
        · exact fun h => (hFint h).aestronglyMeasurable
        · filter_upwards [hae] with t ht
          exact hlimF t ht.1
      refine Integrable.mono' hgv hmeas ?_
      filter_upwards [hae] with t ht
      rw [Real.norm_eq_abs]
      refine ((iteratedFDeriv ℝ (i + 1) (G t) x).le_opNorm _).trans ?_
      exact mul_le_mul_of_nonneg_right (ht.2.2 (i + 1) (Nat.succ_pos _) hi x) hPw0
  refine ⟨key, fun i hi1 hiK x => ?_⟩
  have hg0 : 0 ≤ ∫ t in Icc (0 : ℝ) τ, g t :=
    integral_nonneg_of_ae (by filter_upwards [hae] with t ht using ht.2.1)
  refine ContinuousMultilinearMap.opNorm_le_bound hg0 fun w => ?_
  rw [(key i hiK x w).2]
  have hwn : IntegrableOn (fun t => g t * ∏ l, ‖w l‖) (Icc (0 : ℝ) τ) volume :=
    hgI.mul_const _
  refine (norm_integral_le_of_norm_le hwn ?_).trans ?_
  · filter_upwards [hae] with t ht
    exact ((iteratedFDeriv ℝ i (G t) x).le_opNorm w).trans
      (mul_le_mul_of_nonneg_right (ht.2.2 i hi1 hiK x) (Finset.prod_nonneg fun l _ => norm_nonneg _))
  · rw [integral_mul_const]

end HRS.MS.BreakdownS67
