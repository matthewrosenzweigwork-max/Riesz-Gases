import HRS.MS.Fp81S21ResponseWindow3
import HRS.MS.Fp81S21InitialWindow2
import HRS.MS.S21E_Kappa0

/-!
# S2.1(iii) packet 3: the initial cubic tensor `initialKappa`

Instantiates the generic kappa0 theorems of `S21E_Kappa0` for
`initialKappa R b = E[v ⊗ v ⊗ v]` with `v = responseWindow R b`, using the
cubic integrability and the everywhere coordinate identity of the response
window producers.  The radius is the minimum of the two producer radii.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S21E

/-- The coordinate functional `u ↦ u(α)` on the dual `OscDual d m`, as a
continuous linear map. -/
def fp81s21_oscCoordCLM (d : ℕ) (m : ℝ) (α : MultiIndex d) : OscDual d m →L[ℝ] ℝ :=
  lp.evalCLM ℝ (fun _ : MultiIndex d => ℝ) 2 α

/-- The coordinate functional `w ↦ coord (w(t)) α` on the window `Window p`,
as a continuous linear map. -/
def fp81s21_windowCoordCLM (p : Parameters) (t : Icc (0 : ℝ) p.T) (α : MultiIndex p.d) :
    Window p →L[ℝ] ℝ :=
  (fp81s21_oscCoordCLM p.d (wholeSpaceIndex p.d : ℝ) α).comp (ContinuousMap.evalCLM ℝ t)

theorem fp81s21_windowCoordCLM_apply (p : Parameters) (t : Icc (0 : ℝ) p.T)
    (α : MultiIndex p.d) (w : Window p) :
    fp81s21_windowCoordCLM p t α w = OscDual.coord (OscPath.at' w t) α :=
  rfl

/-- Packet 3: the initial cubic tensor `initialKappa R b` is a projective
tensor, symmetric, has norm bounded by the cubic path integral, is determined
by its values on products of continuous linear functionals, and on products of
oscillator coordinates at three window times it equals the integral of the
product of the response coordinates.  Each radius is taken before `δ` and `R`.
The probability instance is the one required by `initialKappa` itself. -/
theorem fp81s21_initialKappa_props (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, 0 < p.γ → ∀ b : ℝ, 0 ≤ b →
        ∀ [IsProbabilityMeasure (r26t3_mu R 0)],
          initialKappa R b ∈ projTensor (Window p) 3 ∧
          (∀ σ : Equiv.Perm (Fin 3), ∀ M : (Window p) [×3]→L[ℝ] ℝ,
            initialKappa R b (M.domDomCongr σ) = initialKappa R b M) ∧
          ‖initialKappa R b‖ ≤
            ∫ x, ‖responseWindow R b x‖ * ‖responseWindow R b x‖ * ‖responseWindow R b x‖
              ∂(r26t3_mu R 0) ∧
          (∀ ℓ : Fin 3 → (Window p →L[ℝ] ℝ),
            initialKappa R b (HRS.MC.E213U18.trilin ℓ) =
              ∫ x, ℓ 0 (responseWindow R b x) * ℓ 1 (responseWindow R b x) *
                ℓ 2 (responseWindow R b x) ∂(r26t3_mu R 0)) ∧
          (∀ (α : Fin 3 → MultiIndex p.d) (t : Fin 3 → ℝ) (ht : ∀ i, t i ∈ Icc (0 : ℝ) p.T),
            initialKappa R b
                (HRS.MC.E213U18.trilin (fun i => fp81s21_windowCoordCLM p ⟨t i, ht i⟩ (α i))) =
              ∫ x, ∏ i : Fin 3,
                r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + t i)
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) (α i))) x
                ∂(r26t3_mu R 0)) := by
  classical
  obtain ⟨δc, hc0, hcHalf, hcube⟩ := fp81s21_responseWindow_cubic_integrable p
  obtain ⟨δg, hg0, hgHalf, hgen⟩ := fp81s21_responseWindow_genuine p
  refine ⟨min δc δg, lt_min hc0 hg0, (min_le_left _ _).trans hcHalf,
    fun δ hδ hδle R hγ b hb => ?_⟩
  have hδc : δ ≤ δc := hδle.trans (min_le_left _ _)
  have hδg : δ ≤ δg := hδle.trans (min_le_right _ _)
  intro _hprob
  obtain ⟨hmeas, hcubeInt⟩ := hcube δ hδ hδc R hγ b hb
  have hi : Integrable
      (fun x : Euc p.d => ‖responseWindow R b x‖ * ‖responseWindow R b x‖ *
        ‖responseWindow R b x‖) (r26t3_mu R 0) :=
    hcubeInt.congr (Filter.Eventually.of_forall fun x =>
      (by ring : ‖responseWindow R b x‖ ^ 3 =
        ‖responseWindow R b x‖ * ‖responseWindow R b x‖ * ‖responseWindow R b x‖))
  have hcoord : ∀ (x : Euc p.d) (s : ℝ) (hs : s ∈ Icc (0 : ℝ) p.T) (β : MultiIndex p.d),
      fp81s21_windowCoordCLM p ⟨s, hs⟩ β (responseWindow R b x) =
        r26t3_a R (propagatorW (r26t3_coeff R) 0 (b + s)
          (oscTestFun (wholeSpaceIndex p.d : ℝ) β)) x := by
    intro x s hs β
    obtain ⟨-, -, hc⟩ := hgen δ hδ hδg R hγ b hb x
    exact hc ⟨s, hs⟩ β
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact HRS.MS.S21E.s21e_kappa0_mem (r26t3_mu R 0) hmeas hi
  · intro σ M
    exact HRS.MS.S21E.s21e_kappa0_symm (r26t3_mu R 0) hmeas hi σ M
  · exact HRS.MS.S21E.s21e_kappa0_norm_le (r26t3_mu R 0) hmeas hi
  · intro ℓ
    exact HRS.MS.S21E.s21e_kappa0_trilin (r26t3_mu R 0) hmeas hi ℓ
  · intro α t ht
    refine (HRS.MS.S21E.s21e_kappa0_trilin (r26t3_mu R 0) hmeas hi
      (fun i => fp81s21_windowCoordCLM p ⟨t i, ht i⟩ (α i))).trans ?_
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [Fin.prod_univ_three]
    rw [hcoord x (t 0) (ht 0) (α 0), hcoord x (t 1) (ht 1) (α 1),
      hcoord x (t 2) (ht 2) (α 2)]

#print axioms HRS.Fp81.S21.fp81s21_initialKappa_props

end HRS.Fp81.S21

end
