import HRS.Uniform.Q54Aux14
import HRS.Uniform.Q54Aux15

/-!
# Q54, part 16: the dual evolution on `E_r` from a function-level family

`EvoCore J Up`: a family `Up u t` (`0 ≤ u ≤ t`) of maps on functions which preserves `Dom J`, is linear on `Dom J`,
preserves constants, is the identity on the diagonal and satisfies the cocycle law `U^{s,t} = U^{s,r} U^{r,t}` on `Dom J`.
`exists_evol`: if moreover `Up` is quasi-contractive in `H^r` then there is a bounded dual evolution on `E_r`:
`⟨V^{t,u} z, φ⟩ = ⟨z, U^{u,t} φ⟩` for `φ ∈ Dom J`, `V^{t,t} = 1`, the cocycle law, and `‖V^{t,u}‖ ≤ e^{C(t-u)}`.
-/

noncomputable section

open MeasureTheory Filter Topology Finset
open scoped ENNReal NNReal BigOperators

namespace HRS.Uniform.Q54

open HRS HRS.PDE HRS.Uniform.Q48b

variable {d : ℕ}

/-- a function-level evolution family. -/
structure EvoCore (J : ℕ) (Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ) : Prop where
  dom : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ φ, Dom J φ → Dom J (Up u t φ)
  lin : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ φ ψ, Dom J φ → Dom J ψ → ∀ α β : ℝ,
    Up u t (fun x => α * φ x + β * ψ x) = fun x => α * Up u t φ x + β * Up u t ψ x
  const : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ c : ℝ, Up u t (fun _ => c) = fun _ => c
  self : ∀ t : ℝ, 0 ≤ t → ∀ φ, Up t t φ = φ
  cocycle : ∀ s r t : ℝ, 0 ≤ s → s ≤ r → r ≤ t → ∀ φ, Dom J φ → Up s t φ = Up s r (Up r t φ)

/-- quasi-contractivity at level `a`. -/
def QuasiAt (J : ℕ) (Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ) (a C : ℝ) : Prop :=
  ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ φ, Dom J φ →
    MemSobolev a (Up u t φ) ∧ sobolevNorm a (Up u t φ) ≤ Real.exp (C * (t - u)) * sobolevNorm a φ

/-- `eval` is linear in the test function (for functions of the level of `z`). -/
theorem eval_sub_fun {r : ℝ} (z : NegSobolev d r) {f g : Torus d → ℝ}
    (hfg : MemSobolev r (fun x => f x - g x)) (hf : MemSobolev r f) (hg : MemSobolev r g) :
    NegSobolev.eval z (fun x => f x - g x) = NegSobolev.eval z f - NegSobolev.eval z g := by
  rw [eval_eq_inner r z hfg, eval_eq_inner r z hf, eval_eq_inner r z hg, ← inner_sub_right]
  congr 1
  show (lpOf r hfg : lp (fun _ : NonzeroLattice d => ℝ) 2) =
    (lpOf r hf : lp (fun _ : NonzeroLattice d => ℝ) 2) - (lpOf r hg : lp (fun _ : NonzeroLattice d => ℝ) 2)
  refine lp.ext (funext fun k => ?_)
  show wseqF r (fun x => f x - g x) k = wseqF r f k - wseqF r g k
  simp only [wseqF]
  rw [funRealCoeff_sub' hf.1 hg.1 k]
  ring

theorem dom_sub {J : ℕ} {φ ψ : Torus d → ℝ} (hφ : Dom J φ) (hψ : Dom J ψ) :
    Dom J (fun x => φ x - ψ x) := by
  have := dom_closed hφ hψ 1 (-1)
  convert this using 2 with x
  ring

theorem memSobolev_of_dom {J : ℕ} {a : ℝ} (ha : a ≤ J) {φ : Torus d → ℝ} (hφ : Dom J φ) :
    MemSobolev a φ :=
  MFAdjoint.memSobolev_mono_idx (m := (J : ℝ)) hφ.2 ha

theorem exists_evol (J : ℕ) (Up : ℝ → ℝ → (Torus d → ℝ) → Torus d → ℝ) (hc : EvoCore J Up)
    (r C : ℝ) (hr : r ≤ J) (hq : QuasiAt J Up r C) :
    ∃ Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r,
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ (z : NegSobolev d r) (φ : Torus d → ℝ), Dom J φ →
        NegSobolev.eval (Vev t u z) φ = NegSobolev.eval z (Up u t φ)) ∧
      (∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp (C * (t - u))) ∧
      (∀ t : ℝ, 0 ≤ t → Vev t t = 1) ∧
      (∀ s r' t : ℝ, 0 ≤ s → s ≤ r' → r' ≤ t → (Vev t r').comp (Vev r' s) = Vev t s) := by
  classical
  have hdh : ∀ u t : ℝ, 0 ≤ u → u ≤ t → DualHyp (Dom J) r (Up u t) (Real.exp (C * (t - u))) := by
    intro u t hu hut
    exact ⟨(Real.exp_pos _).le, fun φ hφ => dom_smooth hφ, fun φ hφ => memSobolev_of_dom hr hφ,
      fun φ ψ hφ hψ α β => dom_closed hφ hψ α β,
      fun φ ψ hφ hψ α β => hc.lin u t hu hut φ ψ hφ hψ α β, fun c' => hc.const u t hu hut c',
      fun φ hφ => hq u t hu hut φ hφ⟩
  have hex : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∃ V : NegSobolev d r →L[ℝ] NegSobolev d r,
      ‖V‖ ≤ Real.exp (C * (t - u)) ∧ ∀ (z : NegSobolev d r) (φ : Torus d → ℝ), Dom J φ →
        NegSobolev.eval (V z) φ = NegSobolev.eval z (Up u t φ) :=
    fun u t hu hut => exists_dual_op (hdh u t hu hut)
  let Vev : ℝ → ℝ → NegSobolev d r →L[ℝ] NegSobolev d r := fun t u =>
    if h : 0 ≤ u ∧ u ≤ t then (hex u t h.1 h.2).choose else 0
  have hV : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ‖Vev t u‖ ≤ Real.exp (C * (t - u)) ∧
      ∀ (z : NegSobolev d r) (φ : Torus d → ℝ), Dom J φ →
        NegSobolev.eval (Vev t u z) φ = NegSobolev.eval z (Up u t φ) := by
    intro u t hu hut
    have h : 0 ≤ u ∧ u ≤ t := ⟨hu, hut⟩
    have e : Vev t u = (hex u t hu hut).choose := dif_pos h
    rw [e]
    exact (hex u t hu hut).choose_spec
  have hdual : ∀ u t : ℝ, 0 ≤ u → u ≤ t → ∀ (z : NegSobolev d r) (φ : Torus d → ℝ), Dom J φ →
      NegSobolev.eval (Vev t u z) φ = NegSobolev.eval z (Up u t φ) :=
    fun u t hu hut => (hV u t hu hut).2
  refine ⟨Vev, hdual, fun u t hu hut => (hV u t hu hut).1, fun t ht => ?_, fun s r' t hs hsr hrt => ?_⟩
  · refine ContinuousLinearMap.ext fun z => eq_of_eval_smooth fun φ hφ => ?_
    rw [hdual t t ht le_rfl z φ (dom_smooth hφ), hc.self t ht φ]
    rfl
  · refine ContinuousLinearMap.ext fun z => eq_of_eval_smooth fun φ hφ => ?_
    have hD := dom_smooth (J := J) hφ
    show NegSobolev.eval (Vev t r' (Vev r' s z)) φ = NegSobolev.eval (Vev t s z) φ
    rw [hdual r' t (hs.trans hsr) hrt _ φ hD, hdual s r' hs hsr z _ (hc.dom r' t (hs.trans hsr) hrt φ hD),
      hdual s t hs (hsr.trans hrt) z φ hD, hc.cocycle s r' t hs hsr hrt φ hD]

end HRS.Uniform.Q54
