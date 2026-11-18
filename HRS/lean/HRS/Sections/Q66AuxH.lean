import HRS.Sections.Q66AuxG
import HRS.Equilibrium.Q84dAuxP
import HRS.Equilibrium.Q84dAuxF

/-!
# Packet Q66: Stein identity under `Q_{N,β}(μ)`, part 1 (calculus along coordinate lines)

`q66_H_line_deriv`: the derivative of the Hamiltonian `∑ V(x_a) + N⁻¹ ∑_{a<b} g(x_a - x_b)` along a
coordinate line, for `C¹` one-body potentials `V` and `0 ≤ s < d` (a copy of `q84d_H_line_deriv`,
which is stated for `s = d/2` and smooth `V`).  `q66_line_ibp`: the line integration by parts in a
form where only the derivative at non-colliding configurations is required.
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.Q66

open HRS.Q84d

variable {d : ℕ} {s : ℝ} {N : ℕ}

theorem q66_H_line_deriv (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {V : Torus d → ℝ}
    (hV : Torus.IsCk 1 V) (Y : Config d N) (hY : ∀ a b : Fin N, a ≠ b → Y a ≠ Y b)
    (i : Fin N) (k : Fin d) :
    HasDerivAt (fun τ : ℝ => canonicalHamiltonian (periodicRiesz d s) V (lineCfg i k Y τ))
      (Bik d s V i k Y) 0 := by
  have hfun : (fun τ : ℝ => canonicalHamiltonian (periodicRiesz d s) V (lineCfg i k Y τ)) =
      fun τ => (∑ a, V ((lineCfg i k Y τ) a)) +
        (1 / (N : ℝ)) * ∑ p ∈ pairsN N, periodicRiesz d s
          ((lineCfg i k Y τ) p.1 - (lineCfg i k Y τ) p.2) := by
    funext τ; exact q84d_H_eq _ _ _
  rw [hfun]
  -- the potential part
  have hVd : DifferentiableAt ℝ (fun u : Euc d => V (Y i + Torus.mk u)) 0 := by
    rw [q84d_slice_eq]
    have hc : ContDiff ℝ 1 (Torus.lift V) := hV
    exact ((hc.differentiable one_ne_zero) _).comp 0 (differentiableAt_id.const_add _)
  have hVline : HasDerivAt (fun τ : ℝ => V ((lineCfg i k Y τ) i)) ((Torus.grad V (Y i)) k) 0 := by
    have h1 : HasDerivAt (fun τ : ℝ => τ • ek k) (ek k) 0 := by
      simpa using (hasDerivAt_id (0 : ℝ)).smul_const (ek k)
    have hF0 : HasFDerivAt (fun u : Euc d => V (Y i + Torus.mk u))
        (fderiv ℝ (fun u : Euc d => V (Y i + Torus.mk u)) 0) ((fun τ : ℝ => τ • ek k) 0) := by
      simpa using hVd.hasFDerivAt
    have h2 := hF0.comp_hasDerivAt (0 : ℝ) h1
    have e : (fun τ : ℝ => V ((lineCfg i k Y τ) i)) =
        (fun u : Euc d => V (Y i + Torus.mk u)) ∘ fun τ : ℝ => τ • ek k := by
      funext τ; simp [lineCfg]
    rw [e]
    convert h2 using 1
    rw [q84d_slice_grad_comp]
  have hVsum : HasDerivAt (fun τ : ℝ => ∑ a, V ((lineCfg i k Y τ) a))
      ((Torus.grad V (Y i)) k) 0 := by
    have : HasDerivAt (fun τ : ℝ => ∑ a, V ((lineCfg i k Y τ) a))
        (∑ a : Fin N, (if a = i then (Torus.grad V (Y i)) k else 0)) 0 := by
      refine HasDerivAt.fun_sum (fun a _ => ?_)
      by_cases h : a = i
      · subst h; simpa using hVline
      · simp only [h, ite_false]
        have : (fun τ : ℝ => V ((lineCfg i k Y τ) a)) = fun _ => V (Y a) := by
          funext τ; simp [lineCfg, Function.update_of_ne h]
        rw [this]; exact hasDerivAt_const _ _
    simpa using this
  -- the interaction part
  have hpair : ∀ p ∈ pairsN N, HasDerivAt (fun τ : ℝ => periodicRiesz d s
      ((lineCfg i k Y τ) p.1 - (lineCfg i k Y τ) p.2))
      ((((if p.1 = i then (1 : ℝ) else 0) - (if p.2 = i then 1 else 0)) *
        (periodicRieszGrad d s (Y p.1 - Y p.2)) k)) 0 := by
    intro p hp
    have hlt : p.1 < p.2 := by simpa [pairsN] using hp
    have hz : Y p.1 - Y p.2 ≠ 0 := sub_ne_zero.2 (hY _ _ hlt.ne)
    have := q84d_g_line_deriv hd hs0 hsd hz k
      ((if p.1 = i then (1 : ℝ) else 0) - (if p.2 = i then 1 else 0))
    have e : (fun τ : ℝ => periodicRiesz d s ((lineCfg i k Y τ) p.1 - (lineCfg i k Y τ) p.2)) =
        fun τ => periodicRiesz d s ((Y p.1 - Y p.2) + Torus.mk
          ((((if p.1 = i then (1 : ℝ) else 0) - (if p.2 = i then 1 else 0)) * τ) • ek k)) := by
      funext τ; rw [q84d_line_diff]
    rw [e]; exact this
  have hsum := HasDerivAt.fun_sum hpair
  have hid := q84d_pair_sum_identity (fun z => (periodicRieszGrad d s z) k)
    (fun z => by simp [HRS.KernelGrad.periodicRieszGrad_neg_of_lt hsd]) Y i
  have h3 := (hVsum.add (hsum.const_mul (1 / (N : ℝ))))
  convert h3 using 1
  unfold Bik
  rw [← hid]

/-- Line integration by parts: it suffices to know the derivative at non-colliding configurations. -/
theorem q66_line_ibp (hd : 2 ≤ d) (i : Fin N) (k : Fin d) {w D : Config d N → ℝ}
    (hDm : Measurable D) (hDi : Integrable D (volume : Measure (Config d N)))
    (hbase : ∀ Y : Config d N, (∀ a b : Fin N, a ≠ b → Y a ≠ Y b) →
      HasDerivAt (fun τ : ℝ => w (lineCfg i k Y τ)) (D Y) 0) :
    ∫ X, D X = 0 := by
  refine q84d_ibp i k (w := w) hDm hDi ?_
  filter_upwards [q84d_ae_line_free hd i k] with Y hY t
  have hfree : ∀ a b : Fin N, a ≠ b → (lineCfg i k Y t) a ≠ (lineCfg i k Y t) b := by
    intro a b hab hX
    exact hY t ⟨a, b, hab, hX⟩
  have h0 := hbase (lineCfg i k Y t) hfree
  have e : (fun τ : ℝ => w (lineCfg i k (lineCfg i k Y t) τ)) =
      fun τ => w (lineCfg i k Y (t + τ)) := by
    funext τ; rw [lineCfg_add]
  rw [e] at h0
  have h1 : HasDerivAt (fun σ : ℝ => w (lineCfg i k Y (t + σ))) (D (lineCfg i k Y t)) (t - t) := by
    rw [sub_self]; exact h0
  have h2 := h1.comp_sub_const t t
  have e2 : (fun x : ℝ => w (lineCfg i k Y (t + (x - t)))) = fun x => w (lineCfg i k Y x) := by
    funext x; rw [add_sub_cancel]
  rw [e2] at h2
  exact h2

end HRS.Q66

end
