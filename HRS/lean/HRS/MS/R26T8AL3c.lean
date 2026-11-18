import HRS.MS.R26T8AL3b
import HRS.MS.R26T8AF05d

/-!
# S8.2 observed-time layer, generic lemma L3c: Leibniz formula for the directional iterates of a product

`(∂_i)^[j] (c · v) = fun x => ∑_{k ≤ j} C(j,k) · ((∂_i)^[k] c x) · ((∂_i)^[j-k] v x)` for `c, v` smooth.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ContDiff FourierTransform ComplexConjugate
namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.PDE.ToolboxRd HRS.PDE.ToolboxRd.FourierAux

variable {d : ℕ}

theorem r26t8a_l3_D_sum_fun {ι : Type*} (i : Fin d) (s : Finset ι) (F : ι → Euc d → ℝ)
    (hF : ∀ k ∈ s, Differentiable ℝ (F k)) :
    r26t8a_l3_D i (fun x => ∑ k ∈ s, F k x) = fun x => ∑ k ∈ s, r26t8a_l3_D i (F k) x := by
  funext x
  unfold r26t8a_l3_D
  have hfun : (fun y => ∑ k ∈ s, F k y) = ∑ k ∈ s, F k := by
    funext y
    simp [Finset.sum_apply]
  rw [hfun, fderiv_sum (fun k hk => hF k hk x), ContinuousLinearMap.sum_apply]

theorem r26t8a_l3_D_const (i : Fin d) (c : ℝ) (g : Euc d → ℝ) (hg : Differentiable ℝ g) (x : Euc d) :
    r26t8a_l3_D i (fun y => c * g y) x = c * r26t8a_l3_D i g x := by
  unfold r26t8a_l3_D
  rw [fderiv_const_mul (hg x) c]
  simp

theorem r26t8a_l3_D_mul (i : Fin d) (a b : Euc d → ℝ) (ha : Differentiable ℝ a)
    (hb : Differentiable ℝ b) (x : Euc d) :
    r26t8a_l3_D i (fun y => a y * b y) x = a x * r26t8a_l3_D i b x + b x * r26t8a_l3_D i a x := by
  unfold r26t8a_l3_D
  exact r26t8a_f05d_prod_apply a b x _ (ha x) (hb x)

theorem r26t8a_l3_leibniz (i : Fin d) (c v : Euc d → ℝ) (hc : ContDiff ℝ ∞ c)
    (hv : ContDiff ℝ ∞ v) (j : ℕ) :
    (r26t8a_l3_D i)^[j] (fun x => c x * v x) =
      fun x => ∑ k ∈ Finset.range (j + 1),
        (j.choose k : ℝ) * ((r26t8a_l3_D i)^[k] c x * (r26t8a_l3_D i)^[j - k] v x) := by
  induction j with
  | zero =>
    funext x
    simp
  | succ j ih =>
    rw [Function.iterate_succ_apply', ih]
    have hdiff : ∀ k, Differentiable ℝ (fun x => (r26t8a_l3_D i)^[k] c x) := fun k =>
      ((r26t8a_l3_contDiff_iter i c hc k).differentiable (by simp))
    have hdiffv : ∀ k, Differentiable ℝ (fun x => (r26t8a_l3_D i)^[k] v x) := fun k =>
      ((r26t8a_l3_contDiff_iter i v hv k).differentiable (by simp))
    have hterm : ∀ k ∈ Finset.range (j + 1), Differentiable ℝ
        (fun x => (j.choose k : ℝ) * ((r26t8a_l3_D i)^[k] c x * (r26t8a_l3_D i)^[j - k] v x)) :=
      fun k _ => (hdiff k).mul (hdiffv (j - k)) |>.const_mul _
    rw [r26t8a_l3_D_sum_fun i _ _ hterm]
    funext x
    have step : ∀ k ∈ Finset.range (j + 1),
        r26t8a_l3_D i (fun y => (j.choose k : ℝ) * ((r26t8a_l3_D i)^[k] c y * (r26t8a_l3_D i)^[j - k] v y)) x =
          (j.choose k : ℝ) * ((r26t8a_l3_D i)^[k] c x * (r26t8a_l3_D i)^[j - k + 1] v x +
            (r26t8a_l3_D i)^[j - k] v x * (r26t8a_l3_D i)^[k + 1] c x) := by
      intro k _
      have hp : Differentiable ℝ (fun y => (r26t8a_l3_D i)^[k] c y * (r26t8a_l3_D i)^[j - k] v y) :=
        (hdiff k).mul (hdiffv (j - k))
      rw [r26t8a_l3_D_const i _ _ hp x,
        r26t8a_l3_D_mul i _ _ (hdiff k) (hdiffv (j - k)) x]
      rw [Function.iterate_succ_apply' (r26t8a_l3_D i) (j - k) v,
        Function.iterate_succ_apply' (r26t8a_l3_D i) k c]
    rw [Finset.sum_congr rfl step]
    have hp := r26t8a_l3_pascal (fun k => (r26t8a_l3_D i)^[k] c x)
      (fun l => (r26t8a_l3_D i)^[l] v x) j
    have hq : ∀ k ∈ Finset.range (j + 1),
        (j.choose k : ℝ) * ((r26t8a_l3_D i)^[k] c x * (r26t8a_l3_D i)^[j - k + 1] v x +
            (r26t8a_l3_D i)^[j - k] v x * (r26t8a_l3_D i)^[k + 1] c x) =
        (j.choose k : ℝ) * ((r26t8a_l3_D i)^[k + 1] c x * (r26t8a_l3_D i)^[j - k] v x +
            (r26t8a_l3_D i)^[k] c x * (r26t8a_l3_D i)^[j - k + 1] v x) := fun k _ => by ring
    rw [Finset.sum_congr rfl hq]
    exact hp

end HRS.MS.R26T8A

end
