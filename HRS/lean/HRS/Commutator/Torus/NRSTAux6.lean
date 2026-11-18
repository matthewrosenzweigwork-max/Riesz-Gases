import HRS.Commutator.Torus.NRSTAux5

/-!
# NRS-T, part 6: the commutator of trigonometric polynomials equals `2 Re pr A (v·∇(g*A))`
-/

noncomputable section

open MeasureTheory
open scoped BigOperators ComplexConjugate

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ} {s : ℝ}

/-- The vector field with components `Re ev V_j`. -/
def vOf (V : Fin d → TPA d) (x : Torus d) : Euc d := WithLp.toLp 2 fun j => (ev (V j) x).re

/-- The real function `Re ev A`. -/
def aOf (A : TPA d) (x : Torus d) : ℝ := (ev A x).re

lemma ev_re_cast (f : TPA d) (hr : ∀ x, (ev f x).im = 0) (x : Torus d) :
    (((ev f x).re : ℝ) : ℂ) = ev f x :=
  Complex.ext (by simp) (by simp [hr x])

lemma contDiff_ev_lift (f : TPA d) (n : WithTop ℕ∞) :
    ContDiff ℝ n (fun y : Euc d => ev f (Torus.mk y)) := by
  have e : (fun y : Euc d => ev f (Torus.mk y)) = fun y : Euc d =>
      ∑ k ∈ f.coeff.support, f.coeff k *
        Complex.exp (((2 * Real.pi * Lattice.dot k y : ℝ) : ℂ) * Complex.I) := by
    funext y
    rw [ev_apply_sum]
    exact Finset.sum_congr rfl fun k _ => by rw [Torus.mode_mk]
  rw [e]
  refine ContDiff.sum fun k _ => contDiff_const.mul ?_
  refine Complex.contDiff_exp.comp ?_
  have hdot : ContDiff ℝ n (fun y : Euc d => Lattice.dot k y) := by
    have : (fun y : Euc d => Lattice.dot k y) = fun y : Euc d => inner ℝ (Lattice.toEuc k) y :=
      funext fun y => Torus.dot_eq_inner k y
    rw [this]
    exact contDiff_const.inner ℝ contDiff_id
  exact (Complex.ofRealCLM.contDiff.comp (contDiff_const.mul hdot)).mul contDiff_const

lemma isCk_aOf (A : TPA d) (n : WithTop ℕ∞) : Torus.IsCk n (aOf A) := by
  unfold Torus.IsCk Torus.lift aOf
  exact Complex.reCLM.contDiff.comp (contDiff_ev_lift A n)

lemma exists_box (S : Finset (Lattice d)) : ∃ n : ℕ, ∀ k ∈ S, KernelGrad.InBox n k := by
  refine ⟨∑ k ∈ S, ∑ i, (k i).natAbs, fun k hk i => ?_⟩
  have h1 : (k i).natAbs ≤ ∑ i, (k i).natAbs :=
    Finset.single_le_sum (f := fun i => (k i).natAbs) (fun _ _ => Nat.zero_le _) (Finset.mem_univ i)
  have h2 : ∑ i, (k i).natAbs ≤ ∑ k ∈ S, ∑ i, (k i).natAbs :=
    Finset.single_le_sum (f := fun k => ∑ i, (k i).natAbs) (fun _ _ => Nat.zero_le _) hk
  have := h1.trans h2
  have h3 : |k i| = ((k i).natAbs : ℤ) := Int.abs_eq_natAbs _
  rw [h3]
  exact_mod_cast this

lemma coeffOf_re_ev (f : TPA d) (hr : ∀ x, (ev f x).im = 0) (k : Lattice d) :
    KernelGrad.coeffOf (fun x => (ev f x).re) k = f.coeff k := by
  rw [KernelGrad.coeffOf_eq_integral]
  simp_rw [ev_re_cast f hr]
  exact ev_coeff f k

lemma isTrigPoly_aOf (A : TPA d) (hAr : ∀ x, (ev A x).im = 0) :
    ∃ n : ℕ, KernelGrad.IsTrigPoly n (KernelGrad.coeffOf (aOf A)) := by
  obtain ⟨n, hn⟩ := exists_box A.coeff.support
  refine ⟨n, fun k hk => hn k ?_⟩
  unfold aOf at hk
  rw [coeffOf_re_ev A hAr] at hk
  simpa using hk

lemma ev_mul_real (f g : TPA d) (hf : ∀ x, (ev f x).im = 0) (hg : ∀ x, (ev g x).im = 0) (x : Torus d) :
    (ev (f * g) x).im = 0 := by
  rw [ev_mul, Pi.mul_apply, Complex.mul_im, hf, hg]; ring

lemma conj_coeff_of_real (A : TPA d) (hAr : ∀ x, (ev A x).im = 0) (k : Lattice d) :
    (starRingEnd ℂ) (A.coeff k) = A.coeff (-k) := by
  rw [← ev_coeff A k, ← ev_coeff A (-k), neg_neg, ← integral_conj]
  refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
  simp only [map_mul, Torus.mode_neg]
  have : (starRingEnd ℂ) (ev A x) = ev A x := by
    rw [← ev_re_cast A hAr x]; exact Complex.conj_ofReal _
  rw [this, Complex.conj_conj]

end HRS.Commutator.TorusNote.NRST
