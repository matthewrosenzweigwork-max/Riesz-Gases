import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie

/-!
# S6.7 nonlinear, packet S6.7nl.55: finite-difference PDE with the shifted OU commutator

Namespace `HRS.MS.BreakdownS67`, helper prefix `s67bd_`. TeX S:4844-4851 (finiteness
prerequisite), row `S:W:lem:r2mov-global-adjoint` (nonlinear part). Owned definitions:
`s67bd_ParabolicData`, `s67bd_diff`.
The single difference quotient commutes with iterated derivatives, gradient and Laplacian of a
`C^2` function; subtracting the two time-integral identities and the two equations gives the
difference PDE, the extra drift term being the shifted gradient paired with the coefficient
difference and the negative shifted OU commutator.
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

structure s67bd_ParabolicData (ν q T : ℝ) (u a : ℝ → Euc d → ℝ)
    (B : ℝ → Euc d → Euc d) (J : ℝ → Euc d → ℝ) : Prop where
  c2 : ∀ t ∈ Icc (0 : ℝ) T, ContDiff ℝ 2 (u t)
  bdd_c2 : ∃ K : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ k ≤ 2, ∀ x,
    ‖iteratedFDeriv ℝ k (u t) x‖ ≤ K
  cont_c2 : ∀ k ≤ 2, ContinuousOn
    (fun p : ℝ × Euc d => iteratedFDeriv ℝ k (u p.1) p.2)
    (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d)))
  acont : ContinuousOn (fun p : ℝ × Euc d => a p.1 p.2)
    (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d)))
  agrow : ∃ K : ℝ, ∀ t ∈ Icc (0 : ℝ) T, ∀ x, |a t x| ≤ K * (1 + ‖x‖)
  Bcont : ContinuousOn (fun p : ℝ × Euc d => B p.1 p.2)
    (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d)))
  Jcont : ContinuousOn (fun p : ℝ × Euc d => J p.1 p.2)
    (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d)))
  hint : ∀ t ∈ Icc (0 : ℝ) T, ∀ t0 ∈ Icc (0 : ℝ) T, ∀ x,
    u t x - u t0 x = ∫ v in t0..t, a v x
  equation : ∀ t ∈ Icc (0 : ℝ) T, ∀ x,
    a t x = ν * Laplacian.laplacian (u t) x +
      inner ℝ ((-q) • x + B t x) (gradient (u t) x) + J t x

def s67bd_diff {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (h : ℝ) (e : Euc d) (u : Euc d → F) (x : Euc d) : F :=
  h⁻¹ • (u (x + h • e) - u x)

section DiffCalculus

variable {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

lemma s67bd_diff_contDiff {n : WithTop ℕ∞} {f : Euc d → F} (hf : ContDiff ℝ n f)
    (h : ℝ) (e : Euc d) : ContDiff ℝ n (s67bd_diff h e f) := by
  unfold s67bd_diff
  exact ((hf.comp (contDiff_id.add contDiff_const)).sub hf).const_smul _

lemma s67bd_diff_iteratedFDeriv {f : Euc d → F} (hf : ContDiff ℝ 2 f) (h : ℝ) (e : Euc d)
    {k : ℕ} (hk : k ≤ 2) (x : Euc d) :
    iteratedFDeriv ℝ k (s67bd_diff h e f) x =
      h⁻¹ • (iteratedFDeriv ℝ k f (x + h • e) - iteratedFDeriv ℝ k f x) := by
  have hk' : ContDiff ℝ (k : WithTop ℕ∞) f := hf.of_le (by exact_mod_cast hk)
  have hs : ContDiff ℝ (k : WithTop ℕ∞) (fun y : Euc d => f (y + h • e)) :=
    hk'.comp (contDiff_id.add contDiff_const)
  unfold s67bd_diff
  rw [iteratedFDeriv_const_smul_apply' ((hs.sub hk').contDiffAt)]
  have hsub := iteratedFDeriv_sub_apply (𝕜 := ℝ) (x := x) hs.contDiffAt hk'.contDiffAt
  rw [show (fun y : Euc d => f (y + h • e) - f y) = (fun y : Euc d => f (y + h • e)) - f from rfl,
    hsub, iteratedFDeriv_comp_add_right]

lemma s67bd_diff_fderiv {f : Euc d → F} (hf : Differentiable ℝ f) (h : ℝ) (e : Euc d)
    (x : Euc d) :
    fderiv ℝ (s67bd_diff h e f) x = h⁻¹ • (fderiv ℝ f (x + h • e) - fderiv ℝ f x) := by
  have hs : DifferentiableAt ℝ (fun y : Euc d => f (y + h • e)) x :=
    (hf (x + h • e)).comp x (differentiableAt_id.add_const _)
  unfold s67bd_diff
  rw [show (fun y : Euc d => h⁻¹ • (f (y + h • e) - f y)) =
    h⁻¹ • ((fun y : Euc d => f (y + h • e)) - f) from rfl,
    fderiv_const_smul (hs.sub (hf x)), fderiv_sub hs (hf x), fderiv_comp_add_right]

end DiffCalculus

lemma s67bd_diff_gradient {f : Euc d → ℝ} (hf : Differentiable ℝ f) (h : ℝ) (e : Euc d)
    (x : Euc d) :
    gradient (s67bd_diff h e f) x =
      h⁻¹ • (gradient f (x + h • e) - gradient f x) := by
  unfold gradient
  rw [s67bd_diff_fderiv hf, map_smul, map_sub]

lemma s67bd_diff_laplacian {f : Euc d → ℝ} (hf : ContDiff ℝ 2 f) (h : ℝ) (e : Euc d)
    (x : Euc d) :
    Laplacian.laplacian (s67bd_diff h e f) x =
      h⁻¹ * (Laplacian.laplacian f (x + h • e) - Laplacian.laplacian f x) := by
  have hL : ∀ g : Euc d → ℝ, ∀ y, Laplacian.laplacian g y = ∑ i,
      iteratedFDeriv ℝ 2 g y ![(stdOrthonormalBasis ℝ (Euc d)) i, (stdOrthonormalBasis ℝ (Euc d)) i] :=
    fun g y => congrFun (InnerProductSpace.laplacian_eq_iteratedFDeriv_stdOrthonormalBasis g) y
  rw [hL, hL, hL]
  simp only [s67bd_diff_iteratedFDeriv hf h e (le_refl 2), smul_apply,
    sub_apply, smul_eq_mul, ← Finset.mul_sum, ← Finset.sum_sub_distrib]

lemma s67bd_gradient_eq_curry (f : Euc d → ℝ) (x : Euc d) :
    gradient f x = (InnerProductSpace.toDual ℝ (Euc d)).symm
      (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 1 f x)) := by
  unfold gradient
  congr 1
  ext v
  simp [continuousMultilinearCurryFin1_apply, iteratedFDeriv_one_apply]

theorem s67bd_difference_pde (ν q T : ℝ)
    (u a : ℝ → Euc d → ℝ) (B : ℝ → Euc d → Euc d) (J : ℝ → Euc d → ℝ)
    (hu : s67bd_ParabolicData ν q T u a B J)
    (h : ℝ) (hh : h ≠ 0) (e : Euc d) (he : ‖e‖ = 1) :
    s67bd_ParabolicData ν q T (fun t => s67bd_diff h e (u t))
      (fun t => s67bd_diff h e (a t)) B
      (fun t x => s67bd_diff h e (J t) x +
        inner ℝ (s67bd_diff h e (B t) x) (gradient (u t) (x + h • e)) -
        q * inner ℝ e (gradient (u t) (x + h • e))) := by
  -- the shift map on the time-space slab
  have hshift : ContinuousOn (fun p : ℝ × Euc d => (p.1, p.2 + h • e))
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) :=
    (continuousOn_fst.prodMk (continuousOn_snd.add continuousOn_const))
  have hmaps : Set.MapsTo (fun p : ℝ × Euc d => (p.1, p.2 + h • e))
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) :=
    fun p hp => ⟨hp.1, mem_univ _⟩
  -- continuity of a family and its shift-difference
  have hdiffc : ∀ {F : Type} [NormedAddCommGroup F] [NormedSpace ℝ F] (W : ℝ → Euc d → F),
      ContinuousOn (fun p : ℝ × Euc d => W p.1 p.2) (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) →
      ContinuousOn (fun p : ℝ × Euc d => s67bd_diff h e (W p.1) p.2)
        (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := by
    intro F _ _ W hW
    exact ((hW.comp hshift hmaps).sub hW).const_smul _
  have hgrad : ContinuousOn (fun p : ℝ × Euc d => gradient (u p.1) p.2)
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := by
    have h1 := hu.cont_c2 1 (by norm_num)
    have h2 : ContinuousOn (fun p : ℝ × Euc d =>
        (InnerProductSpace.toDual ℝ (Euc d)).symm
          (continuousMultilinearCurryFin1 ℝ (Euc d) ℝ (iteratedFDeriv ℝ 1 (u p.1) p.2)))
        (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) :=
      (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
        ((continuousMultilinearCurryFin1 ℝ (Euc d) ℝ).continuous.comp_continuousOn h1)
    refine h2.congr (fun p _ => ?_)
    exact s67bd_gradient_eq_curry (u p.1) p.2
  have hgrad' : ContinuousOn (fun p : ℝ × Euc d => gradient (u p.1) (p.2 + h • e))
      (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := hgrad.comp hshift hmaps
  have hcont0 : ∀ y : Euc d, ∀ {t : ℝ} {t0 : ℝ}, t ∈ Icc (0 : ℝ) T → t0 ∈ Icc (0 : ℝ) T →
      IntervalIntegrable (fun v => a v y) volume t0 t := by
    intro y t t0 ht ht0
    have hc : ContinuousOn (fun v => a v y) (Icc (0 : ℝ) T) :=
      hu.acont.comp (continuousOn_id.prodMk continuousOn_const) (fun v hv => ⟨hv, mem_univ _⟩)
    exact (hc.mono (uIcc_subset_Icc ht0 ht)).intervalIntegrable
  refine
    { c2 := fun t ht => s67bd_diff_contDiff (hu.c2 t ht) h e
      bdd_c2 := ?_
      cont_c2 := ?_
      acont := hdiffc a hu.acont
      agrow := ?_
      Bcont := hu.Bcont
      Jcont := ?_
      hint := ?_
      equation := ?_ }
  · obtain ⟨K, hK⟩ := hu.bdd_c2
    refine ⟨|h|⁻¹ * (K + K), fun t ht k hk x => ?_⟩
    rw [s67bd_diff_iteratedFDeriv (hu.c2 t ht) h e hk, norm_smul, norm_inv, Real.norm_eq_abs]
    refine mul_le_mul_of_nonneg_left ?_ (by positivity)
    exact (norm_sub_le _ _).trans (add_le_add (hK t ht k hk _) (hK t ht k hk x))
  · intro k hk
    have h1 := hu.cont_c2 k hk
    have h2 : ContinuousOn (fun p : ℝ × Euc d =>
        h⁻¹ • (iteratedFDeriv ℝ k (u p.1) (p.2 + h • e) - iteratedFDeriv ℝ k (u p.1) p.2))
        (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) :=
      by have := ((h1.comp hshift hmaps).sub h1).const_smul h⁻¹; exact this
    refine h2.congr (fun p hp => ?_)
    exact s67bd_diff_iteratedFDeriv (hu.c2 p.1 hp.1) h e hk p.2
  · obtain ⟨K, hK⟩ := hu.agrow
    refine ⟨|h|⁻¹ * (|K| * (2 + |h|)), fun t ht x => ?_⟩
    have h1 := hK t ht (x + h • e)
    have h2 := hK t ht x
    have hn : ‖x + h • e‖ ≤ ‖x‖ + |h| :=
      (norm_add_le _ _).trans (by rw [norm_smul, he, Real.norm_eq_abs, mul_one])
    have hKa : K * (1 + ‖x + h • e‖) ≤ |K| * (1 + ‖x‖ + |h|) :=
      calc K * (1 + ‖x + h • e‖) ≤ |K| * (1 + ‖x + h • e‖) :=
            mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
        _ ≤ |K| * (1 + ‖x‖ + |h|) := mul_le_mul_of_nonneg_left (by linarith) (abs_nonneg K)
    have hKb : K * (1 + ‖x‖) ≤ |K| * (1 + ‖x‖) :=
      mul_le_mul_of_nonneg_right (le_abs_self K) (by positivity)
    have hsum : |a t (x + h • e) - a t x| ≤ |K| * (2 + |h|) * (1 + ‖x‖) := by
      have := abs_sub (a t (x + h • e)) (a t x)
      nlinarith [mul_nonneg (abs_nonneg K) (mul_nonneg (abs_nonneg h) (norm_nonneg x))]
    show |s67bd_diff h e (a t) x| ≤ _
    unfold s67bd_diff
    rw [smul_eq_mul, abs_mul, abs_inv]
    calc |h|⁻¹ * |a t (x + h • e) - a t x| ≤ |h|⁻¹ * (|K| * (2 + |h|) * (1 + ‖x‖)) :=
          mul_le_mul_of_nonneg_left hsum (by positivity)
      _ = |h|⁻¹ * (|K| * (2 + |h|)) * (1 + ‖x‖) := by ring
  · have hBd : ContinuousOn (fun p : ℝ × Euc d => s67bd_diff h e (B p.1) p.2)
        (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := hdiffc B hu.Bcont
    have hin1 : ContinuousOn (fun p : ℝ × Euc d =>
        inner ℝ (s67bd_diff h e (B p.1) p.2) (gradient (u p.1) (p.2 + h • e)))
        (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := hBd.inner hgrad'
    have hin2 : ContinuousOn (fun p : ℝ × Euc d =>
        inner ℝ e (gradient (u p.1) (p.2 + h • e)))
        (Icc (0 : ℝ) T ×ˢ (univ : Set (Euc d))) := continuousOn_const.inner hgrad'
    exact ((hdiffc J hu.Jcont).add hin1).sub (hin2.const_smul q)
  · intro t ht t0 ht0 x
    show h⁻¹ • (u t (x + h • e) - u t x) - h⁻¹ • (u t0 (x + h • e) - u t0 x) =
      ∫ v in t0..t, h⁻¹ • (a v (x + h • e) - a v x)
    rw [intervalIntegral.integral_smul, intervalIntegral.integral_sub (hcont0 _ ht ht0)
      (hcont0 _ ht ht0), ← hu.hint t ht t0 ht0 (x + h • e), ← hu.hint t ht t0 ht0 x,
      ← smul_sub]
    congr 1
    abel
  · intro t ht x
    have hU := hu.c2 t ht
    have hd : Differentiable ℝ (u t) := hU.differentiable (by norm_num)
    have e1 := hu.equation t ht (x + h • e)
    have e0 := hu.equation t ht x
    show h⁻¹ • (a t (x + h • e) - a t x) = _
    rw [s67bd_diff_laplacian hU h e x, s67bd_diff_gradient hd h e x]
    simp only [s67bd_diff, smul_eq_mul]
    rw [e1, e0]
    simp only [inner_add_left, inner_sub_right, inner_smul_left, inner_smul_right,
      inner_neg_left, inner_add_right, inner_sub_left, RCLike.conj_to_real,
      real_inner_smul_left, real_inner_smul_right, smul_sub, smul_add, smul_eq_mul]
    field_simp
    ring

end HRS.MS.BreakdownS67
