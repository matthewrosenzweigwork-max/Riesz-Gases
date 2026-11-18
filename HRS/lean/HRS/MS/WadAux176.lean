import HRS.MS.WadAux175

/-!
# S8.3, packet S8H2-2: the separated jet bound

Abstract bound: let `G(x,y) = ∑_l a_l(x) b_l(y)` and `H(x,y) = ∑_l a_l(x) c_l(y)`, where the assignment `∑ λ_l b_l ↦ ∑ λ_l c_l`
is bounded for jets of order `r ≤ m` against a weight `wt` (this is the case `c_l = U_t b_l`).  If the pair jets of `G` of order `≤ m`
are bounded by `N wt(x) wt(y)`, then those of `H` are bounded by `2^i K N wt(x) wt(y)` (`s8h2_sep_bound`).
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Wad

section Sep

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E] {ι : Type} [Fintype ι]

/-- `G(x,y) = ∑_l a_l(x) b_l(y)`. -/
def s8h2_G (a b : ι → E → ℝ) (z : E × E) : ℝ := ∑ l, a l z.1 * b l z.2

/-- `f_{p,η}(x,y) = ∑_l a_l(x) D^p c_l(y)(η)`. -/
def s8h2_f (a c : ι → E → ℝ) (p : ℕ) (η : Fin p → E) (z : E × E) : ℝ :=
  ∑ l, a l z.1 * iteratedFDeriv ℝ p (c l) z.2 η

theorem s8h2_f_zero (a c : ι → E → ℝ) (η : Fin 0 → E) : s8h2_f a c 0 η = s8h2_G a c := by
  funext z
  simp [s8h2_f, s8h2_G, iteratedFDeriv_zero_apply]

theorem s8h2_f_contDiff {a c : ι → E → ℝ} {n p : ℕ} (ha : ∀ l, ContDiff ℝ n (a l))
    (hc : ∀ l, ContDiff ℝ (n + p : ℕ) (c l)) (η : Fin p → E) : ContDiff ℝ n (s8h2_f a c p η) := by
  unfold s8h2_f
  refine ContDiff.sum fun l _ => ?_
  have h1 : ContDiff ℝ n (fun z : E × E => a l z.1) := (ha l).comp contDiff_fst
  have h2 : ContDiff ℝ n (iteratedFDeriv ℝ p (c l)) :=
    (hc l).iteratedFDeriv_right (i := p) (by exact_mod_cast le_refl _)
  have h3 : ContDiff ℝ n (fun y : E => iteratedFDeriv ℝ p (c l) y η) :=
    (ContinuousMultilinearMap.apply ℝ (fun _ : Fin p => E) ℝ η).contDiff.comp h2
  exact h1.mul (h3.comp contDiff_snd)

theorem s8h2_fderiv_f {a c : ι → E → ℝ} {p : ℕ} (ha : ∀ l, ContDiff ℝ 1 (a l))
    (hc : ∀ l, ContDiff ℝ (p + 1 : ℕ) (c l)) (η : Fin p → E) (z w : E × E) :
    fderiv ℝ (s8h2_f a c p η) z w =
      s8h2_f (fun l x => fderiv ℝ (a l) x w.1) c p η z + s8h2_f a c (p + 1) (Fin.cons w.2 η) z := by
  have hd : ∀ l ∈ (Finset.univ : Finset ι), HasFDerivAt (fun z : E × E => a l z.1 * iteratedFDeriv ℝ p (c l) z.2 η)
      (a l z.1 • ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin p => E) ℝ η).comp
          ((fderiv ℝ (iteratedFDeriv ℝ p (c l)) z.2).comp (ContinuousLinearMap.snd ℝ E E))) +
        iteratedFDeriv ℝ p (c l) z.2 η • ((fderiv ℝ (a l) z.1).comp (ContinuousLinearMap.fst ℝ E E))) z := by
    intro l _
    have hA : HasFDerivAt (fun z : E × E => a l z.1) ((fderiv ℝ (a l) z.1).comp (ContinuousLinearMap.fst ℝ E E)) z :=
      HasFDerivAt.comp z (((ha l).differentiable one_ne_zero z.1).hasFDerivAt) (hasFDerivAt_fst)
    have hdiff : Differentiable ℝ (iteratedFDeriv ℝ p (c l)) :=
      (hc l).differentiable_iteratedFDeriv (m := p) (by exact_mod_cast Nat.lt_succ_self p)
    have hD0 : HasFDerivAt (iteratedFDeriv ℝ p (c l)) (fderiv ℝ (iteratedFDeriv ℝ p (c l)) z.2) z.2 :=
      (hdiff z.2).hasFDerivAt
    have hD1 : HasFDerivAt (fun y : E => iteratedFDeriv ℝ p (c l) y η)
        ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin p => E) ℝ η).comp
          (fderiv ℝ (iteratedFDeriv ℝ p (c l)) z.2)) z.2 :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin p => E) ℝ η).hasFDerivAt.comp z.2 hD0
    have hD2 : HasFDerivAt (fun z : E × E => iteratedFDeriv ℝ p (c l) z.2 η)
        (((ContinuousMultilinearMap.apply ℝ (fun _ : Fin p => E) ℝ η).comp
          (fderiv ℝ (iteratedFDeriv ℝ p (c l)) z.2)).comp (ContinuousLinearMap.snd ℝ E E)) z :=
      HasFDerivAt.comp z hD1 (hasFDerivAt_snd)
    exact hA.mul hD2 |>.congr_fderiv (by
      rw [ContinuousLinearMap.comp_assoc])
  have hs := HasFDerivAt.fun_sum hd
  have e : s8h2_f a c p η = fun z : E × E => ∑ l, a l z.1 * iteratedFDeriv ℝ p (c l) z.2 η := rfl
  rw [e, hs.fderiv]
  simp only [s8h2_f, ContinuousLinearMap.sum_apply, ContinuousLinearMap.add_apply,
    ContinuousLinearMap.smul_apply, ContinuousLinearMap.comp_apply, ContinuousLinearMap.coe_fst',
    ContinuousLinearMap.coe_snd', ContinuousMultilinearMap.apply_apply, smul_eq_mul]
  rw [← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun l _ => ?_
  rw [iteratedFDeriv_succ_apply_left]
  simp only [Fin.cons_zero, Fin.tail_cons]
  ring

theorem s8h2_G_contDiff {a b : ι → E → ℝ} {n : ℕ} (ha : ∀ l, ContDiff ℝ n (a l))
    (hb : ∀ l, ContDiff ℝ n (b l)) : ContDiff ℝ n (s8h2_G a b) :=
  ContDiff.sum fun l _ => ((ha l).comp contDiff_fst).mul ((hb l).comp contDiff_snd)

theorem s8h2_iter_lincomb {c : ι → E → ℝ} {n : ℕ} (hc : ∀ l, ContDiff ℝ n (c l)) (lam : ι → ℝ) (y : E)
    (η : Fin n → E) :
    iteratedFDeriv ℝ n (fun y => ∑ l, lam l * c l y) y η = ∑ l, lam l * iteratedFDeriv ℝ n (c l) y η := by
  rw [iteratedFDeriv_fun_sum_apply (f := fun l z => lam l * c l z)
    (fun l _ => ((hc l).const_smul (lam l)).contDiffAt)]
  simp only [ContinuousMultilinearMap.sum_apply]
  refine Finset.sum_congr rfl fun l _ => ?_
  have := iteratedFDeriv_const_smul_apply' (a := lam l) (f := c l) (x := y) (i := n) (hc l).contDiffAt
  simp only [smul_eq_mul] at this
  rw [this]
  simp

theorem s8h2_iter_succ_le {V : Type} [NormedAddCommGroup V] [NormedSpace ℝ V] {f : V → ℝ} {k : ℕ}
    (hf : ContDiff ℝ (k + 1 : ℕ) f) {B : ℝ} (hB0 : 0 ≤ B) (z : V)
    (hB : ∀ w : V, ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ f z w) z‖ ≤ B * ‖w‖) :
    ‖iteratedFDeriv ℝ (k + 1) f z‖ ≤ B := by
  rw [← norm_iteratedFDeriv_fderiv]
  have hfd : ContDiffAt ℝ k (fderiv ℝ f) z :=
    (hf.fderiv_right (m := k) (by exact_mod_cast le_refl _)).contDiffAt
  refine ContinuousMultilinearMap.opNorm_le_bound hB0 fun m => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (mul_nonneg hB0 (Finset.prod_nonneg fun i _ => norm_nonneg _))
    fun w => ?_
  have h1 := ContinuousLinearMap.iteratedFDeriv_comp_left (ContinuousLinearMap.apply ℝ ℝ w) hfd (i := k)
    (by exact_mod_cast le_refl _)
  have h2 : (iteratedFDeriv ℝ k (fderiv ℝ f) z m) w = iteratedFDeriv ℝ k (fun z => fderiv ℝ f z w) z m := by
    have := congrArg (fun T => T m) h1
    simpa [Function.comp_def] using this.symm
  rw [h2]
  calc ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ f z w) z m‖
      ≤ ‖iteratedFDeriv ℝ k (fun z => fderiv ℝ f z w) z‖ * ∏ i, ‖m i‖ :=
        (iteratedFDeriv ℝ k (fun z => fderiv ℝ f z w) z).le_opNorm m
    _ ≤ B * ‖w‖ * ∏ i, ‖m i‖ :=
        mul_le_mul_of_nonneg_right (hB w) (Finset.prod_nonneg fun i _ => norm_nonneg _)
    _ = B * (∏ i, ‖m i‖) * ‖w‖ := by ring

theorem s8h2_slice_jet {G : E × E → ℝ} {m : ℕ} (hG : ContDiff ℝ m G) (x : E) {i : ℕ} (hi : i ≤ m) (y : E) :
    ‖iteratedFDeriv ℝ i (fun y => G (x, y)) y‖ ≤ ‖iteratedFDeriv ℝ i G (x, y)‖ := by
  have h1 : ContDiff ℝ m (fun z : E × E => G (z + (x, 0))) := hG.comp (contDiff_id.add contDiff_const)
  have h2 := ContinuousLinearMap.iteratedFDeriv_comp_right (ContinuousLinearMap.inr ℝ E E) h1 y (i := i)
    (by exact_mod_cast hi)
  have e : (fun y : E => G (x, y)) = (fun z : E × E => G (z + (x, 0))) ∘ (ContinuousLinearMap.inr ℝ E E) := by
    funext y; simp
  rw [e, h2, iteratedFDeriv_comp_add_right]
  refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
  have hp : ∏ _i : Fin i, ‖ContinuousLinearMap.inr ℝ E E‖ ≤ 1 :=
    Finset.prod_le_one₀ (fun _ _ => norm_nonneg _) (fun _ _ => ContinuousLinearMap.norm_inr_le_one ℝ E E)
  have e2 : (ContinuousLinearMap.inr ℝ E E) y + (x, 0) = (x, y) := by simp
  rw [e2]
  calc _ ≤ ‖iteratedFDeriv ℝ i G (x, y)‖ * 1 :=
        mul_le_mul_of_nonneg_left hp (norm_nonneg _)
    _ = _ := mul_one _

theorem s8h2_swap_jet {F : E × E → ℝ} (i : ℕ) (z : E × E) :
    ‖iteratedFDeriv ℝ i (F ∘ Prod.swap) z‖ = ‖iteratedFDeriv ℝ i F z.swap‖ :=
  (LinearIsometryEquiv.prodComm ℝ E E).norm_iteratedFDeriv_comp_right F z i

theorem s8h2_sep_step {b c : ι → E → ℝ} {wt : E → ℝ} (hwt : ∀ x, 0 ≤ wt x) {K : ℝ} (hK : 0 ≤ K) {m : ℕ}
    (hb : ∀ l, ContDiff ℝ m (b l)) (hc : ∀ l, ContDiff ℝ m (c l))
    (hP : ∀ r ≤ m, ∀ lam : ι → ℝ, ∀ {N' : ℝ}, 0 ≤ N' →
      (∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i (fun y => ∑ l, lam l * b l y) y‖ ≤ N' * wt y) →
      ∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i (fun y => ∑ l, lam l * c l y) y‖ ≤ K * N' * wt y) :
    ∀ k : ℕ, ∀ (m' : ℕ) (a : ι → E → ℝ) {N : ℝ}, m' ≤ m → (∀ l, ContDiff ℝ m' (a l)) → 0 ≤ N →
      (∀ i ≤ m', ∀ z, ‖iteratedFDeriv ℝ i (s8h2_G a b) z‖ ≤ N * (wt z.1 * wt z.2)) →
      ∀ p, k + p ≤ m' → ∀ η : Fin p → E, ∀ z,
        ‖iteratedFDeriv ℝ k (s8h2_f a c p η) z‖ ≤ 2 ^ k * K * N * (wt z.1 * wt z.2) * ∏ i, ‖η i‖ := by
  intro k
  induction k with
  | zero =>
    intro m' a N hm ha hN hG p hp η z
    simp only [pow_zero, one_mul, norm_iteratedFDeriv_zero]
    have hpm : p ≤ m' := by omega
    have hcp : ∀ l, ContDiff ℝ p (c l) := fun l => (hc l).of_le (by exact_mod_cast hpm.trans hm)
    have e1 : s8h2_f a c p η z = iteratedFDeriv ℝ p (fun y => ∑ l, a l z.1 * c l y) z.2 η := by
      rw [s8h2_iter_lincomb hcp]; rfl
    have hGd : ContDiff ℝ m' (s8h2_G a b) := s8h2_G_contDiff ha (fun l => (hb l).of_le (by exact_mod_cast hm))
    have hbd := hP p (hpm.trans hm) (fun l => a l z.1) (N' := N * wt z.1) (mul_nonneg hN (hwt _)) (by
      intro i hi y
      have e : (fun y => ∑ l, a l z.1 * b l y) = fun y => s8h2_G a b (z.1, y) := rfl
      rw [e]
      refine (s8h2_slice_jet hGd z.1 (hi.trans hpm) y).trans ?_
      have := hG i (hi.trans hpm) (z.1, y)
      calc _ ≤ N * (wt (z.1, y).1 * wt (z.1, y).2) := this
        _ = N * wt z.1 * wt y := by simp [mul_assoc]) p le_rfl z.2
    rw [e1]
    refine ((iteratedFDeriv ℝ p (fun y => ∑ l, a l z.1 * c l y) z.2).le_opNorm η).trans ?_
    refine mul_le_mul_of_nonneg_right ?_ (Finset.prod_nonneg fun i _ => norm_nonneg _)
    calc _ ≤ K * (N * wt z.1) * wt z.2 := hbd
      _ = K * N * (wt z.1 * wt z.2) := by ring
  | succ k ih =>
    intro m' a N hm ha hN hG p hp η z
    obtain ⟨m'', rfl⟩ : ∃ m'', m' = m'' + 1 := ⟨m' - 1, by omega⟩
    have ha1 : ∀ l, ContDiff ℝ 1 (a l) := fun l => (ha l).of_le (by exact_mod_cast (by omega : 1 ≤ m'' + 1))
    have hcp1 : ∀ l, ContDiff ℝ (p + 1 : ℕ) (c l) :=
      fun l => (hc l).of_le (by exact_mod_cast (by omega : p + 1 ≤ m))
    have hfd : ContDiff ℝ (k + 1 : ℕ) (s8h2_f a c p η) :=
      s8h2_f_contDiff (n := k + 1) (fun l => (ha l).of_le (by exact_mod_cast (by omega : k + 1 ≤ m'' + 1)))
        (fun l => (hc l).of_le (by exact_mod_cast (by omega : k + 1 + p ≤ m))) η
    have hW0 : 0 ≤ wt z.1 * wt z.2 := mul_nonneg (hwt _) (hwt _)
    have hprod0 : 0 ≤ ∏ i, ‖η i‖ := Finset.prod_nonneg fun i _ => norm_nonneg _
    have hB0 : 0 ≤ 2 ^ (k + 1) * K * N * (wt z.1 * wt z.2) * ∏ i, ‖η i‖ := by positivity
    refine s8h2_iter_succ_le hfd hB0 z (fun w => ?_)
    have hfun : (fun z => fderiv ℝ (s8h2_f a c p η) z w) = fun z =>
        s8h2_f (fun l x => fderiv ℝ (a l) x w.1) c p η z + s8h2_f a c (p + 1) (Fin.cons w.2 η) z :=
      funext fun z => s8h2_fderiv_f ha1 hcp1 η z w
    rw [hfun]
    have ha' : ∀ l, ContDiff ℝ m'' (fun x => fderiv ℝ (a l) x w.1) := fun l =>
      ((ha l).fderiv_right (m := m'') (by exact_mod_cast le_refl _)).clm_apply contDiff_const
    have hf1 : ContDiff ℝ k (s8h2_f (fun l x => fderiv ℝ (a l) x w.1) c p η) :=
      s8h2_f_contDiff (n := k) (fun l => (ha' l).of_le (by exact_mod_cast (by omega : k ≤ m'')))
        (fun l => (hc l).of_le (by exact_mod_cast (by omega : k + p ≤ m))) η
    have hf2 : ContDiff ℝ k (s8h2_f a c (p + 1) (Fin.cons w.2 η)) :=
      s8h2_f_contDiff (n := k) (fun l => (ha l).of_le (by exact_mod_cast (by omega : k ≤ m'' + 1)))
        (fun l => (hc l).of_le (by exact_mod_cast (by omega : k + (p + 1) ≤ m))) _
    have hsplit := iteratedFDeriv_add_apply hf1.contDiffAt hf2.contDiffAt (x := z)
    refine ((le_of_eq (congrArg norm hsplit)).trans (norm_add_le _ _)).trans ?_
    -- the jet hypothesis for the differentiated family
    have hGd : ContDiff ℝ (m'' + 1) (s8h2_G a b) :=
      s8h2_G_contDiff ha (fun l => (hb l).of_le (by exact_mod_cast hm))
    have eG : s8h2_G (fun l x => fderiv ℝ (a l) x w.1) b = fun z => fderiv ℝ (s8h2_G a b) z (w.1, 0) := by
      funext z'
      have h := s8h2_fderiv_f (a := a) (c := b) (p := 0) ha1
        (fun l => (hb l).of_le (by exact_mod_cast (by omega : 1 ≤ m))) (fun i => Fin.elim0 i) z' (w.1, 0)
      rw [s8h2_f_zero] at h
      rw [h, s8h2_f_zero]
      have h0 : s8h2_f a b (0 + 1) (Fin.cons (w.1, 0).2 (fun i : Fin 0 => Fin.elim0 i)) z' = 0 := by
        simp [s8h2_f]
      rw [h0, add_zero]
    have hG' : ∀ i ≤ m'', ∀ z, ‖iteratedFDeriv ℝ i (s8h2_G (fun l x => fderiv ℝ (a l) x w.1) b) z‖ ≤
        N * ‖w.1‖ * (wt z.1 * wt z.2) := by
      intro i hi z'
      rw [eG]
      have h1 := norm_iteratedFDeriv_clm_apply_const (f := fderiv ℝ (s8h2_G a b)) (c := (w.1, (0 : E)))
        (x := z') (n := i) (N := (m'' : ℕ∞ω))
        ((hGd.fderiv_right (m := m'') (by exact_mod_cast le_refl _)).contDiffAt) (by exact_mod_cast hi)
      rw [norm_iteratedFDeriv_fderiv] at h1
      have h2 := hG (i + 1) (by omega) z'
      have h3 : ‖(w.1, (0 : E))‖ = ‖w.1‖ := by simp [Prod.norm_def]
      rw [h3] at h1
      calc _ ≤ ‖w.1‖ * ‖iteratedFDeriv ℝ (i + 1) (s8h2_G a b) z'‖ := h1
        _ ≤ ‖w.1‖ * (N * (wt z'.1 * wt z'.2)) := mul_le_mul_of_nonneg_left h2 (norm_nonneg _)
        _ = N * ‖w.1‖ * (wt z'.1 * wt z'.2) := by ring
    have ih1 := ih m'' (fun l x => fderiv ℝ (a l) x w.1) (N := N * ‖w.1‖) (by omega) ha'
      (mul_nonneg hN (norm_nonneg _)) hG' p (by omega) η z
    have ih2 := ih (m'' + 1) a (N := N) hm ha hN hG (p + 1) (by omega) (Fin.cons w.2 η) z
    have hprod : ∏ i : Fin (p + 1), ‖(Fin.cons w.2 η : Fin (p + 1) → E) i‖ = ‖w.2‖ * ∏ i, ‖η i‖ := by
      rw [Fin.prod_univ_succ]; simp
    rw [hprod] at ih2
    have hw1 : ‖w.1‖ ≤ ‖w‖ := norm_fst_le w
    have hw2 : ‖w.2‖ ≤ ‖w‖ := norm_snd_le w
    have hX : 0 ≤ 2 ^ k * K * N * (wt z.1 * wt z.2) * ∏ i, ‖η i‖ := by positivity
    calc _ ≤ 2 ^ k * K * (N * ‖w.1‖) * (wt z.1 * wt z.2) * ∏ i, ‖η i‖ +
        2 ^ k * K * N * (wt z.1 * wt z.2) * (‖w.2‖ * ∏ i, ‖η i‖) := add_le_add ih1 ih2
      _ = (2 ^ k * K * N * (wt z.1 * wt z.2) * ∏ i, ‖η i‖) * (‖w.1‖ + ‖w.2‖) := by ring
      _ ≤ (2 ^ k * K * N * (wt z.1 * wt z.2) * ∏ i, ‖η i‖) * (2 * ‖w‖) :=
          mul_le_mul_of_nonneg_left (by linarith) hX
      _ = 2 ^ (k + 1) * K * N * (wt z.1 * wt z.2) * (∏ i, ‖η i‖) * ‖w‖ := by ring

theorem s8h2_sep_bound {b c : ι → E → ℝ} {wt : E → ℝ} (hwt : ∀ x, 0 ≤ wt x) {K : ℝ} (hK : 0 ≤ K) {m : ℕ}
    (hb : ∀ l, ContDiff ℝ m (b l)) (hc : ∀ l, ContDiff ℝ m (c l))
    (hP : ∀ r ≤ m, ∀ lam : ι → ℝ, ∀ {N' : ℝ}, 0 ≤ N' →
      (∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i (fun y => ∑ l, lam l * b l y) y‖ ≤ N' * wt y) →
      ∀ i ≤ r, ∀ y, ‖iteratedFDeriv ℝ i (fun y => ∑ l, lam l * c l y) y‖ ≤ K * N' * wt y)
    {a : ι → E → ℝ} (ha : ∀ l, ContDiff ℝ m (a l)) {N : ℝ} (hN : 0 ≤ N)
    (hG : ∀ i ≤ m, ∀ z, ‖iteratedFDeriv ℝ i (s8h2_G a b) z‖ ≤ N * (wt z.1 * wt z.2)) :
    ∀ i ≤ m, ∀ z, ‖iteratedFDeriv ℝ i (s8h2_G a c) z‖ ≤ 2 ^ i * K * N * (wt z.1 * wt z.2) := by
  intro i hi z
  have := s8h2_sep_step hwt hK hb hc hP i m a le_rfl ha hN hG 0 (by omega) (fun j => Fin.elim0 j) z
  rw [s8h2_f_zero] at this
  simpa using this

end Sep

end HRS.MS.Wad
