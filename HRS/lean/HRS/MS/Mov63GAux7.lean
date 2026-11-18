import HRS.MS.Mov63GAux6

/-!
# S6.3, packet N8 (part 7): bridges between partial-derivative jets and `iteratedFDeriv`

Namespace `HRS.MS.Mov63`, prefix `mng_`.

* `mngJt_eq_iter`: `∂_{l_1}⋯∂_{l_n} g (x) = D^n g(x)(e_{l_1}, …, e_{l_n})`.
* `mngJt_le_norm`: `|∂_l g| ≤ ‖D^n g‖`; `mng_norm_iter_le`: `‖D^n g(x)‖ ≤ ∑_σ |∂_σ g (x)|`; `mng_norm_iter_sq_le`: `‖D^n g(x)‖² ≤ d^n S_n`.
* `mngJC_of_iter`, `mngBW_of_iter`: joint continuity / bounds of all partial derivatives from those of `iteratedFDeriv`.
-/

noncomputable section

open Filter Topology Set MeasureTheory
open scoped RealInnerProductSpace

namespace HRS.MS.Mov63

open HRS

variable {d : ℕ}

/-- The basis tuple of a list of directions. -/
def mngMv (l : List (Fin d)) : Fin l.length → Euc d := fun a => mngE (l.get a)

lemma mngJt_eq_iter {Q : ℝ → Euc d → ℝ} {n : ℕ} (hQ : ∀ t, ContDiff ℝ n (Q t)) :
    ∀ l : List (Fin d), l.length ≤ n → ∀ t x,
      mngJt Q l t x = iteratedFDeriv ℝ l.length (Q t) x (mngMv l)
  | [], _, t, x => by simp [mngJt, mngMv]
  | i :: l, hl, t, x => by
    have ih := mngJt_eq_iter hQ l (by simp at hl; omega)
    have hfun : mngJt Q l t = fun y => iteratedFDeriv ℝ l.length (Q t) y (mngMv l) := funext (ih t)
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ l.length (Q t)) x :=
      ((hQ t).differentiable_iteratedFDeriv (by exact_mod_cast (by simp at hl; omega : l.length < n)) x)
    have h1 : HasFDerivAt (fun y => iteratedFDeriv ℝ l.length (Q t) y (mngMv l))
        ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin l.length => Euc d) ℝ (mngMv l)).comp
          (fderiv ℝ (iteratedFDeriv ℝ l.length (Q t)) x)) x :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin l.length => Euc d) ℝ (mngMv l)).hasFDerivAt.comp x
        hd.hasFDerivAt
    have e1 : mngJt Q (i :: l) t x = fderiv ℝ (mngJt Q l t) x (mngE i) := rfl
    rw [e1, hfun, h1.fderiv]
    show _ = iteratedFDeriv ℝ (l.length + 1) (Q t) x (mngMv (i :: l))
    rw [iteratedFDeriv_succ_apply_left]
    have hm0 : mngMv (i :: l) 0 = mngE i := by simp [mngMv]
    have hmt : Fin.tail (mngMv (i :: l)) = mngMv l := by
      ext a; simp [mngMv, Fin.tail]
    rw [hm0, hmt]
    rfl

lemma mngJt_le_norm {Q : ℝ → Euc d → ℝ} {n : ℕ} (hQ : ∀ t, ContDiff ℝ n (Q t)) (l : List (Fin d))
    (hl : l.length ≤ n) (t : ℝ) (x : Euc d) : |mngJt Q l t x| ≤ ‖iteratedFDeriv ℝ l.length (Q t) x‖ := by
  rw [mngJt_eq_iter hQ l hl t x, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have : ∏ a, ‖mngMv l a‖ = 1 := by
    simp [mngMv, mngE]
  rw [this, mul_one]
lemma mngJt_ofFn {Q : ℝ → Euc d → ℝ} {N : ℕ} (hQ : ∀ t, ContDiff ℝ N (Q t)) :
    ∀ (n : ℕ), n ≤ N → ∀ (σ : Fin n → Fin d) (t : ℝ) (x : Euc d),
      mngJt Q (List.ofFn σ) t x = iteratedFDeriv ℝ n (Q t) x (fun a => mngE (σ a))
  | 0, _, σ, t, x => by simp [mngJt]
  | n + 1, hn, σ, t, x => by
    have ih := mngJt_ofFn hQ n (by omega) (fun a => σ a.succ) t
    have hfun : mngJt Q (List.ofFn fun a : Fin n => σ a.succ) t =
        fun y => iteratedFDeriv ℝ n (Q t) y (fun a => mngE (σ a.succ)) := funext ih
    have hd : DifferentiableAt ℝ (iteratedFDeriv ℝ n (Q t)) x :=
      ((hQ t).differentiable_iteratedFDeriv (by exact_mod_cast (by omega : n < N)) x)
    have h1 : HasFDerivAt (fun y => iteratedFDeriv ℝ n (Q t) y (fun a => mngE (σ a.succ)))
        ((ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ (fun a => mngE (σ a.succ))).comp
          (fderiv ℝ (iteratedFDeriv ℝ n (Q t)) x)) x :=
      (ContinuousMultilinearMap.apply ℝ (fun _ : Fin n => Euc d) ℝ (fun a => mngE (σ a.succ))).hasFDerivAt.comp x
        hd.hasFDerivAt
    rw [List.ofFn_succ]
    have e1 : mngJt Q (σ 0 :: List.ofFn fun a : Fin n => σ a.succ) t x =
        fderiv ℝ (mngJt Q (List.ofFn fun a : Fin n => σ a.succ) t) x (mngE (σ 0)) := rfl
    rw [e1, hfun, h1.fderiv, iteratedFDeriv_succ_apply_left]
    rfl

lemma mng_opnorm_le_sum {n : ℕ} (M : ContinuousMultilinearMap ℝ (fun _ : Fin n => Euc d) ℝ) :
    ‖M‖ ≤ ∑ σ : Fin n → Fin d, |M (fun a => mngE (σ a))| := by
  classical
  refine M.opNorm_le_bound (Finset.sum_nonneg fun _ _ => abs_nonneg _) fun h => ?_
  have hh : ∀ a, h a = ∑ j : Fin d, (h a j) • mngE j := fun a => by
    ext k; simp [mngE, Pi.single_apply]
  have e1 : M h = ∑ r : Fin n → Fin d, M (fun a => (h a (r a)) • mngE (r a)) := by
    have := MultilinearMap.map_sum (M.toMultilinearMap) (fun (a : Fin n) (j : Fin d) => (h a j) • mngE j)
    have e : h = fun a => ∑ j : Fin d, (h a j) • mngE j := funext hh
    conv_lhs => rw [e]
    exact this
  have e2 : ∀ r : Fin n → Fin d, M (fun a => (h a (r a)) • mngE (r a)) =
      (∏ a, h a (r a)) • M (fun a => mngE (r a)) := fun r => M.map_smul_univ _ _
  rw [e1]
  calc |∑ r : Fin n → Fin d, M (fun a => (h a (r a)) • mngE (r a))|
      ≤ ∑ r : Fin n → Fin d, |M (fun a => (h a (r a)) • mngE (r a))| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ r : Fin n → Fin d, |M (fun a => mngE (r a))| * ∏ a, ‖h a‖ := by
        refine Finset.sum_le_sum fun r _ => ?_
        rw [e2, smul_eq_mul, abs_mul, mul_comm]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        rw [Finset.abs_prod]
        refine Finset.prod_le_prod₀ (fun a _ => abs_nonneg ((h a) (r a))) (fun a _ => ?_)
        rw [← Real.norm_eq_abs]; exact PiLp.norm_apply_le (h a) (r a)
    _ = _ := by rw [← Finset.sum_mul]

lemma mng_sum_vector {n : ℕ} (f : List (Fin d) → ℝ) :
    ∑ v : List.Vector (Fin d) n, f v.toList = ∑ σ : Fin n → Fin d, f (List.ofFn σ) := by
  refine Fintype.sum_equiv (Equiv.vectorEquivFin (Fin d) n) _ _ fun v => ?_
  have : v = List.Vector.ofFn (Equiv.vectorEquivFin (Fin d) n v) := by
    simp [Equiv.vectorEquivFin]
  conv_lhs => rw [this]
  rw [List.Vector.toList_ofFn]

lemma mng_norm_iter_sq_le {Q : ℝ → Euc d → ℝ} {N : ℕ} (hQ : ∀ t, ContDiff ℝ N (Q t)) {n : ℕ} (hn : n ≤ N)
    (t : ℝ) (x : Euc d) : ‖iteratedFDeriv ℝ n (Q t) x‖ ^ 2 ≤ (d : ℝ) ^ n * mngS Q n t x := by
  have h1 := mng_opnorm_le_sum (iteratedFDeriv ℝ n (Q t) x)
  have e : ∀ σ : Fin n → Fin d, |iteratedFDeriv ℝ n (Q t) x (fun a => mngE (σ a))| =
      |mngJt Q (List.ofFn σ) t x| := fun σ => by rw [mngJt_ofFn hQ n hn σ t x]
  simp only [e] at h1
  have hS : mngS Q n t x = ∑ σ : Fin n → Fin d, (mngJt Q (List.ofFn σ) t x) ^ 2 := by
    unfold mngS
    rw [mng_sum_vector (fun l => mngJt Q l t x * mngJt Q l t x)]
    exact Finset.sum_congr rfl fun σ _ => (sq _).symm
  have hcs := sq_sum_le_card_mul_sum_sq (s := (Finset.univ : Finset (Fin n → Fin d)))
    (f := fun σ => |mngJt Q (List.ofFn σ) t x|)
  have hc : (Finset.univ : Finset (Fin n → Fin d)).card = d ^ n := by simp
  rw [hc] at hcs
  simp only [sq_abs] at hcs
  rw [hS]
  have h0 := norm_nonneg (iteratedFDeriv ℝ n (Q t) x)
  calc ‖iteratedFDeriv ℝ n (Q t) x‖ ^ 2 ≤ (∑ σ : Fin n → Fin d, |mngJt Q (List.ofFn σ) t x|) ^ 2 :=
        pow_le_pow_left₀ h0 h1 2
    _ ≤ _ := by push_cast at hcs; exact hcs

lemma mng_jt_sq_le {Q : ℝ → Euc d → ℝ} {N : ℕ} (hQ : ∀ t, ContDiff ℝ N (Q t)) {n : ℕ} (hn : n ≤ N)
    (σ : Fin n → Fin d) (t : ℝ) (x : Euc d) :
    |mngJt Q (List.ofFn σ) t x| ≤ ‖iteratedFDeriv ℝ n (Q t) x‖ := by
  rw [mngJt_ofFn hQ n hn σ t x, ← Real.norm_eq_abs]
  refine (ContinuousMultilinearMap.le_opNorm _ _).trans ?_
  have : ∏ a, ‖mngE (σ a)‖ = 1 := by simp [mngE]
  rw [this, mul_one]

lemma mng_apply_norm_le (i : Fin d) : ‖ContinuousLinearMap.apply ℝ ℝ (mngE i)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun L => ?_
  simp only [ContinuousLinearMap.apply_apply]
  have := L.le_opNorm (mngE i)
  simpa [mngE] using this

lemma mng_iter_pd {g : Euc d → ℝ} {k : ℕ} (hg : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g) (i : Fin d) (x : Euc d) :
    iteratedFDeriv ℝ k (fun y => fderiv ℝ g y (mngE i)) x =
      (ContinuousLinearMap.apply ℝ ℝ (mngE i)).compContinuousMultilinearMap
        (iteratedFDeriv ℝ k (fderiv ℝ g) x) := by
  have h1 : ContDiff ℝ (k : WithTop ℕ∞) (fderiv ℝ g) := hg.fderiv_right (by exact_mod_cast le_rfl)
  exact (ContinuousLinearMap.apply ℝ ℝ (mngE i)).iteratedFDeriv_comp_left h1.contDiffAt (le_refl _)

lemma mng_iter_fderiv_eq {g : Euc d → ℝ} {k : ℕ} (x : Euc d) :
    iteratedFDeriv ℝ k (fderiv ℝ g) x =
      (continuousMultilinearCurryRightEquiv' ℝ k (Euc d) ℝ) (iteratedFDeriv ℝ (k + 1) g x) := by
  rw [iteratedFDeriv_succ_eq_comp_right]
  simp

lemma mng_norm_iter_pd_le {g : Euc d → ℝ} {k : ℕ} (hg : ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) g) (i : Fin d)
    (x : Euc d) : ‖iteratedFDeriv ℝ k (fun y => fderiv ℝ g y (mngE i)) x‖ ≤ ‖iteratedFDeriv ℝ (k + 1) g x‖ := by
  rw [mng_iter_pd hg i x]
  refine (ContinuousLinearMap.norm_compContinuousMultilinearMap_le _ _).trans ?_
  have h1 := mng_apply_norm_le i
  have h2 : ‖iteratedFDeriv ℝ k (fderiv ℝ g) x‖ = ‖iteratedFDeriv ℝ (k + 1) g x‖ := norm_iteratedFDeriv_fderiv
  rw [h2]
  calc _ ≤ 1 * ‖iteratedFDeriv ℝ (k + 1) g x‖ := mul_le_mul_of_nonneg_right h1 (norm_nonneg _)
    _ = _ := one_mul _

lemma mng_cont_iter_pd {f : ℝ → Euc d → ℝ} {k : ℕ} (hcd : ∀ t, ContDiff ℝ ((k + 1 : ℕ) : WithTop ℕ∞) (f t))
    {S : Set (ℝ × Euc d)}
    (hc : ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ (k + 1) (f p.1) p.2) S) (i : Fin d) :
    ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ k (mngPd i f p.1) p.2) S := by
  have e : (fun p : ℝ × Euc d => iteratedFDeriv ℝ k (mngPd i f p.1) p.2) = fun p =>
      ((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => Euc d) (Euc d →L[ℝ] ℝ) ℝ)
        (ContinuousLinearMap.apply ℝ ℝ (mngE i)))
        ((continuousMultilinearCurryRightEquiv' ℝ k (Euc d) ℝ) (iteratedFDeriv ℝ (k + 1) (f p.1) p.2)) := by
    funext p
    show iteratedFDeriv ℝ k (fun y => fderiv ℝ (f p.1) y (mngE i)) p.2 = _
    rw [mng_iter_pd (hcd p.1) i p.2, mng_iter_fderiv_eq]
    rfl
  rw [e]
  exact (((ContinuousLinearMap.compContinuousMultilinearMapL ℝ (fun _ : Fin k => Euc d) (Euc d →L[ℝ] ℝ) ℝ)
    (ContinuousLinearMap.apply ℝ ℝ (mngE i))).continuous.comp
      (continuousMultilinearCurryRightEquiv' ℝ k (Euc d) ℝ).continuous).comp_continuousOn hc

lemma mngJC0_of_iter {f : ℝ → Euc d → ℝ} {S : Set (ℝ × Euc d)}
    (h0 : ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ 0 (f p.1) p.2) S) :
    ContinuousOn (fun p : ℝ × Euc d => f p.1 p.2) S := by
  have : (fun p : ℝ × Euc d => f p.1 p.2) =
      fun p => (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ (fun _ => 0))
        (iteratedFDeriv ℝ 0 (f p.1) p.2) := by
    funext p; simp
  rw [this]
  exact (ContinuousMultilinearMap.apply ℝ (fun _ : Fin 0 => Euc d) ℝ (fun _ => 0)).continuous.comp_continuousOn h0

lemma mngJC_of_iter : ∀ (r : ℕ) (f : ℝ → Euc d → ℝ), (∀ t, ContDiff ℝ r (f t)) →
    (∀ k ≤ r, ContinuousOn (fun p : ℝ × Euc d => iteratedFDeriv ℝ k (f p.1) p.2) (Ici 0 ×ˢ univ)) → mngJC r f
  | 0, f, _, hc => mngJC0_of_iter (hc 0 le_rfl)
  | r + 1, f, hcd, hc => by
    refine ⟨mngJC0_of_iter (hc 0 (Nat.zero_le _)), fun i => ?_⟩
    refine mngJC_of_iter r (mngPd i f) (fun t => mng_cd_pd (hcd t) i) (fun k hk => ?_)
    exact mng_cont_iter_pd (fun t => (hcd t).of_le (by exact_mod_cast (by omega : k + 1 ≤ r + 1)))
      (hc (k + 1) (by omega)) i

lemma mngBW_of_iter : ∀ (r : ℕ) (w : ℝ → ℝ) (M : ℝ) (f : ℝ → Euc d → ℝ), (∀ t, ContDiff ℝ r (f t)) →
    (∀ t, 0 ≤ t → ∀ k ≤ r, ∀ x, ‖iteratedFDeriv ℝ k (f t) x‖ ≤ M * w t) → mngBW r w M f
  | 0, w, M, f, _, h => fun t ht x => by
      have := h t ht 0 le_rfl x
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  | r + 1, w, M, f, hcd, h => by
    refine ⟨fun t ht x => ?_, fun i => ?_⟩
    · have := h t ht 0 (Nat.zero_le _) x
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    · refine mngBW_of_iter r w M (mngPd i f) (fun t => mng_cd_pd (hcd t) i) (fun t ht k hk x => ?_)
      exact (mng_norm_iter_pd_le (hcd t |>.of_le (by exact_mod_cast (by omega : k + 1 ≤ r + 1))) i x).trans
        (h t ht (k + 1) (by omega) x)

end HRS.MS.Mov63

end
