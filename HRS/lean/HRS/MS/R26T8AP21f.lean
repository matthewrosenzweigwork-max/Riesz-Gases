import HRS.MS.R26T8AP21e

/-!
# S8.2 local Newton layer, packet T8A.P21 (part f): nested jets of `u_m(tau)`
`u_m(tau)(Y,w) = D^m f(Y+tau w)(w,...,w)` is the `curryFin0` image of the `m`-fold contraction of `D^m f (Y + tau w)`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82

section U

variable {E : Type} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem r26t8a_contrIter_apply : ∀ (j : ℕ) (G : E × E → r26t8a_Mult E (0 + j)) (Yw : E × E) (v : Fin 0 → E),
    r26t8a_contrIter j G Yw v = G Yw (fun _ => Yw.2)
  | 0, G, Yw, v => by
    show G Yw v = G Yw (fun _ => Yw.2)
    congr 1
    funext i
    exact Fin.elim0 i
  | j + 1, G, Yw, v => by
    show r26t8a_contrIter j (r26t8a_contr G) Yw v = _
    rw [r26t8a_contrIter_apply j (r26t8a_contr G) Yw v]
    show (r26t8a_contrCLM E (0 + j) Yw.2 (G Yw)) (fun _ => Yw.2) = _
    rw [r26t8a_contrCLM_apply, ContinuousMultilinearMap.curryLeft_apply]
    congr 1
    funext i
    refine Fin.cases rfl (fun _ => rfl) i

end U

section UD

variable {d : ℕ}

/-- `u_m` as the `curryFin0` image of the `m`-fold contraction. -/
theorem r26t8a_u_eq (f : Euc d → ℝ) (m : ℕ) (τ : ℝ) :
    (fun Yw : Euc d × Euc d => r26t8a_u f Yw.1 Yw.2 (0 + m) τ) = fun Yw =>
      continuousMultilinearCurryFin0 ℝ (Euc d) ℝ (r26t8a_contrIter m (n := 0)
        (fun Yw : Euc d × Euc d => iteratedFDeriv ℝ (0 + m) f (Yw.1 + τ • Yw.2)) Yw) := by
  funext Yw
  rw [continuousMultilinearCurryFin0_apply, r26t8a_contrIter_apply]
  rfl

theorem r26t8a_curry0_norm : ‖(continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).toLinearIsometry.toContinuousLinearMap‖ ≤ 1 :=
  LinearIsometry.norm_toContinuousLinearMap_le _

theorem r26t8a_G0_contDiff {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) (τ : ℝ) (N : ℕ) :
    ContDiff ℝ (N : WithTop ℕ∞) (fun Yw : Euc d × Euc d => iteratedFDeriv ℝ (0 + m) f (Yw.1 + τ • Yw.2)) :=
  ((hf.iteratedFDeriv_right (m := (N : WithTop ℕ∞)) (by exact_mod_cast le_top))).comp
    (contDiff_fst.add (contDiff_snd.const_smul τ))

theorem r26t8a_u_joint_contDiff {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) (m : ℕ) (τ : ℝ) (N : ℕ) :
    ContDiff ℝ (N : WithTop ℕ∞) (fun Yw : Euc d × Euc d => r26t8a_u f Yw.1 Yw.2 (0 + m) τ) := by
  rw [r26t8a_u_eq]
  exact (continuousMultilinearCurryFin0 ℝ (Euc d) ℝ).toLinearIsometry.toContinuousLinearMap.contDiff.comp
    (r26t8a_contrIter_contDiff m _ (r26t8a_G0_contDiff hf m τ N))

theorem r26t8a_G0_nest {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {k : ℕ} {A : ℝ}
    (hA : ∀ j, 1 ≤ j → j ≤ k + 4 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A) (m : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (τ : ℝ) (hτ : |τ| ≤ 1) (p q : ℕ) (hpq : p + q ≤ k) (X z : Euc d) :
    ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => iteratedFDeriv ℝ (0 + m) f (Yw.1 + τ • Yw.2)) X z‖ ≤ A := by
  have hg : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞) (iteratedFDeriv ℝ (0 + m) f) :=
    hf.iteratedFDeriv_right (by exact_mod_cast le_top)
  refine (r26t8a_nest_affine q p (iteratedFDeriv ℝ (0 + m) f) τ X z hg).trans ?_
  rw [r26t8a_norm_iter_iter]
  have h1 : |τ| ^ q ≤ 1 := pow_le_one₀ (abs_nonneg _) hτ
  have h2 := hA (p + q + (0 + m)) (by omega) (by omega) (X + τ • z)
  have hA0 : 0 ≤ A := (norm_nonneg _).trans h2
  calc |τ| ^ q * ‖iteratedFDeriv ℝ (p + q + (0 + m)) f (X + τ • z)‖ ≤ 1 * A :=
        mul_le_mul h1 h2 (norm_nonneg _) zero_le_one
    _ = A := one_mul A

theorem r26t8a_nest_u_small {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {k : ℕ} {A : ℝ}
    (hA : ∀ j, 1 ≤ j → j ≤ k + 4 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A) (m : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (τ : ℝ) (hτ : |τ| ≤ 1) (p q : ℕ) (hpq : p + q ≤ k) (X z : Euc d) (hz : ‖z‖ ≤ 1) :
    ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_u f Yw.1 Yw.2 (0 + m) τ) X z‖ ≤
      A * ((q : ℝ) + 1) ^ m * ‖z‖ ^ (m - q) := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1 le_rfl (by omega) 0)
  have hch := r26t8a_chain_small (E := Euc d) k p hA0 X z hz m (n := 0) 0 0
    (fun Yw : Euc d × Euc d => iteratedFDeriv ℝ (0 + m) f (Yw.1 + τ • Yw.2))
    (r26t8a_G0_contDiff hf m τ k)
    (fun q hq => by
      have := r26t8a_G0_nest hf hA m hm1 hm4 τ hτ p q (by omega) X z
      simpa using this) q hpq
  rw [r26t8a_u_eq]
  have hcd : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
      (r26t8a_contrIter m (n := 0) (fun Yw : Euc d × Euc d => iteratedFDeriv ℝ (0 + m) f (Yw.1 + τ • Yw.2))) :=
    r26t8a_contrIter_contDiff m _ (r26t8a_G0_contDiff hf m τ (p + q))
  have := r26t8a_nest_clm (E := Euc d) _ r26t8a_curry0_norm p q _ X z hcd
  refine this.trans ?_
  simpa using hch

theorem r26t8a_nest_u_large {f : Euc d → ℝ} (hf : ContDiff ℝ ∞ f) {k : ℕ} {A : ℝ}
    (hA : ∀ j, 1 ≤ j → j ≤ k + 4 → ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ A) (m : ℕ) (hm1 : 1 ≤ m) (hm4 : m ≤ 4)
    (τ : ℝ) (hτ : |τ| ≤ 1) (p q : ℕ) (hpq : p + q ≤ k) (X z : Euc d) :
    ‖r26t8a_nest p q (fun Yw : Euc d × Euc d => r26t8a_u f Yw.1 Yw.2 (0 + m) τ) X z‖ ≤
      A * ((q : ℝ) + 1) ^ m * (1 + ‖z‖) ^ m := by
  have hA0 : 0 ≤ A := (norm_nonneg _).trans (hA 1 le_rfl (by omega) 0)
  have hch := r26t8a_chain_large (E := Euc d) k p hA0 X z m (n := 0) 0 0
    (fun Yw : Euc d × Euc d => iteratedFDeriv ℝ (0 + m) f (Yw.1 + τ • Yw.2))
    (r26t8a_G0_contDiff hf m τ k)
    (fun q hq => by
      have := r26t8a_G0_nest hf hA m hm1 hm4 τ hτ p q (by omega) X z
      simpa using this) q hpq
  rw [r26t8a_u_eq]
  have hcd : ContDiff ℝ ((p + q : ℕ) : WithTop ℕ∞)
      (r26t8a_contrIter m (n := 0) (fun Yw : Euc d × Euc d => iteratedFDeriv ℝ (0 + m) f (Yw.1 + τ • Yw.2))) :=
    r26t8a_contrIter_contDiff m _ (r26t8a_G0_contDiff hf m τ (p + q))
  have := r26t8a_nest_clm (E := Euc d) _ r26t8a_curry0_norm p q _ X z hcd
  refine this.trans ?_
  simpa using hch

end UD


end HRS.MS.R26T8A
