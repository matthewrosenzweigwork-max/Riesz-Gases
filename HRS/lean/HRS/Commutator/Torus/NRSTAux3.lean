import HRS.Commutator.Torus.NRSTAux2
import HRS.Kernel.GradBasic

/-!
# NRS-T, part 3: Lipschitz bounds for trigonometric polynomials (`‖∂_a P‖_∞ ≤ L`)
-/

noncomputable section

open scoped BigOperators
open MeasureTheory

namespace HRS.Commutator.TorusNote.NRST

open HRS

variable {d : ℕ}

lemma abs_centeredRep_mk_le (z : Euc d) (i : Fin d) :
    |KernelGrad.centeredRep (Torus.mk z) i| ≤ |z i| := by
  rw [← KernelGrad.norm_apply_eq]
  show ‖((z i : ℝ) : UnitAddCircle)‖ ≤ |z i|
  rw [UnitAddCircle.norm_eq]
  simpa using round_le (z i) 0

lemma tdist_mk_le (a b : Euc d) : KernelGrad.tdist (Torus.mk a) (Torus.mk b) ≤ ‖a - b‖ := by
  have h : Torus.mk a - Torus.mk b = Torus.mk (a - b) := by
    funext i; simp [Torus.mk]
  unfold KernelGrad.tdist
  rw [h, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  refine Real.sqrt_le_sqrt (Finset.sum_le_sum fun i _ => ?_)
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  have := abs_centeredRep_mk_le (a - b) i
  have h0 := abs_nonneg (KernelGrad.centeredRep (Torus.mk (a - b)) i)
  simpa using pow_le_pow_left₀ h0 this 2

/-- Derivative of a mode along the `a`-th coordinate line. -/
lemma hasDerivAt_mode_line (k : Lattice d) (y : Euc d) (a : Fin d) :
    HasDerivAt (fun t : ℝ => Torus.mode k (Torus.mk (y + t • EuclideanSpace.single a (1 : ℝ))))
      (2 * Real.pi * Complex.I * ((k a : ℤ) : ℂ) * Torus.mode k (Torus.mk y)) 0 := by
  have hdot : ∀ t : ℝ, Lattice.dot k (y + t • EuclideanSpace.single a (1 : ℝ)) =
      Lattice.dot k y + t * (k a : ℝ) := by
    intro t
    rw [Torus.dot_add, Torus.dot_smul]
    congr 2
    simp [Lattice.dot, EuclideanSpace.single_apply]
  have h1 : HasDerivAt (fun t : ℝ => ((2 * Real.pi * (Lattice.dot k y + t * (k a : ℝ)) : ℝ) : ℂ) * Complex.I)
      (((2 * Real.pi * (k a : ℝ) : ℝ) : ℂ) * Complex.I) 0 := by
    have : HasDerivAt (fun t : ℝ => 2 * Real.pi * (Lattice.dot k y + t * (k a : ℝ)))
        (2 * Real.pi * (k a : ℝ)) 0 := by
      have := (((hasDerivAt_id (0 : ℝ)).mul_const (k a : ℝ)).const_add (Lattice.dot k y)).const_mul (2 * Real.pi)
      simpa using this
    exact (this.ofReal_comp).mul_const Complex.I
  have h2 := h1.cexp
  have e : (fun t : ℝ => Torus.mode k (Torus.mk (y + t • EuclideanSpace.single a (1 : ℝ)))) =
      fun t : ℝ => Complex.exp (((2 * Real.pi * (Lattice.dot k y + t * (k a : ℝ)) : ℝ) : ℂ) * Complex.I) := by
    funext t; rw [Torus.mode_mk, hdot]
  rw [e]
  convert h2 using 1
  rw [Torus.mode_mk]
  simp
  ring

lemma supp_dd_subset (a : Fin d) (f : TPA d) : (dd a f).coeff.support ⊆ f.coeff.support :=
  supp_mulSeq_subset _ f

lemma ev_dd_apply (a : Fin d) (f : TPA d) (x : Torus d) :
    ev (dd a f) x = ∑ k ∈ f.coeff.support,
      (2 * Real.pi * Complex.I * ((k a : ℤ) : ℂ) * f.coeff k) * Torus.mode k x := by
  rw [ev_apply_sum]
  rw [Finset.sum_subset (supp_dd_subset a f) (fun k _ hk => by
    have : (dd a f).coeff k = 0 := by simpa using hk
    simp [this])]
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_dd]

lemma hasDerivAt_ev_line (f : TPA d) (y : Euc d) (a : Fin d) :
    HasDerivAt (fun t : ℝ => ev f (Torus.mk (y + t • EuclideanSpace.single a (1 : ℝ))))
      (ev (dd a f) (Torus.mk y)) 0 := by
  have h := HasDerivAt.fun_sum (u := f.coeff.support) (fun k _ =>
    (hasDerivAt_mode_line k y a).const_mul (f.coeff k))
  have e1 : (fun t : ℝ => ev f (Torus.mk (y + t • EuclideanSpace.single a (1 : ℝ)))) =
      fun t : ℝ => ∑ k ∈ f.coeff.support,
        f.coeff k * Torus.mode k (Torus.mk (y + t • EuclideanSpace.single a (1 : ℝ))) :=
    funext fun t => ev_apply_sum f _
  rw [e1, ev_dd_apply]
  convert h using 1
  refine Finset.sum_congr rfl fun k _ => ?_
  ring

lemma norm_ev_dd_le (f : TPA d) {L : ℝ} (hL0 : 0 ≤ L)
    (hL : ∀ x y : Torus d, ‖ev f x - ev f y‖ ≤ L * KernelGrad.tdist x y) (a : Fin d) (x : Torus d) :
    ‖ev (dd a f) x‖ ≤ L := by
  obtain ⟨y, rfl⟩ : ∃ y : Euc d, Torus.mk y = x := ⟨Torus.rep x, Torus.mk_rep x⟩
  set e : Euc d := EuclideanSpace.single a (1 : ℝ) with he
  set φ : ℝ → ℂ := fun t => ev f (Torus.mk (y + t • e)) with hφ
  have hlip : LipschitzWith L.toNNReal φ := by
    refine LipschitzWith.of_dist_le_mul fun t s => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ hL0]
    refine (hL _ _).trans ?_
    refine mul_le_mul_of_nonneg_left ((tdist_mk_le _ _).trans ?_) hL0
    have : y + t • e - (y + s • e) = (t - s) • e := by
      rw [add_sub_add_left_eq_sub, sub_smul]
    rw [this, norm_smul, he, PiLp.norm_single]
    simp
  have := norm_deriv_le_of_lipschitz hlip (x₀ := (0 : ℝ))
  rw [(hasDerivAt_ev_line f y a).deriv] at this
  simpa [Real.coe_toNNReal _ hL0] using this

lemma pr_eq_integral (f g : TPA d) : pr f g = ∫ x, ev f x * ev g x := by
  have := integral_ev (f * g)
  rw [ev_mul] at this
  rw [pr]
  simpa using this.symm

/-- zero mode removed. -/
lemma lam_zero_coeff (h : TPA d) (k : Lattice d) :
    (lam 0 h).coeff k = if k = 0 then 0 else h.coeff k := by
  rw [coeff_lam]
  by_cases hk : k = 0
  · simp [hk, lw_zero]
  · simp [hk, lw, Real.rpow_zero]

lemma dd_lam_zero (c : Fin d) (h : TPA d) : dd c (lam 0 h) = dd c h := by
  rw [← AddMonoidAlgebra.coeff_inj]
  ext k
  rw [coeff_dd, coeff_dd, lam_zero_coeff]
  by_cases hk : k = 0
  · simp [hk]
  · simp [hk]

lemma nsq_lam_zero (h : TPA d) :
    ∑ k ∈ (lam 0 h).coeff.support, ‖(lam 0 h).coeff k‖ ^ 2 = hom 0 h := by
  have hs : (lam 0 h).coeff.support ⊆ h.coeff.support := supp_mulSeq_subset _ h
  rw [Finset.sum_subset hs (fun k _ hk => by
    have : (lam 0 h).coeff k = 0 := by simpa using hk
    simp [this])]
  unfold hom
  refine Finset.sum_congr rfl fun k _ => ?_
  rw [coeff_lam, norm_mul, Complex.norm_real, Real.norm_eq_abs, abs_of_nonneg (lw_nonneg _ _), mul_pow]

lemma pr_key (V h : TPA d) (c : Fin d) :
    pr (dd c V) (h * h) = -2 * pr h (V * dd c h) := by
  rw [pr_dd, dd_mul, pr_add_right]
  have h1 : pr V (dd c h * h) = pr V (h * dd c h) := by rw [mul_comm]
  have h2 : pr V (h * dd c h) = pr h (V * dd c h) := by
    unfold pr; rw [mul_left_comm]
  rw [h1, h2]; ring

theorem base_zero (V : Fin d → TPA d) {M : ℝ} (hM : 0 ≤ M)
    (hMV : ∀ (c : Fin d) (x : Torus d), ‖ev (dd c (V c)) x‖ ≤ M) (h : TPA d) :
    ‖Jf V 0 h‖ ≤ ((d : ℝ) * M / 2) * hom 0 h := by
  set h' := lam 0 h with hh'
  have e1 : Jf V 0 h = ∑ c, pr h' (V c * dd c h') := by
    unfold Jf adv
    rw [pr_sum_right]
    refine Finset.sum_congr rfl fun c _ => ?_
    rw [dd_lam_zero]
  have e2 : ∀ c : Fin d, pr h' (V c * dd c h') = -(1 / 2 : ℂ) * pr (dd c (V c)) (h' * h') := by
    intro c; rw [pr_key]; ring
  have e3 : ∀ c : Fin d, ‖pr (dd c (V c)) (h' * h')‖ ≤ M * hom 0 h := by
    intro c
    rw [pr_eq_integral, ev_mul]
    have hc : Continuous (ev h') := continuous_ev h'
    have hint : Integrable (fun x => ‖ev h' x‖ ^ 2) :=
      ((continuous_norm.comp hc).pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    calc ‖∫ x, ev (dd c (V c)) x * (ev h' * ev h') x‖
        ≤ ∫ x, ‖ev (dd c (V c)) x * (ev h' * ev h') x‖ := norm_integral_le_integral_norm _
      _ ≤ ∫ x, M * ‖ev h' x‖ ^ 2 := by
          refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun x => norm_nonneg _)
            (hint.const_mul M) (Filter.Eventually.of_forall fun x => ?_)
          dsimp only
          rw [norm_mul, Pi.mul_apply, norm_mul, ← sq]
          exact mul_le_mul_of_nonneg_right (hMV c x) (sq_nonneg _)
      _ = M * hom 0 h := by
          rw [integral_const_mul, integral_ev_mul_conj, nsq_lam_zero]
  rw [e1]
  simp_rw [e2]
  calc ‖∑ c, -(1 / 2 : ℂ) * pr (dd c (V c)) (h' * h')‖
      ≤ ∑ c : Fin d, ‖-(1 / 2 : ℂ) * pr (dd c (V c)) (h' * h')‖ := norm_sum_le _ _
    _ ≤ ∑ c : Fin d, (1 / 2) * (M * hom 0 h) := by
        refine Finset.sum_le_sum fun c _ => ?_
        rw [norm_mul]
        simp only [norm_neg, norm_div, norm_one, Complex.norm_ofNat]
        exact mul_le_mul_of_nonneg_left (e3 c) (by norm_num)
    _ = ((d : ℝ) * M / 2) * hom 0 h := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        ring

end HRS.Commutator.TorusNote.NRST
