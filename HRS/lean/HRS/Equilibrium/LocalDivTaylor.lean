import HRS.Equilibrium.LocalDivAux
import HRS.Equilibrium.StaticLimitsAux
import HRS.Kernel.GradConv
/-! Taylor expansion of the pair transport kernel (helpers for Proposition 7.17). -/
open MeasureTheory Set Metric
noncomputable section
namespace HRS.LocalDivAux
variable {d : ℕ}

theorem mk_add' (a b : Euc d) : Torus.mk (a + b) = Torus.mk a + Torus.mk b := by
  funext i; simp [Torus.mk]

theorem mk_zero' : Torus.mk (0 : Euc d) = 0 := by
  funext i; simp [Torus.mk]

theorem isSmooth_partialDeriv {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (i : Fin d) :
    Torus.IsSmooth (Torus.partialDeriv i f) := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
  have h1 : Torus.IsCk 1 f := ContDiff.of_le hF (by norm_cast)
  unfold Torus.IsSmooth Torus.IsCk
  rw [HRS.PDE.lift_partialDeriv i f h1]
  exact (hF.fderiv_right (by simp)).clm_apply contDiff_const

theorem fderiv_lift_periodic (f : Torus d → ℝ) (w : Euc d) (n : Lattice d) :
    fderiv ℝ (Torus.lift f) (w + Lattice.toEuc n) = fderiv ℝ (Torus.lift f) w := by
  have hp : (fun x => Torus.lift f (x + Lattice.toEuc n)) = Torus.lift f :=
    funext fun x => Torus.lift_periodic f x n
  rw [← fderiv_comp_add_right (Lattice.toEuc n) (f := Torus.lift f) (x := w), hp]

theorem lift_mk_add (f : Torus d → ℝ) (x : Torus d) (w : Euc d) :
    Torus.lift f (Torus.rep x + w) = f (x + Torus.mk w) := by
  simp [Torus.lift, mk_add', Torus.mk_rep]

theorem taylor_one {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (x : Torus d) (w : Euc d),
      |f (x + Torus.mk w) - f x - ∑ j, Torus.partialDeriv j f x * w j| ≤ L * ‖w‖ ^ 2 := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
  have hF1 : ContDiff ℝ 1 (fderiv ℝ (Torus.lift f)) := hF.fderiv_right (by simp)
  obtain ⟨L, hL⟩ := HRS.rem_exists_lipschitz_of_periodic (fderiv ℝ (Torus.lift f)) hF1
    (fun w n => fderiv_lift_periodic f w n)
  refine ⟨L, L.2, fun x w => ?_⟩
  set a := Torus.rep x with ha
  set g : Euc d → ℝ := fun v => Torus.lift f (a + v) - fderiv ℝ (Torus.lift f) a v with hg
  have hdiff : ∀ v, DifferentiableAt ℝ g v := fun v => by
    refine DifferentiableAt.sub ?_ (ContinuousLinearMap.differentiableAt _)
    exact (differentiableAt_comp_add_left a).2 ((hF.differentiable (by simp)) (a + v))
  have hgd : ∀ v, fderiv ℝ g v = fderiv ℝ (Torus.lift f) (a + v) - fderiv ℝ (Torus.lift f) a := by
    intro v
    have h1 : HasFDerivAt (fun v => Torus.lift f (a + v)) (fderiv ℝ (Torus.lift f) (a + v)) v := by
      exact (hasFDerivAt_comp_add_left a).2 ((hF.differentiable (by simp)) (a + v)).hasFDerivAt
    have h2 : HasFDerivAt (fun v : Euc d => fderiv ℝ (Torus.lift f) a v) (fderiv ℝ (Torus.lift f) a) v :=
      (fderiv ℝ (Torus.lift f) a).hasFDerivAt
    exact (h1.sub h2).fderiv
  have hbound : ∀ v ∈ closedBall (0 : Euc d) ‖w‖, ‖fderiv ℝ g v‖ ≤ L * ‖w‖ := by
    intro v hv
    rw [hgd]
    have := hL.dist_le_mul (a + v) a
    rw [dist_eq_norm, dist_eq_norm] at this
    simp only [add_sub_cancel_left] at this
    have hv' : ‖v‖ ≤ ‖w‖ := by simpa using hv
    calc _ ≤ (L : ℝ) * ‖v‖ := this
      _ ≤ _ := by gcongr
  have key := Convex.norm_image_sub_le_of_norm_fderiv_le (fun v _ => hdiff v) hbound
    (convex_closedBall (0 : Euc d) ‖w‖) (mem_closedBall_self (norm_nonneg w))
    (show w ∈ closedBall (0 : Euc d) ‖w‖ by simp)
  have e0 : g 0 = f x := by simp [hg, ha, Torus.lift, Torus.mk_rep]
  have e := lift_mk_add f x w
  rw [← ha] at e
  have e1 : g w = f (x + Torus.mk w) - fderiv ℝ (Torus.lift f) a w := by
    simp only [hg]; rw [e]
  have e2 : fderiv ℝ (Torus.lift f) a w = ∑ j, Torus.partialDeriv j f x * w j := by
    have hw : w = ∑ j, w j • (EuclideanSpace.single j (1 : ℝ) : Euc d) := by
      ext k; simp [Finset.sum_apply, Pi.single_apply]
    conv_lhs => rw [hw]
    simp only [map_sum, map_smul, smul_eq_mul]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [Torus.partialDeriv, ha]; ring
  have e3 : g w - g 0 = f (x + Torus.mk w) - f x - ∑ j, Torus.partialDeriv j f x * w j := by
    rw [e0, e1, e2]; ring
  rw [← e3, ← Real.norm_eq_abs]
  calc ‖g w - g 0‖ ≤ L * ‖w‖ * ‖w - 0‖ := key
    _ = _ := by simp; ring


theorem fderiv_rep_apply (f : Torus d → ℝ) (x : Torus d) (v : Euc d) :
    fderiv ℝ (Torus.lift f) (Torus.rep x) v = ∑ j, Torus.partialDeriv j f x * v j := by
  have hw : v = ∑ j, v j • (EuclideanSpace.single j (1 : ℝ) : Euc d) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hw]
  simp only [map_sum, map_smul, smul_eq_mul]
  refine Finset.sum_congr rfl fun j _ => ?_
  simp only [Torus.partialDeriv]; ring

theorem hTransport_eq (s : ℝ) (f : Torus d → ℝ) (hf : Torus.IsSmooth f) (x y : Torus d) :
    hTransport d s f x y = ∑ i, (Torus.partialDeriv i f x - Torus.partialDeriv i f y) *
      (periodicRieszGrad d s (x - y)) i := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
  have hdiff : Differentiable ℝ (Torus.lift f) := hF.differentiable (by simp)
  unfold hTransport Torus.grad
  rw [inner_sub_left, inner_gradient_left, inner_gradient_left, fderiv_rep_apply, fderiv_rep_apply,
    ← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl fun i _ => ?_
  ring


theorem hTransport_shift {s : ℝ} (hsd : s < d) (f : Torus d → ℝ) (hf : Torus.IsSmooth f)
    (x : Torus d) (w : Euc d) :
    hTransport d s f x (x + Torus.mk w) = ∑ i, (Torus.partialDeriv i f (x + Torus.mk w) -
      Torus.partialDeriv i f x) * (periodicRieszGrad d s (Torus.mk w)) i := by
  rw [hTransport_eq s f hf]
  have e : x - (x + Torus.mk w) = -Torus.mk w := by abel
  rw [e, HRS.PDE.periodicRieszGrad_neg hsd]
  refine Finset.sum_congr rfl fun i _ => ?_
  simp only [PiLp.neg_apply]; ring

/-- Hessian matrix, `H i j = ∂_j ∂_i f`. -/
def hess (f : Torus d → ℝ) (x : Torus d) : Matrix (Fin d) (Fin d) ℝ :=
  fun i j => Torus.partialDeriv j (Torus.partialDeriv i f) x

theorem partialDeriv_partialDeriv_mixed (i j : Fin d) (φ : Torus d → ℝ) (hφ : Torus.IsCk 2 φ)
    (x : Torus d) :
    Torus.partialDeriv i (Torus.partialDeriv j φ) x =
      fderiv ℝ (fderiv ℝ (Torus.lift φ)) (Torus.rep x) (EuclideanSpace.single i 1)
        (EuclideanSpace.single j 1) := by
  have h1 : Torus.IsCk 1 φ := hφ.of_le (by norm_num)
  have hd : DifferentiableAt ℝ (fderiv ℝ (Torus.lift φ)) (Torus.rep x) :=
    ((hφ.fderiv_right (by norm_num) : ContDiff ℝ 1 (fderiv ℝ (Torus.lift φ)))).differentiable
      one_ne_zero _
  have e : Torus.partialDeriv i (Torus.partialDeriv j φ) x =
      fderiv ℝ (Torus.lift (Torus.partialDeriv j φ)) (Torus.rep x) (EuclideanSpace.single i 1) := rfl
  rw [e, HRS.PDE.lift_partialDeriv j φ h1, fderiv_clm_apply hd (differentiableAt_const _)]
  simp

theorem partialDeriv_comm {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (i j : Fin d) (x : Torus d) :
    Torus.partialDeriv i (Torus.partialDeriv j f) x = Torus.partialDeriv j (Torus.partialDeriv i f) x := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) := hf
  have h2 : Torus.IsCk 2 f := StaticLimitsAux.isCk_two_of_smooth hf
  rw [partialDeriv_partialDeriv_mixed i j f h2, partialDeriv_partialDeriv_mixed j i f h2]
  have hsym := (hF.contDiffAt (x := Torus.rep x)).isSymmSndFDerivAt (by simp [minSmoothness])
  exact hsym _ _

theorem hess_isHermitian {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (x : Torus d) :
    (hess f x).IsHermitian := by
  ext i j
  simp only [Matrix.conjTranspose_apply, hess, star_trivial]
  exact partialDeriv_comm hf i j x


theorem kernel_remainder_bound {r : Torus d → Euc d} (hr : Torus.IsSmooth r) (hr0 : r 0 = 0) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ w : Euc d, ‖r (Torus.mk w)‖ ≤ L * ‖w‖ := by
  have hF : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift r) := hr
  obtain ⟨L, hL⟩ := HRS.rem_exists_lipschitz_of_periodic (Torus.lift r)
    (hF.of_le (by norm_cast)) (fun w n => Torus.lift_periodic r w n)
  refine ⟨L, L.2, fun w => ?_⟩
  have := hL.dist_le_mul w 0
  rw [dist_eq_norm, dist_eq_norm] at this
  have h0 : r (Torus.mk (0 : Euc d)) = 0 := by rw [mk_zero']; exact hr0
  simpa [h0, Torus.lift] using this

theorem isCk_one_of_smooth {f : Torus d → ℝ} (hf : Torus.IsSmooth f) : Torus.IsCk 1 f :=
  ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift f) from hf) (by norm_cast)

theorem continuous_hess_entry {f : Torus d → ℝ} (hf : Torus.IsSmooth f) (i j : Fin d) :
    Continuous (fun x => hess f x i j) :=
  StaticLimitsAux.continuous_partialDeriv (isCk_one_of_smooth (isSmooth_partialDeriv hf i)) j

theorem hess_bound {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ x i j, |hess f x i j| ≤ B := by
  have h : ∀ i j : Fin d, ∃ B : ℝ, 0 ≤ B ∧ ∀ x, |hess f x i j| ≤ B := by
    intro i j
    obtain ⟨C, hC⟩ := isCompact_univ.exists_bound_of_continuousOn
      (continuous_hess_entry hf i j).continuousOn
    refine ⟨max C 0, le_max_right _ _, fun x => ?_⟩
    have := hC x (mem_univ x)
    rw [Real.norm_eq_abs] at this
    exact this.trans (le_max_left _ _)
  choose B hB0 hB using h
  refine ⟨∑ i, ∑ j, B i j, Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => hB0 i j,
    fun x i j => (hB i j x).trans ?_⟩
  calc B i j ≤ ∑ j', B i j' :=
        Finset.single_le_sum (f := fun j' => B i j') (fun j' _ => hB0 i j') (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', B i' j' :=
        Finset.single_le_sum (f := fun i' => ∑ j', B i' j')
          (fun i' _ => Finset.sum_nonneg fun j' _ => hB0 i' j') (Finset.mem_univ i)


theorem taylor_all {f : Torus d → ℝ} (hf : Torus.IsSmooth f) :
    ∃ L : ℝ, 0 ≤ L ∧ ∀ (i : Fin d) (x : Torus d) (w : Euc d),
      |Torus.partialDeriv i f (x + Torus.mk w) - Torus.partialDeriv i f x -
        ∑ j, hess f x i j * w j| ≤ L * ‖w‖ ^ 2 := by
  have hTay : ∀ i : Fin d, ∃ L : ℝ, 0 ≤ L ∧ ∀ (x : Torus d) (w : Euc d),
      |Torus.partialDeriv i f (x + Torus.mk w) - Torus.partialDeriv i f x -
        ∑ j, hess f x i j * w j| ≤ L * ‖w‖ ^ 2 := fun i => taylor_one (isSmooth_partialDeriv hf i)
  choose Li hLi0 hLi using hTay
  refine ⟨∑ i, Li i, Finset.sum_nonneg fun i _ => hLi0 i, fun i x w => (hLi i x w).trans ?_⟩
  exact mul_le_mul_of_nonneg_right (Finset.single_le_sum (f := Li) (fun i _ => hLi0 i)
    (Finset.mem_univ i)) (sq_nonneg _)

theorem rieszRadial_le {s : ℝ} (hs0 : 0 ≤ s) {w : Euc d} (hw : 0 < ‖w‖) :
    rieszRadial s w ≤ (s + 1) * ‖w‖ ^ (-s - 2) := by
  unfold rieszRadial
  have hp : 0 < ‖w‖ ^ (-s - 2) := Real.rpow_pos_of_pos hw _
  split_ifs with h
  · subst h
    simp only [neg_zero, zero_sub, zero_add, one_mul]
    exact le_of_eq rfl
  · exact mul_le_mul_of_nonneg_right (by linarith) hp.le

theorem h_expand {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) :
    ∃ C δ : ℝ, 0 < δ ∧ δ ≤ 1 ∧ ∀ (x : Torus d) (w : Euc d), 0 < ‖w‖ → ‖w‖ < δ →
      |hTransport d s f x (x + Torus.mk w) + rieszRadial s w * quadForm (hess f x) w| ≤
        C * ‖w‖ ^ (1 - s) := by
  obtain ⟨r, δ0, hδ0, hr, hr0, hloc⟩ := periodicRieszGrad_local_singularity hd hs0 hsd
  obtain ⟨Lr, hLr0, hLr⟩ := kernel_remainder_bound hr hr0
  obtain ⟨BH, hBH0, hBH⟩ := hess_bound hf
  obtain ⟨L, hL0, hL⟩ := taylor_all hf
  refine ⟨(d : ℝ) ^ 2 * BH * Lr + d * L * (s + 1) + d * L * Lr, min δ0 1, lt_min hδ0 one_pos,
    min_le_right _ _, fun x w hw0 hwδ => ?_⟩
  have hwδ0 : ‖w‖ < δ0 := lt_of_lt_of_le hwδ (min_le_left _ _)
  have hw1 : ‖w‖ ≤ 1 := (lt_of_lt_of_le hwδ (min_le_right _ _)).le
  set ρ := ‖w‖ with hρ
  have hw_ne : w ≠ 0 := norm_pos_iff.1 hw0
  have hK : ∀ i, (periodicRieszGrad d s (Torus.mk w)) i =
      -(rieszRadial s w) * w i + r (Torus.mk w) i := by
    intro i
    rw [hloc w hwδ0 hw_ne]
    simp [eucRieszGrad]
  rw [hTransport_shift hsd f hf x w]
  set a := rieszRadial s w with ha
  set Rr := r (Torus.mk w) with hRr
  set Rem : Fin d → ℝ := fun i => Torus.partialDeriv i f (x + Torus.mk w) - Torus.partialDeriv i f x -
        ∑ j, hess f x i j * w j with hRem
  have hdec : ∀ i, Torus.partialDeriv i f (x + Torus.mk w) - Torus.partialDeriv i f x =
      (∑ j, hess f x i j * w j) + Rem i := fun i => by simp only [hRem]; ring
  set A : Fin d → ℝ := fun i => ∑ j, hess f x i j * w j with hA
  set q := quadForm (hess f x) w with hq
  have hApos : 0 ≤ a := (rieszRadial_pos hs0 hw_ne).le
  have hsumq : ∑ i, A i * w i = q := by
    simp only [hA, hq, quadForm, Finset.sum_mul]
    refine Finset.sum_congr rfl fun i _ => Finset.sum_congr rfl fun j _ => by ring
  have key : ∑ i, (Torus.partialDeriv i f (x + Torus.mk w) - Torus.partialDeriv i f x) *
        (periodicRieszGrad d s (Torus.mk w)) i + a * q =
      ∑ i, A i * Rr i + ∑ i, Rem i * (-a * w i) + ∑ i, Rem i * Rr i := by
    have e : ∀ i, (Torus.partialDeriv i f (x + Torus.mk w) - Torus.partialDeriv i f x) *
        (periodicRieszGrad d s (Torus.mk w)) i =
        -a * (A i * w i) + A i * Rr i + Rem i * (-a * w i) + Rem i * Rr i := by
      intro i
      rw [hdec i, hK i]
      ring
    simp_rw [e, Finset.sum_add_distrib, ← Finset.mul_sum, hsumq]
    ring
  rw [key]
  have hwj : ∀ j, |w j| ≤ ρ := fun j => by
    have := PiLp.norm_apply_le w j
    simpa [Real.norm_eq_abs] using this
  have hRri : ∀ i, |Rr i| ≤ Lr * ρ := fun i => by
    have := PiLp.norm_apply_le Rr i
    rw [Real.norm_eq_abs] at this
    exact this.trans (hLr w)
  have hAi : ∀ i, |A i| ≤ d * BH * ρ := fun i => by
    calc |A i| ≤ ∑ j, |hess f x i j * w j| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ j : Fin d, BH * ρ := Finset.sum_le_sum fun j _ => by
          rw [abs_mul]
          exact mul_le_mul (hBH x i j) (hwj j) (abs_nonneg _) hBH0
      _ = d * BH * ρ := by simp [Finset.sum_const]; ring
  have hρ0 : 0 < ρ := hw0
  have b1 : |∑ i, A i * Rr i| ≤ (d : ℝ) ^ 2 * BH * Lr * ρ ^ 2 := by
    calc |∑ i, A i * Rr i| ≤ ∑ i, |A i * Rr i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, (d * BH * ρ) * (Lr * ρ) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul (hAi i) (hRri i) (abs_nonneg _) (by positivity)
      _ = _ := by simp [Finset.sum_const]; ring
  have b2 : |∑ i, Rem i * (-a * w i)| ≤ (d : ℝ) * L * (a * ρ ^ 3) := by
    calc |∑ i, Rem i * (-a * w i)| ≤ ∑ i, |Rem i * (-a * w i)| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, (L * ρ ^ 2) * (a * ρ) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          refine mul_le_mul (hL i x w) ?_ (abs_nonneg _) (by positivity)
          rw [abs_mul, abs_neg, abs_of_nonneg hApos]
          exact mul_le_mul_of_nonneg_left (hwj i) hApos
      _ = _ := by simp [Finset.sum_const]; ring
  have b3 : |∑ i, Rem i * Rr i| ≤ (d : ℝ) * L * Lr * ρ ^ 3 := by
    calc |∑ i, Rem i * Rr i| ≤ ∑ i, |Rem i * Rr i| := Finset.abs_sum_le_sum_abs _ _
      _ ≤ ∑ i : Fin d, (L * ρ ^ 2) * (Lr * ρ) := Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul (hL i x w) (hRri i) (abs_nonneg _) (by positivity)
      _ = _ := by simp [Finset.sum_const]; ring
  -- powers
  have p2 : ρ ^ 2 ≤ ρ ^ (1 - s) := by
    have := Real.rpow_le_rpow_of_exponent_ge hρ0 hw1 (show 1 - s ≤ (2 : ℝ) by linarith)
    rwa [Real.rpow_two] at this
  have p3 : ρ ^ 3 ≤ ρ ^ (1 - s) := by
    have := Real.rpow_le_rpow_of_exponent_ge hρ0 hw1 (show 1 - s ≤ (3 : ℝ) by linarith)
    rwa [show (3 : ℝ) = ((3 : ℕ) : ℝ) by norm_num, Real.rpow_natCast] at this
  have pa : a * ρ ^ 3 ≤ (s + 1) * ρ ^ (1 - s) := by
    have h1 := rieszRadial_le hs0 hw0 (w := w)
    have h2 : ρ ^ (-s - 2) * ρ ^ 3 = ρ ^ (1 - s) := by
      rw [← Real.rpow_natCast ρ 3, ← Real.rpow_add hρ0]
      congr 1; push_cast; ring
    calc a * ρ ^ 3 ≤ (s + 1) * ρ ^ (-s - 2) * ρ ^ 3 :=
          mul_le_mul_of_nonneg_right h1 (by positivity)
      _ = (s + 1) * (ρ ^ (-s - 2) * ρ ^ 3) := by ring
      _ = _ := by rw [h2]
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hs1 : 0 ≤ s + 1 := by linarith
  calc |∑ i, A i * Rr i + ∑ i, Rem i * (-a * w i) + ∑ i, Rem i * Rr i|
      ≤ |∑ i, A i * Rr i| + |∑ i, Rem i * (-a * w i)| + |∑ i, Rem i * Rr i| := abs_add_three _ _ _
    _ ≤ (d : ℝ) ^ 2 * BH * Lr * ρ ^ 2 + (d : ℝ) * L * (a * ρ ^ 3) + (d : ℝ) * L * Lr * ρ ^ 3 := by
        linarith
    _ ≤ (d : ℝ) ^ 2 * BH * Lr * ρ ^ (1 - s) + (d : ℝ) * L * ((s + 1) * ρ ^ (1 - s)) +
          (d : ℝ) * L * Lr * ρ ^ (1 - s) := by
        gcongr
    _ = _ := by ring


theorem norm_le_dim {w : Euc d} (hw : ∀ i, |w i| ≤ 1 / 2) : ‖w‖ ≤ d := by
  rw [EuclideanSpace.norm_eq]
  have : ∑ i, ‖w i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := Finset.sum_le_sum fun i _ => by
    rw [Real.norm_eq_abs]
    have h1 := hw i
    have h0 := abs_nonneg (w i)
    nlinarith
  simp at this
  calc Real.sqrt (∑ i, ‖w i‖ ^ 2) ≤ Real.sqrt d := Real.sqrt_le_sqrt (by simpa using this)
    _ ≤ d := by
      rcases Nat.eq_zero_or_pos d with h | h
      · subst h; simp
      · have h1 : (1 : ℝ) ≤ d := by exact_mod_cast h
        exact Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith⟩
  

theorem h_bound {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {f : Torus d → ℝ}
    (hf : Torus.IsSmooth f) :
    ∃ B : ℝ, 0 ≤ B ∧ ∀ (x : Torus d) (w : Euc d), 0 < ‖w‖ → (∀ i, |w i| ≤ 1 / 2) →
      |hTransport d s f x (x + Torus.mk w)| ≤ B * ‖w‖ ^ (-s) := by
  obtain ⟨CK, hCK⟩ := HRS.KernelGrad.periodicRieszGrad_bound_tdist hd hs0 hsd
  obtain ⟨BH, hBH0, hBH⟩ := hess_bound hf
  obtain ⟨L, hL0, hL⟩ := taylor_all hf
  have hd0 : (0 : ℝ) < d := by exact_mod_cast (by omega : 0 < d)
  set C1 : ℝ := d * BH + L * d with hC1
  refine ⟨d * (C1 * (|CK| * (1 + (d : ℝ) ^ (s + 1)))), by positivity, fun x w hw0 hwc => ?_⟩
  set ρ := ‖w‖ with hρ
  have hρd : ρ ≤ d := norm_le_dim hwc
  have hw_ne : w ≠ 0 := norm_pos_iff.1 hw0
  have hwj : ∀ j, |w j| ≤ ρ := fun j => by
    have := PiLp.norm_apply_le w j
    simpa [Real.norm_eq_abs] using this
  rw [hTransport_shift hsd f hf x w]
  -- kernel bound
  have hmk : Torus.mk w ≠ 0 := by
    intro h
    apply hw_ne
    ext i
    have h1 : ((w i : ℝ) : UnitAddCircle) = 0 := congrFun h i
    rw [AddCircle.coe_eq_zero_iff] at h1
    obtain ⟨n, hn⟩ := h1
    have h2 := hwc i
    rw [← hn] at h2
    simp only [zsmul_eq_mul, mul_one] at h2
    have hn0 : n = 0 := by
      have : |(n : ℝ)| < 1 := by linarith
      have h3 : |n| < 1 := by exact_mod_cast this
      exact Int.abs_lt_one_iff.1 h3
    simp [← hn, hn0]
  have hK := hCK (Torus.mk w) hmk
  have htd : HRS.KernelGrad.tdist (Torus.mk w) 0 = ρ := HRS.KernelGrad.tdist_mk hwc
  rw [htd] at hK
  have hρ0 : 0 < ρ := hw0
  have hKi : ∀ i, |(periodicRieszGrad d s (Torus.mk w)) i| ≤ |CK| * (1 + (d : ℝ) ^ (s + 1)) * ρ ^ (-s - 1) := by
    intro i
    have h1 := PiLp.norm_apply_le (periodicRieszGrad d s (Torus.mk w)) i
    rw [Real.norm_eq_abs] at h1
    refine h1.trans (hK.trans ?_)
    have h2 : 1 ≤ (d : ℝ) ^ (s + 1) * ρ ^ (-s - 1) := by
      have h3 : 1 ≤ ((d : ℝ) / ρ) ^ (s + 1) :=
        Real.one_le_rpow (by rw [le_div_iff₀ hρ0]; linarith) (by linarith)
      have h4 : ((d : ℝ) / ρ) ^ (s + 1) = (d : ℝ) ^ (s + 1) * ρ ^ (-s - 1) := by
        rw [Real.div_rpow hd0.le hρ0.le, div_eq_mul_inv, ← Real.rpow_neg hρ0.le]
        congr 2; ring
      exact h4 ▸ h3
    calc CK * (ρ ^ (-s - 1) + 1) ≤ |CK| * (ρ ^ (-s - 1) + 1) :=
          mul_le_mul_of_nonneg_right (le_abs_self _) (by positivity)
      _ ≤ |CK| * (ρ ^ (-s - 1) + (d : ℝ) ^ (s + 1) * ρ ^ (-s - 1)) := by
          gcongr
      _ = _ := by ring
  have hPi : ∀ i, |Torus.partialDeriv i f (x + Torus.mk w) - Torus.partialDeriv i f x| ≤ C1 * ρ := by
    intro i
    have h1 := hL i x w
    have h2 : |∑ j, hess f x i j * w j| ≤ d * BH * ρ := by
      calc |∑ j, hess f x i j * w j| ≤ ∑ j, |hess f x i j * w j| := Finset.abs_sum_le_sum_abs _ _
        _ ≤ ∑ j : Fin d, BH * ρ := Finset.sum_le_sum fun j _ => by
            rw [abs_mul]
            exact mul_le_mul (hBH x i j) (hwj j) (abs_nonneg _) hBH0
        _ = d * BH * ρ := by simp [Finset.sum_const]; ring
    have h3 : |Torus.partialDeriv i f (x + Torus.mk w) - Torus.partialDeriv i f x| ≤
        |∑ j, hess f x i j * w j| + L * ρ ^ 2 := by
      have := abs_sub_abs_le_abs_sub (Torus.partialDeriv i f (x + Torus.mk w) - Torus.partialDeriv i f x)
        (∑ j, hess f x i j * w j)
      linarith
    have h4 : L * ρ ^ 2 ≤ L * d * ρ := by
      rw [sq]
      have : ρ * ρ ≤ d * ρ := mul_le_mul_of_nonneg_right hρd hρ0.le
      nlinarith
    simp only [hC1]
    nlinarith
  calc |∑ i, (Torus.partialDeriv i f (x + Torus.mk w) - Torus.partialDeriv i f x) *
        (periodicRieszGrad d s (Torus.mk w)) i|
      ≤ ∑ i, |(Torus.partialDeriv i f (x + Torus.mk w) - Torus.partialDeriv i f x) *
        (periodicRieszGrad d s (Torus.mk w)) i| := Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ i : Fin d, (C1 * ρ) * (|CK| * (1 + (d : ℝ) ^ (s + 1)) * ρ ^ (-s - 1)) :=
        Finset.sum_le_sum fun i _ => by
          rw [abs_mul]
          exact mul_le_mul (hPi i) (hKi i) (abs_nonneg _) (by positivity)
    _ = d * (C1 * (|CK| * (1 + (d : ℝ) ^ (s + 1)))) * (ρ * ρ ^ (-s - 1)) := by
        simp [Finset.sum_const]; ring
    _ = _ := by
        have : ρ * ρ ^ (-s - 1) = ρ ^ (-s) := by
          have h := Real.rpow_add hρ0 1 (-s - 1)
          rw [Real.rpow_one] at h
          rw [← h]; congr 1; ring
        rw [this]

end HRS.LocalDivAux
