import HRS.Kernel.GradOp
import HRS.Kernel.GradSmooth

/-!
# Regularity of the cancellation convolution

Auxiliary file of `HRS/Kernel/GradConv.lean`: for a good kernel `G` and `C^{m+1}` `h`, the
cancellation convolution `G * h` is `C^m` with `‖G * h‖_{C^m} ≤ C ‖h‖_{C^{m+1}}`, by induction on
`m`, using `D (G * h) = G * (D h)` (differentiation under the integral sign).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.KernelGrad

variable {d : ℕ}

local notation "∞'" => ((⊤ : ℕ∞) : WithTop ℕ∞)

section Calculus

variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

theorem lift_add_toEuc (φ : Torus d → E) (y : Euc d) (m : Lattice d) :
    Torus.lift φ (y + Lattice.toEuc m) = Torus.lift φ y := by
  simp [Torus.lift, mk_add, mk_toEuc]

theorem iteratedFDeriv_lift_add (φ : Torus d → E) (j : ℕ) (y : Euc d) (m : Lattice d) :
    iteratedFDeriv ℝ j (Torus.lift φ) (y + Lattice.toEuc m) = iteratedFDeriv ℝ j (Torus.lift φ) y := by
  have h : (fun z => Torus.lift φ (z + Lattice.toEuc m)) = Torus.lift φ :=
    funext fun z => lift_add_toEuc φ z m
  have := iteratedFDeriv_comp_add_right (𝕜 := ℝ) (f := Torus.lift φ) j (Lattice.toEuc m) y
  rw [h] at this
  exact this.symm

theorem exists_bound_iteratedFDeriv {φ : Torus d → E} {k : ℕ} (hφ : Torus.IsCk k φ) {j : ℕ}
    (hj : j ≤ k) : ∃ M : ℝ, ∀ y, ‖iteratedFDeriv ℝ j (Torus.lift φ) y‖ ≤ M := by
  have hc : Continuous fun y => ‖iteratedFDeriv ℝ j (Torus.lift φ) y‖ :=
    (hφ.continuous_iteratedFDeriv (by exact_mod_cast hj)).norm
  obtain ⟨M, hM⟩ := (isCompact_closedBall (0 : Euc d) d).exists_bound_of_continuousOn hc.continuousOn
  refine ⟨M, fun y => ?_⟩
  obtain ⟨x, hxm, hxb⟩ := exists_mk_box (Torus.mk y)
  obtain ⟨m, hm⟩ := exists_lattice_of_mk_eq hxm
  have hx : x ∈ Metric.closedBall (0 : Euc d) d := by
    simpa using norm_le_card_of_box hxb
  have h1 := hM x hx
  rw [hm, iteratedFDeriv_lift_add, Real.norm_eq_abs, abs_of_nonneg (norm_nonneg _)] at h1
  exact h1

theorem bddAbove_iteratedFDeriv {φ : Torus d → E} {k : ℕ} (hφ : Torus.IsCk k φ) {j : ℕ}
    (hj : j ≤ k) : BddAbove (range fun x : Euc d => ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖) := by
  obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv hφ hj
  exact ⟨M, by rintro _ ⟨x, rfl⟩; exact hM x⟩

theorem term_nonneg (φ : Torus d → E) (j : ℕ) :
    0 ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ :=
  Real.iSup_nonneg fun _ => norm_nonneg _

theorem norm_le_term {φ : Torus d → E} {k : ℕ} (hφ : Torus.IsCk k φ) {j : ℕ} (hj : j ≤ k)
    (y : Euc d) :
    ‖iteratedFDeriv ℝ j (Torus.lift φ) y‖ ≤ ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ :=
  le_ciSup (bddAbove_iteratedFDeriv hφ hj) y

theorem term_le_cbNorm (φ : Torus d → E) {k j : ℕ} (hj : j ≤ k) :
    ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖ ≤ Torus.cbNorm k φ := by
  unfold Torus.cbNorm
  exact Finset.single_le_sum (f := fun j => ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift φ) x‖)
    (fun j _ => term_nonneg φ j) (Finset.mem_range.mpr (by omega))

theorem norm_iteratedFDeriv_le_cbNorm {φ : Torus d → E} {k : ℕ} (hφ : Torus.IsCk k φ) {j : ℕ}
    (hj : j ≤ k) (y : Euc d) : ‖iteratedFDeriv ℝ j (Torus.lift φ) y‖ ≤ Torus.cbNorm k φ :=
  (norm_le_term hφ hj y).trans (term_le_cbNorm φ hj)

theorem cbNorm_nonneg' (φ : Torus d → E) (k : ℕ) : 0 ≤ Torus.cbNorm k φ :=
  Finset.sum_nonneg fun j _ => term_nonneg φ j

theorem cbNorm_mono {φ : Torus d → E} {k k' : ℕ} (hk : k ≤ k') : Torus.cbNorm k φ ≤ Torus.cbNorm k' φ := by
  unfold Torus.cbNorm
  exact Finset.sum_le_sum_of_subset_of_nonneg (Finset.range_mono (by omega))
    (fun j _ _ => term_nonneg φ j)

end Calculus

/-! ### Derivative of a torus function, as a torus function -/

/-- the derivative of (the lift of) `h`, as a function on the torus -/
def Dtor (h : Torus d → ℝ) (w : Torus d) : Euc d →L[ℝ] ℝ := fderiv ℝ (Torus.lift h) (centeredRep w)

theorem fderiv_lift_add (h : Torus d → ℝ) (y : Euc d) (m : Lattice d) :
    fderiv ℝ (Torus.lift h) (y + Lattice.toEuc m) = fderiv ℝ (Torus.lift h) y := by
  have hf : (fun z => Torus.lift h (z + Lattice.toEuc m)) = Torus.lift h :=
    funext fun z => lift_add_toEuc h z m
  have := fderiv_comp_add_right (𝕜 := ℝ) (f := Torus.lift h) (x := y) (Lattice.toEuc m)
  rw [hf] at this
  exact this.symm

theorem lift_Dtor (h : Torus d → ℝ) : Torus.lift (Dtor h) = fderiv ℝ (Torus.lift h) := by
  funext y
  obtain ⟨m, hm⟩ := exists_lattice_of_mk_eq (mk_centeredRep (Torus.mk y))
  simp only [Torus.lift, Function.comp, Dtor]
  rw [hm]
  exact fderiv_lift_add h y m

theorem isCk_Dtor {h : Torus d → ℝ} {k : ℕ} (hh : Torus.IsCk ((k + 1 : ℕ) : WithTop ℕ∞) h) :
    Torus.IsCk (k : WithTop ℕ∞) (Dtor h) := by
  unfold Torus.IsCk
  rw [lift_Dtor]
  exact hh.fderiv_right (by exact_mod_cast le_rfl)

/-- the directional derivative `∂_v h` as a function on the torus -/
def dirTor (h : Torus d → ℝ) (v : Euc d) (w : Torus d) : ℝ := Dtor h w v

theorem lift_dirTor (h : Torus d → ℝ) (v : Euc d) :
    Torus.lift (dirTor h v) = fun y => fderiv ℝ (Torus.lift h) y v := by
  funext y
  have := congrFun (lift_Dtor h) y
  simp only [Torus.lift, Function.comp] at this ⊢
  simp only [dirTor]
  rw [this]

theorem isCk_dirTor {h : Torus d → ℝ} {k : ℕ} (hh : Torus.IsCk ((k + 1 : ℕ) : WithTop ℕ∞) h)
    (v : Euc d) : Torus.IsCk (k : WithTop ℕ∞) (dirTor h v) := by
  unfold Torus.IsCk
  rw [lift_dirTor]
  have := isCk_Dtor hh
  unfold Torus.IsCk at this
  rw [lift_Dtor] at this
  exact this.clm_apply contDiff_const

theorem cbNorm_Dtor_le {h : Torus d → ℝ} {k : ℕ} (hh : Torus.IsCk ((k + 1 : ℕ) : WithTop ℕ∞) h) :
    Torus.cbNorm k (Dtor h) ≤ Torus.cbNorm (k + 1) h := by
  unfold Torus.cbNorm
  rw [Finset.sum_range_succ' (fun j => ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift h) x‖)]
  have : ∀ j, ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift (Dtor h)) x‖ =
      ⨆ x : Euc d, ‖iteratedFDeriv ℝ (j + 1) (Torus.lift h) x‖ := by
    intro j
    rw [lift_Dtor]
    exact iSup_congr fun x => norm_iteratedFDeriv_fderiv
  simp only [this]
  have := term_nonneg h 0
  linarith

theorem cbNorm_dirTor_le {h : Torus d → ℝ} {k : ℕ} (hh : Torus.IsCk ((k + 1 : ℕ) : WithTop ℕ∞) h)
    {v : Euc d} (hv : ‖v‖ ≤ 1) :
    Torus.cbNorm k (dirTor h v) ≤ Torus.cbNorm (k + 1) h := by
  refine le_trans ?_ (cbNorm_Dtor_le hh)
  unfold Torus.cbNorm
  refine Finset.sum_le_sum fun j hj => ?_
  have hjk : j ≤ k := Nat.lt_succ_iff.mp (Finset.mem_range.mp hj)
  have hD := isCk_Dtor hh
  have hbdd := bddAbove_iteratedFDeriv hD hjk
  refine ciSup_le fun x => ?_
  rw [lift_dirTor]
  have hL : ContDiffAt ℝ (j : WithTop ℕ∞) (fderiv ℝ (Torus.lift h)) x := by
    have := hD
    unfold Torus.IsCk at this
    rw [lift_Dtor] at this
    exact (this.of_le (by exact_mod_cast hjk)).contDiffAt
  have h1 := (ContinuousLinearMap.apply ℝ ℝ v).norm_iteratedFDeriv_comp_left hL (n := j) (by exact_mod_cast le_rfl)
  have h2 : ‖ContinuousLinearMap.apply ℝ ℝ v‖ ≤ ‖v‖ := by
    refine ContinuousLinearMap.opNorm_le_bound _ (norm_nonneg _) fun f => ?_
    simpa [mul_comm] using f.le_opNorm v
  have h3 : ‖iteratedFDeriv ℝ j (fderiv ℝ (Torus.lift h)) x‖ ≤
      ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift (Dtor h)) x‖ := by
    rw [← lift_Dtor]
    exact le_ciSup hbdd x
  calc ‖iteratedFDeriv ℝ j (fun y => (fderiv ℝ (Torus.lift h)) y v) x‖
      = ‖iteratedFDeriv ℝ j ((ContinuousLinearMap.apply ℝ ℝ v) ∘ fderiv ℝ (Torus.lift h)) x‖ := rfl
    _ ≤ ‖ContinuousLinearMap.apply ℝ ℝ v‖ * ‖iteratedFDeriv ℝ j (fderiv ℝ (Torus.lift h)) x‖ := h1
    _ ≤ 1 * ‖iteratedFDeriv ℝ j (fderiv ℝ (Torus.lift h)) x‖ := by
        gcongr; exact h2.trans hv
    _ ≤ _ := by linarith

/-! ### The base estimate and the derivative of the cancellation convolution -/

variable {s C : ℝ} {G : Torus d → Euc d}

theorem isLipschitz_of_fderiv_le {h : Torus d → ℝ} (hh : Torus.IsCk 1 h) {L : ℝ}
    (hL : ∀ y, ‖fderiv ℝ (Torus.lift h) y‖ ≤ L) : IsLipschitz L h := by
  have h1 : Differentiable ℝ (Torus.lift h) := hh.differentiable one_ne_zero
  intro x y
  set r := centeredRep (x - y) with hr
  have hmk : Torus.mk (Torus.rep y + r) = x := by
    rw [mk_add, Torus.mk_rep, hr, mk_centeredRep]; abel
  have := Convex.norm_image_sub_le_of_norm_fderiv_le (f := Torus.lift h) (fun u _ => h1 u)
    (fun u _ => hL u) convex_univ (mem_univ (Torus.rep y)) (mem_univ (Torus.rep y + r))
  have e1 : Torus.lift h (Torus.rep y + r) = h x := by simp [Torus.lift, hmk]
  have e2 : Torus.lift h (Torus.rep y) = h y := by simp [Torus.lift, Torus.mk_rep]
  rw [e1, e2, Real.norm_eq_abs] at this
  rw [add_sub_cancel_left] at this
  rw [tdist_eq_sub_zero, tdist_zero_right]
  exact this

theorem norm_iteratedFDeriv_one' {f : Euc d → ℝ} (y : Euc d) :
    ‖iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f y‖ := by
  rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0), norm_iteratedFDeriv_zero]

theorem GoodKernel.norm_le_cb (hG : GoodKernel d s C G) {h : Torus d → ℝ} (hh : Torus.IsCk 1 h)
    (x : Torus d) :
    ‖convGradConv G h x‖ ≤ max (opM1 d s C) (opM2 s C) * Torus.cbNorm 1 h := by
  have hh' : Torus.IsCk ((1 : ℕ) : WithTop ℕ∞) h := by exact_mod_cast hh
  set S0 := ⨆ y : Euc d, ‖iteratedFDeriv ℝ 0 (Torus.lift h) y‖ with hS0
  set S1 := ⨆ y : Euc d, ‖iteratedFDeriv ℝ 1 (Torus.lift h) y‖ with hS1
  have hS00 : 0 ≤ S0 := term_nonneg h 0
  have hS10 : 0 ≤ S1 := term_nonneg h 1
  have hB : ∀ x, |h x| ≤ S0 := by
    intro x
    obtain ⟨y, hy, _⟩ := exists_mk_box x
    have e : ‖iteratedFDeriv ℝ 0 (Torus.lift h) y‖ = |h x| := by
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs]; simp [Torus.lift, hy]
    rw [← e]
    exact norm_le_term hh' (Nat.zero_le 1) y
  have hL : IsLipschitz S1 h := by
    refine isLipschitz_of_fderiv_le hh fun y => ?_
    have := norm_le_term hh' le_rfl y
    rwa [norm_iteratedFDeriv_one'] at this
  have hbd := hG.bound_op h S0 S1 (isCk_continuous hh).measurable hB hL hS10 hS00 x
  have hcb : Torus.cbNorm 1 h = S0 + S1 := by
    unfold Torus.cbNorm
    rw [Finset.sum_range_succ, Finset.sum_range_one]
  rw [hcb]
  have h1 := opM1_nonneg hG
  have h2 := opM2_nonneg hG
  calc _ ≤ S1 * opM1 d s C + S0 * opM2 s C := hbd
    _ ≤ S1 * max (opM1 d s C) (opM2 s C) + S0 * max (opM1 d s C) (opM2 s C) := by
        gcongr <;> simp
    _ = _ := by ring

/-- the derivative of the integrand `kern` in `x`, as a continuous linear map -/
def kernD (G : Torus d → Euc d) (h : Torus d → ℝ) (y : Euc d) (z : Torus d) : Euc d →L[ℝ] Euc d :=
  if ‖z‖ ≤ 1 / 4 then (Dtor h (Torus.mk y - z) - Dtor h (Torus.mk y)).smulRight (G z)
  else (Dtor h (Torus.mk y - z)).smulRight (G z)

theorem kernD_apply (G : Torus d → Euc d) (h : Torus d → ℝ) (y : Euc d) (z : Torus d) (v : Euc d) :
    kernD G h y z v = kern G (dirTor h v) (Torus.mk y) z := by
  unfold kernD kern dirTor
  split_ifs
  · simp [ContinuousLinearMap.smulRight_apply, sub_smul]
  · simp [ContinuousLinearMap.smulRight_apply]

theorem continuous_Dtor {h : Torus d → ℝ} (hh : Torus.IsCk 1 h) : Continuous (Dtor h) := by
  refine continuous_of_lift ?_
  rw [lift_Dtor]
  exact hh.continuous_fderiv one_ne_zero

theorem norm_iteratedFDeriv_one_gen {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    {f : Euc d → F} (y : Euc d) : ‖iteratedFDeriv ℝ 1 f y‖ = ‖fderiv ℝ f y‖ := by
  rw [← norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (n := 0), norm_iteratedFDeriv_zero]

theorem Dtor_bounded {h : Torus d → ℝ} (hh : Torus.IsCk 2 h) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w, ‖Dtor h w‖ ≤ M := by
  have hψ : Torus.IsCk ((1 : ℕ) : WithTop ℕ∞) (Dtor h) := isCk_Dtor (k := 1) (by exact_mod_cast hh)
  obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv hψ (Nat.zero_le 1)
  refine ⟨max M 0, le_max_right _ _, fun w => ?_⟩
  obtain ⟨y, hy, _⟩ := exists_mk_box w
  have := hM y
  rw [norm_iteratedFDeriv_zero] at this
  simp only [Torus.lift, Function.comp, hy] at this
  exact this.trans (le_max_left _ _)

theorem Dtor_lipschitz {h : Torus d → ℝ} (hh : Torus.IsCk 2 h) :
    ∃ M : ℝ, 0 ≤ M ∧ ∀ w a, ‖Dtor h (w - a) - Dtor h w‖ ≤ M * tdist a 0 := by
  have hψ : Torus.IsCk ((1 : ℕ) : WithTop ℕ∞) (Dtor h) := isCk_Dtor (k := 1) (by exact_mod_cast hh)
  obtain ⟨M, hM⟩ := exists_bound_iteratedFDeriv hψ le_rfl
  have hlift : Torus.lift (Dtor h) = fderiv ℝ (Torus.lift h) := lift_Dtor h
  have hdiff : Differentiable ℝ (fderiv ℝ (Torus.lift h)) := by
    have : ContDiff ℝ 1 (Torus.lift (Dtor h)) := by
      have := hψ; unfold Torus.IsCk at this; exact_mod_cast this
    rw [hlift] at this
    exact this.differentiable one_ne_zero
  have hbd : ∀ y, ‖fderiv ℝ (fderiv ℝ (Torus.lift h)) y‖ ≤ M := by
    intro y
    have := hM y
    rw [hlift, norm_iteratedFDeriv_one_gen] at this
    exact this
  refine ⟨max M 0, le_max_right _ _, fun w a => ?_⟩
  obtain ⟨y, hy, _⟩ := exists_mk_box w
  set c := centeredRep a with hc
  have hmk : w - a = Torus.mk (y - c) := by rw [mk_sub, hy, hc, mk_centeredRep]
  have h1 := Convex.norm_image_sub_le_of_norm_fderiv_le (f := fderiv ℝ (Torus.lift h))
    (fun u _ => hdiff u) (fun u _ => hbd u) convex_univ (mem_univ y) (mem_univ (y - c))
  have e1 : Dtor h (w - a) = fderiv ℝ (Torus.lift h) (y - c) := by
    rw [hmk]; exact congrFun hlift (y - c)
  have e2 : Dtor h w = fderiv ℝ (Torus.lift h) y := by
    rw [← hy]; exact congrFun hlift y
  rw [e1, e2, tdist_zero_right, ← hc]
  have : ‖y - c - y‖ = ‖c‖ := by rw [sub_sub_cancel_left, norm_neg]
  rw [this] at h1
  exact h1.trans (by gcongr; exact le_max_left _ _)

theorem measurable_kernD (hG : GoodKernel d s C G) {h : Torus d → ℝ} (hh : Torus.IsCk 1 h) (y : Euc d) :
    Measurable (kernD G h y) := by
  have hD := continuous_Dtor hh
  have e1 : Continuous fun z : Torus d => Dtor h (Torus.mk y - z) :=
    hD.comp (by fun_prop : Continuous fun z : Torus d => Torus.mk y - z)
  have hsr : Continuous fun p : (Euc d →L[ℝ] ℝ) × Euc d => (p.1.smulRight p.2 : Euc d →L[ℝ] Euc d) :=
    (ContinuousLinearMap.smulRightL ℝ (Euc d) (Euc d)).continuous₂
  unfold kernD
  refine Measurable.ite (measurableSet_le measurable_norm measurable_const) ?_ ?_
  · exact hsr.measurable.comp ((e1.measurable.sub measurable_const).prodMk hG.meas)
  · exact hsr.measurable.comp (e1.measurable.prodMk hG.meas)

theorem hasFDerivAt_kern {h : Torus d → ℝ} (hh : Torus.IsCk 2 h) (y : Euc d) (z : Torus d) :
    HasFDerivAt (fun y : Euc d => kern G h (Torus.mk y) z) (kernD G h y z) y := by
  have hl : Differentiable ℝ (Torus.lift h) := hh.differentiable (by norm_num)
  set c := centeredRep z with hc
  have hmk : ∀ y : Euc d, Torus.mk y - z = Torus.mk (y - c) := by
    intro y; rw [mk_sub, hc, mk_centeredRep]
  have h1 : HasFDerivAt (fun y : Euc d => Torus.lift h (y - c)) (fderiv ℝ (Torus.lift h) (y - c)) y := by
    have := (hl (y - c)).hasFDerivAt.comp y ((hasFDerivAt_id y).sub_const c)
    exact this.congr_fderiv (ContinuousLinearMap.comp_id _)
  have h2 : HasFDerivAt (Torus.lift h) (fderiv ℝ (Torus.lift h) y) y := (hl y).hasFDerivAt
  have hDt : ∀ y : Euc d, Dtor h (Torus.mk y) = fderiv ℝ (Torus.lift h) y :=
    fun y => congrFun (lift_Dtor h) y
  unfold kern kernD
  split_ifs with hz
  · have := (h1.sub h2).smul_const (G z)
    convert this using 1
    · funext y; simp only [hmk, Torus.lift, Function.comp, Pi.sub_apply]
    · rw [hmk, hDt, hDt]
  · have := h1.smul_const (G z)
    convert this using 1
    · funext y; simp only [hmk, Torus.lift, Function.comp]
    · rw [hmk, hDt]

theorem kernD_norm_le (hG : GoodKernel d s C G) {h : Torus d → ℝ} {M1 M2 : ℝ}
    (hM1 : ∀ w, ‖Dtor h w‖ ≤ M1) (hM2 : ∀ w a, ‖Dtor h (w - a) - Dtor h w‖ ≤ M2 * tdist a 0)
    (hM10 : 0 ≤ M1) (hM20 : 0 ≤ M2) (y : Euc d) {z : Torus d} (hz : z ≠ 0) :
    ‖kernD G h y z‖ ≤ dom s C M2 M1 d z := by
  have hz0 : 0 < ‖z‖ := norm_pos_iff.mpr hz
  have hC0 := hG.hC0
  have hC := hG.bound_norm
  have hC' := hG.norm_mul_tdist_le
  have hpos1 : 0 ≤ M2 * C * (‖z‖ ^ (-s) + d) := by positivity
  have hpos2 : 0 ≤ M1 * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1) := by positivity
  unfold kernD dom
  split_ifs with hcube
  · rw [ContinuousLinearMap.norm_smulRight_apply]
    have h1 := hM2 (Torus.mk y) z
    calc ‖Dtor h (Torus.mk y - z) - Dtor h (Torus.mk y)‖ * ‖G z‖ ≤ (M2 * tdist z 0) * ‖G z‖ := by gcongr
      _ = M2 * (tdist z 0 * ‖G z‖) := by ring
      _ ≤ M2 * (C * (‖z‖ ^ (-s) + d)) := mul_le_mul_of_nonneg_left (hC' z hz) hM20
      _ = M2 * C * (‖z‖ ^ (-s) + d) := by ring
      _ ≤ _ := by linarith
  · push Not at hcube
    rw [ContinuousLinearMap.norm_smulRight_apply]
    have h1 : ‖z‖ ^ (-s - 1) ≤ (1 / 4 : ℝ) ^ (-s - 1) :=
      Real.rpow_le_rpow_of_nonpos (by norm_num) hcube.le (by have := hG.hs0; linarith)
    calc ‖Dtor h (Torus.mk y - z)‖ * ‖G z‖ ≤ M1 * (C * (‖z‖ ^ (-s - 1) + 1)) := by
          gcongr; exact hM1 _; exact hC z hz
      _ ≤ M1 * (C * ((1 / 4 : ℝ) ^ (-s - 1) + 1)) := by gcongr
      _ = M1 * C * ((1 / 4 : ℝ) ^ (-s - 1) + 1) := by ring
      _ ≤ _ := by linarith

theorem integrable_kernD (hG : GoodKernel d s C G) {h : Torus d → ℝ} (hh : Torus.IsCk 2 h) (y : Euc d) :
    Integrable (kernD G h y) := by
  obtain ⟨M1, hM10, hM1⟩ := Dtor_bounded hh
  obtain ⟨M2, hM20, hM2⟩ := Dtor_lipschitz hh
  have hh1 : Torus.IsCk 1 h := hh.of_le (by norm_num)
  refine (integrable_dom hG M2 M1).mono' (measurable_kernD hG hh1 y).aestronglyMeasurable ?_
  filter_upwards [torus_ae_ne' hG.pos] with z hz
  exact kernD_norm_le hG hM1 hM2 hM10 hM20 y hz

theorem hasFDerivAt_convGradConv (hG : GoodKernel d s C G) {h : Torus d → ℝ} (hh : Torus.IsCk 2 h)
    (y0 : Euc d) :
    HasFDerivAt (Torus.lift (convGradConv G h)) (∫ z, kernD G h y0 z) y0 := by
  have hh1 : Torus.IsCk 1 h := hh.of_le (by norm_num)
  obtain ⟨B, hB0, hB⟩ := isCk_bounded hh1
  obtain ⟨L, hL0, hL⟩ := isLipschitz_of_isCk hh1
  obtain ⟨M1, hM10, hM1⟩ := Dtor_bounded hh
  obtain ⟨M2, hM20, hM2⟩ := Dtor_lipschitz hh
  have hfun : Torus.lift (convGradConv G h) = fun y => ∫ z, kern G h (Torus.mk y) z :=
    funext fun y => convGradConv_eq_integral_kern G h (Torus.mk y)
  rw [hfun]
  exact hasFDerivAt_integral_of_dominated_of_fderiv_le (F' := fun y z => kernD G h y z)
    (x₀ := y0) (s := univ) (bound := dom s C M2 M1 d) Filter.univ_mem
    (Filter.Eventually.of_forall fun y =>
      (measurable_kern hG (isCk_continuous hh1).measurable (Torus.mk y)).aestronglyMeasurable)
    (integrable_kern hG (isCk_continuous hh1).measurable hB hL hL0 hB0 (Torus.mk y0))
    (measurable_kernD hG hh1 y0).aestronglyMeasurable
    (by
      filter_upwards [torus_ae_ne' hG.pos] with z hz y _
      exact kernD_norm_le hG hM1 hM2 hM10 hM20 y hz)
    (integrable_dom hG M2 M1)
    (Filter.Eventually.of_forall fun z y _ => hasFDerivAt_kern hh y z)

theorem integral_kernD_apply (hG : GoodKernel d s C G) {h : Torus d → ℝ} (hh : Torus.IsCk 2 h)
    (y : Euc d) (v : Euc d) :
    (∫ z, kernD G h y z) v = convGradConv G (dirTor h v) (Torus.mk y) := by
  rw [ContinuousLinearMap.integral_apply (integrable_kernD hG hh y), convGradConv_eq_integral_kern]
  exact integral_congr_ae (Filter.Eventually.of_forall fun z => kernD_apply G h y z v)

/-! ### Induction on the order of regularity -/

/-- `v ↦ v_i • b` as a continuous linear map `ℝ^d → ℝ^d` -/
def projR (i : Fin d) : Euc d →L[ℝ] (Euc d →L[ℝ] Euc d) :=
  ContinuousLinearMap.smulRightL ℝ (Euc d) (Euc d) (EuclideanSpace.proj i)

theorem projR_apply (i : Fin d) (b v : Euc d) : projR i b v = v i • b := by
  simp [projR]

theorem norm_projR_le (i : Fin d) : ‖projR i‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun b => ?_
  refine ContinuousLinearMap.opNorm_le_bound _ (by positivity) fun v => ?_
  rw [projR_apply, norm_smul, one_mul]
  have := PiLp.norm_apply_le v i
  have h2 := mul_le_mul_of_nonneg_right this (norm_nonneg b)
  linarith

theorem clm_eq_sum (A : Euc d →L[ℝ] Euc d) :
    A = ∑ i, projR i (A (EuclideanSpace.single i 1)) := by
  ext v : 1
  have hv : v = ∑ i, v i • EuclideanSpace.single i (1 : ℝ) := by
    ext j
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hv]
  rw [map_sum, ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [map_smul, projR_apply]

theorem GoodKernel.regularity (hG : GoodKernel d s C G) (m : ℕ) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ h : Torus d → ℝ, Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) h →
      Torus.IsCk (m : WithTop ℕ∞) (convGradConv G h) ∧
        Torus.cbNorm m (convGradConv G h) ≤ K * Torus.cbNorm (m + 1) h := by
  set K0 := max (opM1 d s C) (opM2 s C) with hK0
  have hK00 : 0 ≤ K0 := le_max_of_le_left (opM1_nonneg hG)
  induction m with
  | zero =>
    refine ⟨K0, hK00, fun h hh => ?_⟩
    have hh1 : Torus.IsCk 1 h := by exact_mod_cast hh
    refine ⟨?_, ?_⟩
    · unfold Torus.IsCk
      rw [Nat.cast_zero, contDiff_zero]
      obtain ⟨B, hB0, hB⟩ := isCk_bounded hh1
      obtain ⟨L, hL0, hL⟩ := isLipschitz_of_isCk hh1
      exact (hG.continuous_op (isCk_continuous hh1) hB hL hL0 hB0).comp isOpenQuotientMap_mk.continuous
    · unfold Torus.cbNorm
      rw [Finset.sum_range_one]
      refine ciSup_le fun y => ?_
      rw [norm_iteratedFDeriv_zero]
      exact hG.norm_le_cb hh1 (Torus.mk y)
  | succ m ih =>
    obtain ⟨Km, hKm0, hKm⟩ := ih
    refine ⟨K0 + d * Km, by positivity, fun h hh => ?_⟩
    have hh2 : Torus.IsCk 2 h := hh.of_le (by norm_cast; omega)
    have hh1 : Torus.IsCk 1 h := hh.of_le (by norm_cast; omega)
    -- the directional derivatives
    set e : Fin d → Euc d := fun i => EuclideanSpace.single i 1 with he
    have hdh : ∀ i, Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) (dirTor h (e i)) := fun i =>
      isCk_dirTor (k := m + 1) hh (e i)
    have hnorme : ∀ i, ‖e i‖ ≤ 1 := fun i => by simp [he]
    have hIH := fun i => hKm (dirTor h (e i)) (hdh i)
    set f : Fin d → Euc d → Euc d := fun i => Torus.lift (convGradConv G (dirTor h (e i))) with hf
    have hfC : ∀ i, ContDiff ℝ (m : WithTop ℕ∞) (f i) := fun i => (hIH i).1
    -- derivative
    have hder : ∀ y, HasFDerivAt (Torus.lift (convGradConv G h)) (∑ i, projR i (f i y)) y := by
      intro y
      have h1 := hasFDerivAt_convGradConv hG hh2 y
      have h2 : (∫ z, kernD G h y z) = ∑ i, projR i (f i y) := by
        conv_lhs => rw [clm_eq_sum (∫ z, kernD G h y z)]
        refine Finset.sum_congr rfl fun i _ => ?_
        rw [integral_kernD_apply hG hh2]
        rfl
      rwa [h2] at h1
    have hfd : fderiv ℝ (Torus.lift (convGradConv G h)) = fun y => ∑ i, projR i (f i y) :=
      funext fun y => (hder y).fderiv
    have hsmooth : ContDiff ℝ (((m : WithTop ℕ∞)) + 1) (Torus.lift (convGradConv G h)) := by
      rw [contDiff_succ_iff_fderiv]
      refine ⟨fun y => (hder y).differentiableAt, fun h => absurd h (by simp), ?_⟩
      rw [hfd]
      exact ContDiff.sum fun i _ => (projR i).contDiff.comp (hfC i)
    have hCk : Torus.IsCk ((m + 1 : ℕ) : WithTop ℕ∞) (convGradConv G h) := by
      unfold Torus.IsCk; push_cast; exact hsmooth
    refine ⟨hCk, ?_⟩
    have hterm0 : ⨆ x : Euc d, ‖iteratedFDeriv ℝ 0 (Torus.lift (convGradConv G h)) x‖ ≤
        K0 * Torus.cbNorm (m + 1 + 1) h := by
      refine ciSup_le fun y => ?_
      rw [norm_iteratedFDeriv_zero]
      refine (hG.norm_le_cb hh1 (Torus.mk y)).trans ?_
      have := cbNorm_mono (φ := h) (k := 1) (k' := m + 1 + 1) (by omega)
      exact mul_le_mul_of_nonneg_left this hK00
    have hterm : ∀ j, j ≤ m → ⨆ y : Euc d, ‖iteratedFDeriv ℝ (j + 1) (Torus.lift (convGradConv G h)) y‖ ≤
        ∑ i, ⨆ y : Euc d, ‖iteratedFDeriv ℝ j (f i) y‖ := by
      intro j hj
      refine ciSup_le fun y => ?_
      rw [← norm_iteratedFDeriv_fderiv, hfd]
      have hsum_eq : iteratedFDeriv ℝ j (fun y => ∑ i, (projR i) (f i y)) y =
          ∑ i, iteratedFDeriv ℝ j ((projR i) ∘ (f i)) y :=
        iteratedFDeriv_fun_sum_apply (f := fun i => (projR i) ∘ (f i)) (u := Finset.univ)
          (fun i _ => ((projR i).contDiff.comp (hfC i)).contDiffAt.of_le (by exact_mod_cast hj))
      rw [hsum_eq]
      refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun i _ => ?_)
      have h1 := (projR i).norm_iteratedFDeriv_comp_left (f := f i) (x := y) (n := j)
        ((hfC i).contDiffAt) (by exact_mod_cast hj)
      refine h1.trans ?_
      have h2 := norm_projR_le i
      have h3 : ‖iteratedFDeriv ℝ j (f i) y‖ ≤ ⨆ y : Euc d, ‖iteratedFDeriv ℝ j (f i) y‖ :=
        norm_le_term (φ := convGradConv G (dirTor h (e i))) (hIH i).1 (by exact_mod_cast hj) y
      calc ‖projR i‖ * ‖iteratedFDeriv ℝ j (f i) y‖ ≤ 1 * ‖iteratedFDeriv ℝ j (f i) y‖ := by gcongr
        _ ≤ _ := by linarith
    have hsum : ∑ j ∈ Finset.range (m + 1), ⨆ y : Euc d, ‖iteratedFDeriv ℝ (j + 1) (Torus.lift (convGradConv G h)) y‖
        ≤ ∑ i, Torus.cbNorm m (convGradConv G (dirTor h (e i))) := by
      calc _ ≤ ∑ j ∈ Finset.range (m + 1), ∑ i, ⨆ y : Euc d, ‖iteratedFDeriv ℝ j (f i) y‖ :=
            Finset.sum_le_sum fun j hj => hterm j (Nat.lt_succ_iff.mp (Finset.mem_range.mp hj))
        _ = _ := by
            rw [Finset.sum_comm]
            rfl
    have hcb : ∀ i, Torus.cbNorm m (convGradConv G (dirTor h (e i))) ≤ Km * Torus.cbNorm (m + 1 + 1) h := by
      intro i
      refine (hIH i).2.trans ?_
      exact mul_le_mul_of_nonneg_left (cbNorm_dirTor_le (k := m + 1) hh (hnorme i)) hKm0
    unfold Torus.cbNorm at hterm0 hsum ⊢
    rw [Finset.sum_range_succ' (fun j => ⨆ x : Euc d, ‖iteratedFDeriv ℝ j (Torus.lift (convGradConv G h)) x‖)]
    have hcbs : ∑ i, Torus.cbNorm m (convGradConv G (dirTor h (e i))) ≤
        d * Km * Torus.cbNorm (m + 1 + 1) h := by
      calc _ ≤ ∑ _i : Fin d, Km * Torus.cbNorm (m + 1 + 1) h := Finset.sum_le_sum fun i _ => hcb i
        _ = _ := by simp; ring
    unfold Torus.cbNorm at hcbs
    nlinarith [hterm0, hsum, hcbs]

section KernelInstance

theorem goodKernel_periodicRieszGrad (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, GoodKernel d s C (periodicRieszGrad d s) := by
  obtain ⟨C, hC⟩ := periodicRieszGrad_bound_tdist_aux hd hs0 hsd
  refine ⟨max C 0, ?_⟩
  refine ⟨by omega, hs0, hsd, le_max_right _ _, measurable_periodicRieszGrad hsd,
    periodicRieszGrad_neg_of_lt hsd, fun z hz => (hC z hz).trans ?_⟩
  have : 0 ≤ tdist z 0 ^ (-s - 1) + 1 := by
    have := Real.rpow_nonneg (tdist_nonneg z 0) (-s - 1)
    linarith
  exact mul_le_mul_of_nonneg_right (le_max_left _ _) this


end KernelInstance

end HRS.KernelGrad
