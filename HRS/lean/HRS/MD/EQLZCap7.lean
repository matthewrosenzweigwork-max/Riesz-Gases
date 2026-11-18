import HRS.MD.EQLZCap4
import HRS.MD.EQLZCap6

/-!
# EQ-LZ packet CAP, helper 7: the pair cut-off on `𝕋^{N d}` (without the energy estimate)

`torCut m = ∏_{i<j} Th m (sT (x_i - x_j))` on `𝕋^{Nd} ≃ Config d N` (`d1_configEquiv`), its periodic lift
`∏_{p} Th m (sE (Lp p y))`, smoothness, `0 ≤ torCut ≤ 1`, vanishing near the collision set `badSet`, and `= 1`
near every collision-free point for large `m`.
-/

noncomputable section

set_option linter.unusedSectionVars false

open MeasureTheory Filter Topology
open scoped Classical

namespace HRS.MD.EQLZ.Cap

variable {d N : ℕ}

def pairs (N : ℕ) : Finset (Fin N × Fin N) := Finset.univ.filter fun p => p.1 < p.2

/-- The pair difference `y ↦ y_i - y_j` on the covering space `ℝ^{Nd}`, as a continuous linear map. -/
def Lp (d N : ℕ) (p : Fin N × Fin N) : Euc (N * d) →L[ℝ] Euc d :=
  ((ContinuousLinearMap.proj p.1 : (Fin N → Euc d) →L[ℝ] Euc d) - ContinuousLinearMap.proj p.2).comp
    ((d1_eucEquiv d N).symm : Euc (N * d) →L[ℝ] (Fin N → Euc d))

theorem Lp_apply (p : Fin N × Fin N) (y : Euc (N * d)) :
    Lp d N p y = (d1_eucEquiv d N).symm y p.1 - (d1_eucEquiv d N).symm y p.2 := rfl

def cfgCut (m : ℕ) (X : Config d N) : ℝ := ∏ p ∈ pairs N, Th m (sT (X p.1 - X p.2))

def torCut (d N m : ℕ) (x : Torus (N * d)) : ℝ := cfgCut m ((d1_configEquiv d N).symm x)

def badSet (d N : ℕ) : Set (Torus (N * d)) := {x | (d1_configEquiv d N).symm x ∈ collisionSet d N}

theorem isClosed_collisionSet' (d N : ℕ) : IsClosed (collisionSet d N) := by
  have : collisionSet d N = ⋃ i : Fin N, ⋃ j : Fin N, ⋃ _ : i ≠ j, {X : Config d N | X i = X j} := by
    ext X; simp [collisionSet]
  rw [this]
  exact isClosed_iUnion_of_finite fun i => isClosed_iUnion_of_finite fun j =>
    isClosed_iUnion_of_finite fun _ => isClosed_eq (continuous_apply i) (continuous_apply j)

theorem isClosed_badSet (d N : ℕ) : IsClosed (badSet d N) :=
  (isClosed_collisionSet' d N).preimage (d1_configEquiv_symm_continuous d N)

theorem lift_torCut (m : ℕ) (y : Euc (N * d)) :
    Torus.lift (torCut d N m) y = ∏ p ∈ pairs N, Th m (sE (Lp d N p y)) := by
  unfold Torus.lift torCut cfgCut
  simp only [Function.comp, d1_configEquiv_symm_mk]
  refine Finset.prod_congr rfl fun p _ => ?_
  rw [← KernelGrad.mk_sub, sT_mk, Lp_apply]

section

variable {m : ℕ} (hm : 1 ≤ m)
include hm

theorem torCut_smooth : Torus.IsSmooth (torCut d N m) := by
  unfold Torus.IsSmooth Torus.IsCk
  have : Torus.lift (torCut d N m) = fun y => ∏ p ∈ pairs N, Th m (sE (Lp d N p y)) :=
    funext (lift_torCut m)
  rw [this]
  exact contDiff_prod fun p _ => (Th_smooth hm).comp (contDiff_sE.comp (Lp d N p).contDiff)

theorem torCut_nonneg (x : Torus (N * d)) : 0 ≤ torCut d N m x :=
  Finset.prod_nonneg fun p _ => Th_nonneg hm _

theorem torCut_le_one (x : Torus (N * d)) : torCut d N m x ≤ 1 :=
  Finset.prod_le_one₀ (fun p _ => Th_nonneg hm _) fun p _ => Th_le_one hm _

end

/-- Near a point of the collision set the cut-off vanishes. -/
theorem torCut_zero_near {m : ℕ} (hm : 1 ≤ m) (y : Euc (N * d)) (hy : Torus.mk y ∈ badSet d N) :
    ∀ᶠ z in 𝓝 y, Torus.lift (torCut d N m) z = 0 := by
  obtain ⟨i, j, hij, heq⟩ : ∃ i j : Fin N, i ≠ j ∧
      (d1_configEquiv d N).symm (Torus.mk y) i = (d1_configEquiv d N).symm (Torus.mk y) j := hy
  -- the ordered pair
  obtain ⟨p, hp, hp0⟩ : ∃ p ∈ pairs N, sE (Lp d N p y) = 0 := by
    have key : ∀ a b : Fin N, a < b → (d1_configEquiv d N).symm (Torus.mk y) a =
        (d1_configEquiv d N).symm (Torus.mk y) b → ∃ p ∈ pairs N, sE (Lp d N p y) = 0 := by
      intro a b hab h
      refine ⟨(a, b), by simp [pairs, hab], ?_⟩
      rw [d1_configEquiv_symm_mk] at h
      have h' : Torus.mk ((d1_eucEquiv d N).symm y a) = Torus.mk ((d1_eucEquiv d N).symm y b) :=
        congrFun h |> fun _ => by simpa using h
      rw [Lp_apply, ← sT_mk, KernelGrad.mk_sub]
      simp only
      rw [h', sub_self, sT_zero]
    rcases lt_or_gt_of_ne hij with h | h
    · exact key i j h heq
    · exact key j i h heq.symm
  have hcont : Continuous fun z : Euc (N * d) => sE (Lp d N p z) :=
    (contDiff_sE.continuous).comp (Lp d N p).continuous
  have hlt : sE (Lp d N p y) < Real.exp (-2 * m) := by rw [hp0]; exact Real.exp_pos _
  filter_upwards [hcont.continuousAt.eventually (gt_mem_nhds hlt)] with z hz
  rw [lift_torCut]
  exact Finset.prod_eq_zero hp (Th_zero hm hz.le)

theorem torCut_one_near (y : Euc (N * d)) (hy : Torus.mk y ∉ badSet d N) :
    ∃ k₀ : ℕ, ∀ k ≥ k₀, ∀ᶠ z in 𝓝 y, Torus.lift (torCut d N (k + 1)) z = 1 := by
  -- positivity of the pair separations
  have hpos : ∀ p ∈ pairs N, 0 < sE (Lp d N p y) := by
    intro p hp
    by_contra hneg
    have h0 : sE (Lp d N p y) = 0 := le_antisymm (not_lt.1 hneg) (sE_nonneg _)
    apply hy
    have hmk := sE_eq_zero_imp _ h0
    rw [Lp_apply, KernelGrad.mk_sub, sub_eq_zero] at hmk
    have hlt : p.1 < p.2 := (Finset.mem_filter.1 hp).2
    refine ⟨p.1, p.2, hlt.ne, ?_⟩
    rw [d1_configEquiv_symm_mk]
    exact hmk
  have hev : ∀ᶠ k : ℕ in atTop, ∀ p ∈ pairs N, Real.exp (-((k + 1 : ℕ) : ℝ)) < sE (Lp d N p y) / 2 := by
    rw [Finset.eventually_all]
    intro p hp
    have ht : Tendsto (fun k : ℕ => Real.exp (-((k + 1 : ℕ) : ℝ))) atTop (𝓝 0) :=
      Real.tendsto_exp_neg_atTop_nhds_zero.comp
        (tendsto_natCast_atTop_atTop.comp (tendsto_add_atTop_nat 1))
    exact ht.eventually (gt_mem_nhds (by have := hpos p hp; positivity))
  obtain ⟨k₀, hk₀⟩ := eventually_atTop.1 hev
  refine ⟨k₀, fun k hk => ?_⟩
  have hk1 := hk₀ k hk
  have hcont : ∀ p ∈ pairs N, ∀ᶠ z in 𝓝 y, sE (Lp d N p y) / 2 < sE (Lp d N p z) := by
    intro p hp
    have hc : Continuous fun z : Euc (N * d) => sE (Lp d N p z) :=
      (contDiff_sE.continuous).comp (Lp d N p).continuous
    exact hc.continuousAt.eventually (lt_mem_nhds (by have := hpos p hp; linarith))
  filter_upwards [(Finset.eventually_all (pairs N)).2 hcont] with z hz
  rw [lift_torCut]
  refine Finset.prod_eq_one fun p hp => ?_
  exact Th_one (by omega : 1 ≤ k + 1) (by
    have := hk1 p hp
    have := hz p hp
    push_cast at *
    linarith)

/-! ### The gradient of the cut-off -/

/-- A uniform bound for the norms of the pair differences. -/
def CLs (d N : ℕ) : ℝ := 2 * ‖((d1_eucEquiv d N).symm : Euc (N * d) →L[ℝ] (Fin N → Euc d))‖

theorem norm_proj_le_one (i : Fin N) :
    ‖(ContinuousLinearMap.proj i : (Fin N → Euc d) →L[ℝ] Euc d)‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one (fun f => by
    simpa using norm_le_pi_norm f i)

theorem norm_Lp_le (p : Fin N × Fin N) : ‖Lp d N p‖ ≤ CLs d N := by
  unfold Lp CLs
  refine (ContinuousLinearMap.opNorm_comp_le _ _).trans ?_
  refine mul_le_mul_of_nonneg_right ?_ (norm_nonneg _)
  calc _ ≤ ‖(ContinuousLinearMap.proj p.1 : (Fin N → Euc d) →L[ℝ] Euc d)‖ +
        ‖(ContinuousLinearMap.proj p.2 : (Fin N → Euc d) →L[ℝ] Euc d)‖ := norm_sub_le _ _
    _ ≤ 1 + 1 := add_le_add (norm_proj_le_one _) (norm_proj_le_one _)
    _ = 2 := by norm_num

theorem CLs_nonneg : 0 ≤ CLs d N := by unfold CLs; positivity

theorem hasFDerivAt_factor {m : ℕ} (hm : 1 ≤ m) (p : Fin N × Fin N) (y : Euc (N * d)) :
    HasFDerivAt (fun z => Th m (sE (Lp d N p z)))
      ((deriv (Th m) (sE (Lp d N p y))) • ((fderiv ℝ sE (Lp d N p y)).comp (Lp d N p))) y := by
  have hsd : DifferentiableAt ℝ (sE : Euc d → ℝ) (Lp d N p y) :=
    (contDiff_sE.differentiable (by simp)) _
  have h1 : HasFDerivAt (fun z => sE (Lp d N p z)) ((fderiv ℝ sE (Lp d N p y)).comp (Lp d N p)) y :=
    hsd.hasFDerivAt.comp y (Lp d N p).hasFDerivAt
  have h2 : HasDerivAt (Th m) (deriv (Th m) (sE (Lp d N p y))) (sE (Lp d N p y)) :=
    (((Th_smooth hm).differentiable (by simp)) _).hasDerivAt
  exact h2.comp_hasFDerivAt y h1

/-- The key pointwise gradient bound for the cut-off. -/
theorem fderiv_torCut_sq {m : ℕ} (hm : 1 ≤ m) {A : ℝ} (hA : ∀ x, |deriv Real.smoothTransition x| ≤ A)
    (y : Euc (N * d)) :
    ‖fderiv ℝ (Torus.lift (torCut d N m)) y‖ ^ 2 ≤
      ((pairs N).card * (8 * Real.pi ^ 2 * d) * CLs d N ^ 2 * A ^ 2) / (m : ℝ) ^ 2 *
        ∑ p ∈ pairs N, Psi m (sE (Lp d N p y)) := by
  have hfun : Torus.lift (torCut d N m) = fun z => ∏ p ∈ pairs N, Th m (sE (Lp d N p z)) :=
    funext (lift_torCut m)
  have hD := HasFDerivAt.finsetProd (u := pairs N) (x := y)
    (g := fun p z => Th m (sE (Lp d N p z)))
    (g' := fun p => (deriv (Th m) (sE (Lp d N p y))) • ((fderiv ℝ sE (Lp d N p y)).comp (Lp d N p)))
    (fun p _ => hasFDerivAt_factor hm p y)
  rw [hfun, hD.fderiv]
  set f' : Fin N × Fin N → (Euc (N * d) →L[ℝ] ℝ) := fun p =>
    (deriv (Th m) (sE (Lp d N p y))) • ((fderiv ℝ sE (Lp d N p y)).comp (Lp d N p)) with hf'
  -- norm of the factors
  have h1 : ∀ p ∈ pairs N, ‖f' p‖ ^ 2 ≤ (8 * Real.pi ^ 2 * d) * CLs d N ^ 2 * (A ^ 2 / (m : ℝ) ^ 2) *
      Psi m (sE (Lp d N p y)) := by
    intro p hp
    set s := sE (Lp d N p y) with hs
    have hs0 : 0 ≤ s := sE_nonneg _
    have hn : ‖f' p‖ ≤ |deriv (Th m) s| * (‖fderiv ℝ sE (Lp d N p y)‖ * CLs d N) := by
      rw [hf', norm_smul, Real.norm_eq_abs]
      refine mul_le_mul_of_nonneg_left ((ContinuousLinearMap.opNorm_comp_le _ _).trans ?_) (abs_nonneg _)
      exact mul_le_mul_of_nonneg_left (norm_Lp_le p) (norm_nonneg _)
    have hn2 : ‖f' p‖ ^ 2 ≤ (deriv (Th m) s) ^ 2 * (‖fderiv ℝ sE (Lp d N p y)‖ ^ 2 * CLs d N ^ 2) := by
      calc ‖f' p‖ ^ 2 ≤ (|deriv (Th m) s| * (‖fderiv ℝ sE (Lp d N p y)‖ * CLs d N)) ^ 2 :=
            pow_le_pow_left₀ (norm_nonneg _) hn 2
        _ = _ := by rw [mul_pow, mul_pow, sq_abs]
    have hds := norm_fderiv_sE_sq (Lp d N p y)
    have hTh := Th_deriv_sq hm hA hs0
    calc ‖f' p‖ ^ 2 ≤ (deriv (Th m) s) ^ 2 * (‖fderiv ℝ sE (Lp d N p y)‖ ^ 2 * CLs d N ^ 2) := hn2
      _ ≤ (deriv (Th m) s) ^ 2 * ((8 * Real.pi ^ 2 * d * s) * CLs d N ^ 2) := by
          gcongr
      _ = (8 * Real.pi ^ 2 * d) * CLs d N ^ 2 * ((deriv (Th m) s) ^ 2 * s) := by ring
      _ ≤ (8 * Real.pi ^ 2 * d) * CLs d N ^ 2 * ((A ^ 2 / (m : ℝ) ^ 2) * Psi m s) := by
          gcongr
      _ = _ := by ring
  -- the product coefficients are in [0, 1]
  have h2 : ‖∑ p ∈ pairs N, (∏ q ∈ (pairs N).erase p, Th m (sE (Lp d N q y))) • f' p‖ ≤
      ∑ p ∈ pairs N, ‖f' p‖ := by
    refine (norm_sum_le _ _).trans (Finset.sum_le_sum fun p _ => ?_)
    rw [norm_smul, Real.norm_eq_abs, abs_of_nonneg
      (Finset.prod_nonneg fun q _ => Th_nonneg hm _)]
    refine mul_le_of_le_one_left (norm_nonneg _) ?_
    exact Finset.prod_le_one₀ (fun q _ => Th_nonneg hm _) fun q _ => Th_le_one hm _
  have h3 : (∑ p ∈ pairs N, ‖f' p‖) ^ 2 ≤ (pairs N).card * ∑ p ∈ pairs N, ‖f' p‖ ^ 2 :=
    sq_sum_le_card_mul_sum_sq
  calc ‖∑ p ∈ pairs N, (∏ q ∈ (pairs N).erase p, Th m (sE (Lp d N q y))) • f' p‖ ^ 2
      ≤ (∑ p ∈ pairs N, ‖f' p‖) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h2 2
    _ ≤ (pairs N).card * ∑ p ∈ pairs N, ‖f' p‖ ^ 2 := h3
    _ ≤ (pairs N).card * ∑ p ∈ pairs N, ((8 * Real.pi ^ 2 * d) * CLs d N ^ 2 * (A ^ 2 / (m : ℝ) ^ 2) *
        Psi m (sE (Lp d N p y))) := by
          gcongr with p hp
          exact h1 p hp
    _ = ((pairs N).card * (8 * Real.pi ^ 2 * d) * CLs d N ^ 2 * A ^ 2) / (m : ℝ) ^ 2 *
        ∑ p ∈ pairs N, Psi m (sE (Lp d N p y)) := by
          rw [← Finset.mul_sum]
          ring

end HRS.MD.EQLZ.Cap
