import HRS.Whole.Adjoint

/-!
# MS-ULOC-MW, part 3: summability of `⟨z⟩^{-(d+3)}` over `ℤ^d` and unit-cell geometry

* `uw_summable_jb`: `∑_{z ∈ ℤ^d} ⟨z⟩^{-(d+3)} < ∞` (`ZLattice.summable_norm_rpow`);
* `uw_cellsup_le`: `sup_{z + [0,1]^d} ⟨x⟩^{-(d+3)} ≤ C ⟨z⟩^{-(d+3)}`.
-/

noncomputable section
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate FourierTransform ContDiff

namespace HRS.MS.UlocWeighted
open HRS.Whole

variable {d : ℕ}

/-- the lattice `ℤ^d ⊂ ℝ^d` as a `ℤ`-submodule -/
def uw_L (d : ℕ) : Submodule ℤ (Euc d) :=
  Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)

instance uw_L_discrete : DiscreteTopology (uw_L d) :=
  inferInstanceAs (DiscreteTopology (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)))

instance uw_L_zlattice : IsZLattice ℝ (uw_L d) :=
  inferInstanceAs (IsZLattice ℝ (Submodule.span ℤ (Set.range (EuclideanSpace.basisFun (Fin d) ℝ).toBasis)))

theorem uw_latticePt_mem (z : Fin d → ℤ) : latticePt z ∈ uw_L d := by
  have : latticePt z = ∑ i, (z i) • (EuclideanSpace.basisFun (Fin d) ℝ).toBasis i := by
    ext j
    simp [latticePt, Finset.sum_apply]
    simp [Pi.single_apply]
  rw [this]
  exact Submodule.sum_mem _ fun i _ => Submodule.smul_mem _ _ (Submodule.subset_span ⟨i, rfl⟩)

theorem uw_rank : Module.finrank ℤ (uw_L d) = d := by
  rw [ZLattice.rank ℝ (uw_L d)]; simp

theorem uw_summable_norm {r : ℝ} (hr : (d : ℝ) < r) :
    Summable fun z : Fin d → ℤ => ‖latticePt z‖ ^ (-r) := by
  have hr' : -r < -(Module.finrank ℤ (uw_L d) : ℝ) := by
    rw [uw_rank]; linarith
  have h := ZLattice.summable_norm_rpow (uw_L d) (-r) hr'
  have hinj : Function.Injective (fun z : Fin d → ℤ => (⟨latticePt z, uw_latticePt_mem z⟩ : uw_L d)) := by
    intro a b hab
    have h1 := congrArg Subtype.val hab
    funext i
    have h2 := congrFun (congrArg (fun v : Euc d => (v : Fin d → ℝ)) h1) i
    have h3 : ((a i : ℤ) : ℝ) = ((b i : ℤ) : ℝ) := h2
    exact_mod_cast h3
  have h2 := h.comp_injective hinj
  refine h2.congr (fun a => ?_)
  rfl


theorem uw_summable_jb :
    Summable fun z : Fin d → ℤ => jbracket (latticePt z) ^ (-((d : ℝ) + 3)) := by
  have h := uw_summable_norm (d := d) (r := (d : ℝ) + 3) (by linarith)
  refine Summable.of_norm_bounded_eventually h ?_
  filter_upwards [Filter.eventually_cofinite_ne 0] with z hz
  have hne : latticePt z ≠ 0 := by
    intro h0
    apply hz
    funext i
    have h1 := congrFun (congrArg (fun v : Euc d => (v : Fin d → ℝ)) h0) i
    have h3 : ((z i : ℤ) : ℝ) = 0 := h1
    simpa using h3
  have hpos : 0 < ‖latticePt z‖ := norm_pos_iff.2 hne
  have hjb : ‖latticePt z‖ ≤ jbracket (latticePt z) := by
    unfold jbracket
    apply Real.le_sqrt_of_sq_le
    nlinarith [sq_nonneg ‖latticePt z‖]
  have h0 : 0 ≤ jbracket (latticePt z) ^ (-((d : ℝ) + 3)) :=
    Real.rpow_nonneg (le_trans hpos.le hjb) _
  rw [Real.norm_of_nonneg h0]
  exact Real.rpow_le_rpow_of_nonpos hpos hjb (by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])


theorem uw_S_lt_top :
    (∑' z : Fin d → ℤ, ENNReal.ofReal (jbracket (latticePt z) ^ (-((d : ℝ) + 3)))) < ⊤ := by
  have h := ENNReal.ofReal_tsum_of_nonneg (fun z : Fin d → ℤ =>
    Real.rpow_nonneg (Real.sqrt_nonneg (1 + ‖latticePt z‖ ^ 2)) (-((d : ℝ) + 3))) uw_summable_jb
  exact lt_of_eq_of_lt h.symm ENNReal.ofReal_lt_top

/-- the unit cell `z + [0,1]^d` -/
def uw_cell (z : Fin d → ℤ) : Set (Euc d) :=
  {x : Euc d | ∀ i, latticePt z i ≤ x i ∧ x i ≤ latticePt z i + 1}

theorem uw_cell_closed (z : Fin d → ℤ) : IsClosed (uw_cell z) := by
  have : uw_cell z = ⋂ i : Fin d, ({x : Euc d | latticePt z i ≤ x i} ∩ {x : Euc d | x i ≤ latticePt z i + 1}) := by
    ext x; simp [uw_cell, Set.mem_iInter]
  rw [this]
  refine isClosed_iInter fun i => IsClosed.inter ?_ ?_
  · exact isClosed_le continuous_const (by fun_prop)
  · exact isClosed_le (by fun_prop) continuous_const

theorem uw_cell_cover : (⋃ z : Fin d → ℤ, uw_cell z) = Set.univ := by
  refine Set.eq_univ_of_forall fun x => ?_
  refine Set.mem_iUnion.2 ⟨fun i => ⌊x i⌋, fun i => ?_⟩
  simp only [latticePt]
  exact ⟨Int.floor_le (x i), (Int.lt_floor_add_one (x i)).le⟩

theorem uw_cell_norm {z : Fin d → ℤ} {x : Euc d} (hx : x ∈ uw_cell z) :
    ‖x - latticePt z‖ ^ 2 ≤ d := by
  rw [EuclideanSpace.norm_sq_eq]
  calc ∑ i, ‖(x - latticePt z) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
        refine Finset.sum_le_sum fun i _ => ?_
        have h := hx i
        have h1 : (x - latticePt z) i = x i - latticePt z i := rfl
        rw [h1, Real.norm_eq_abs, sq_abs]
        nlinarith [h.1, h.2]
    _ = d := by simp

theorem uw_jb_peetre (x y : Euc d) :
    jbracket y ≤ Real.sqrt (2 * (1 + ‖x - y‖ ^ 2)) * jbracket x := by
  unfold jbracket
  rw [← Real.sqrt_mul (by positivity)]
  apply Real.sqrt_le_sqrt
  have h1 : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
    have := norm_sub_le x (x - y)
    simpa using this
  have h2 : ‖y‖ ^ 2 ≤ 2 * ‖x‖ ^ 2 + 2 * ‖x - y‖ ^ 2 := by
    nlinarith [sq_nonneg (‖x‖ - ‖x - y‖), norm_nonneg y]
  nlinarith [sq_nonneg ‖x‖, sq_nonneg ‖x - y‖, mul_nonneg (sq_nonneg ‖x‖) (sq_nonneg ‖x - y‖)]

theorem uw_cellsup_le (z : Fin d → ℤ) :
    (⨆ x ∈ uw_cell z, ENNReal.ofReal (jbracket x ^ (-((d : ℝ) + 3)))) ≤
      ENNReal.ofReal (Real.sqrt (2 * (1 + d)) ^ ((d : ℝ) + 3)) *
        ENNReal.ofReal (jbracket (latticePt z) ^ (-((d : ℝ) + 3))) := by
  refine iSup₂_le fun x hx => ?_
  set B := Real.sqrt (2 * (1 + (d : ℝ))) with hB
  have hBpos : 0 < B := Real.sqrt_pos.2 (by positivity)
  have hjz : 0 < jbracket (latticePt z) := Real.sqrt_pos.2 (by positivity)
  have hjx : 0 < jbracket x := Real.sqrt_pos.2 (by positivity)
  have hP := uw_jb_peetre x (latticePt z)
  have hn := uw_cell_norm hx
  have hBle : Real.sqrt (2 * (1 + ‖x - latticePt z‖ ^ 2)) ≤ B :=
    Real.sqrt_le_sqrt (by linarith)
  have h1 : jbracket (latticePt z) / B ≤ jbracket x := by
    rw [div_le_iff₀ hBpos]
    calc jbracket (latticePt z) ≤ _ := hP
      _ ≤ B * jbracket x := mul_le_mul_of_nonneg_right hBle hjx.le
      _ = _ := mul_comm _ _
  rw [← ENNReal.ofReal_mul (by positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h2 := Real.rpow_le_rpow_of_nonpos (div_pos hjz hBpos) h1
    (show -((d : ℝ) + 3) ≤ 0 by linarith [(Nat.cast_nonneg d : (0:ℝ) ≤ d)])
  refine h2.trans (le_of_eq ?_)
  rw [Real.div_rpow hjz.le hBpos.le, div_eq_mul_inv, ← Real.rpow_neg hBpos.le, neg_neg, mul_comm]

end HRS.MS.UlocWeighted
