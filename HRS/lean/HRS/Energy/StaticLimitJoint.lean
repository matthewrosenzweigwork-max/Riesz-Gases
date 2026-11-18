import HRS.Energy.StaticLimitCore
import HRS.Energy.StaticLimitBasic
import HRS.Energy.StaticLimitResponse

/-!
# The joint Hilbert space `H^{-m}_0 ⊕ ℓ²(Idx)` and truncations (work package STAT-4.21)
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.StaticLimitAux

section LpGeneric

variable {ι : Type*}

/-- Squares of the coordinates of an `ℓ²` vector are summable. -/
theorem lp_sq_summable (v : lp (fun _ : ι => ℝ) 2) : Summable fun i => (v i) ^ 2 := by
  have h := lp.memℓp v
  have := (memℓp_gen_iff (p := 2) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mp h
  simpa [Real.norm_eq_abs, sq_abs] using this

theorem lp_norm_sq (v : lp (fun _ : ι => ℝ) 2) : ‖v‖ ^ 2 = ∑' i, (v i) ^ 2 := by
  have := lp.norm_rpow_eq_tsum (p := 2) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal) v
  simpa [Real.norm_eq_abs, sq_abs] using this

/-- Build an `ℓ²` vector from coordinates dominated by a summable sequence. -/
def mkLp (g : ι → ℝ) (b : ι → ℝ) (hb : Summable b) (hg : ∀ i, g i ^ 2 ≤ b i) :
    lp (fun _ : ι => ℝ) 2 :=
  ⟨g, by
    refine (memℓp_gen_iff (p := 2) (by norm_num : (0 : ℝ) < (2 : ℝ≥0∞).toReal)).mpr ?_
    refine Summable.of_nonneg_of_le (fun i => by positivity) (fun i => ?_) hb
    simpa [Real.norm_eq_abs, sq_abs] using hg i⟩

theorem mkLp_apply (g : ι → ℝ) (b : ι → ℝ) (hb : Summable b) (hg : ∀ i, g i ^ 2 ≤ b i) (i : ι) :
    mkLp g b hb hg i = g i := rfl

end LpGeneric


section LpTrunc

variable {ι : Type*} [DecidableEq ι]

/-- Truncation of an `ℓ²` vector to a finite set of coordinates. -/
def truncLp (S : Finset ι) (v : lp (fun _ : ι => ℝ) 2) : lp (fun _ : ι => ℝ) 2 :=
  ∑ i ∈ S, v i • lp.single 2 i (1 : ℝ)

theorem truncLp_apply (S : Finset ι) (v : lp (fun _ : ι => ℝ) 2) (j : ι) :
    truncLp S v j = if j ∈ S then v j else 0 := by
  unfold truncLp
  rw [lp.coeFn_sum, Finset.sum_apply]
  simp only [lp.coeFn_smul, Pi.smul_apply, lp.single_apply, smul_eq_mul]
  by_cases hj : j ∈ S
  · rw [if_pos hj, Finset.sum_eq_single j]
    · simp
    · intro i _ hij; simp [Pi.single_apply, hij.symm]
    · intro h; exact absurd hj h
  · rw [if_neg hj]
    exact Finset.sum_eq_zero fun i hi => by
      have : j ≠ i := fun h => hj (h ▸ hi)
      simp [Pi.single_apply, this]

theorem norm_sub_truncLp_sq_le (v : lp (fun _ : ι => ℝ) 2) (S : Finset ι) (b : ι → ℝ)
    (hb : Summable b) (hv : ∀ i, v i ^ 2 ≤ b i) :
    ‖v - truncLp S v‖ ^ 2 ≤ ∑' i : {x // x ∉ S}, b i := by
  rw [lp_norm_sq]
  have hc : ∀ i, (v - truncLp S v) i = if i ∈ S then 0 else v i := by
    intro i
    rw [lp.coeFn_sub, Pi.sub_apply, truncLp_apply]
    split_ifs <;> simp
  have hsupp : Function.support (fun i => ((v - truncLp S v) i) ^ 2) ⊆ {x | x ∉ S} := by
    intro i hi
    simp only [Function.mem_support, hc] at hi
    by_contra h
    exact hi (by simp [show i ∈ S from not_not.mp h])
  rw [← tsum_subtype_eq_of_support_subset hsupp]
  refine Summable.tsum_le_tsum (fun i => ?_) ?_ (hb.subtype _)
  · have hi : (i : ι) ∉ S := i.2
    simpa [hc, hi] using hv i
  · exact (lp_sq_summable (v - truncLp S v)).subtype _

end LpTrunc


section LpCont

variable {ι : Type*} [DecidableEq ι] {Z : Type*} [TopologicalSpace Z]

theorem continuous_mkLp (g : Z → ι → ℝ) (b : ι → ℝ) (hb : Summable b) (hg : ∀ z i, g z i ^ 2 ≤ b i)
    (hc : ∀ i, Continuous fun z => g z i) :
    Continuous fun z => mkLp (g z) b hb (hg z) := by
  set G : Z → lp (fun _ : ι => ℝ) 2 := fun z => mkLp (g z) b hb (hg z) with hG
  have hF : ∀ S : Finset ι, Continuous fun z => truncLp S (G z) := by
    intro S
    unfold truncLp
    refine continuous_finset_sum _ fun i _ => ?_
    exact (hc i).smul continuous_const
  have hU : TendstoUniformly (fun S : Finset ι => fun z => truncLp S (G z)) G atTop := by
    rw [Metric.tendstoUniformly_iff]
    intro ε hε
    have := (tendsto_order.1 (tendsto_tsum_compl_atTop_zero b)).2 (ε ^ 2) (by positivity)
    filter_upwards [this] with S hS z
    rw [dist_eq_norm]
    have h := norm_sub_truncLp_sq_le (G z) S b hb (hg z)
    have h2 : ‖G z - truncLp S (G z)‖ ^ 2 < ε ^ 2 := lt_of_le_of_lt h hS
    exact lt_of_pow_lt_pow_left₀ 2 hε.le h2
  exact hU.continuous (Filter.Eventually.of_forall hF).frequently

end LpCont


/-- The feature-coefficient space `ℓ²(Idx d)`. -/
def FeatSp (d : ℕ) : Type := lp (fun _ : Idx d => ℝ) 2

namespace FeatSp

variable {d : ℕ}

instance : NormedAddCommGroup (FeatSp d) :=
  inferInstanceAs (NormedAddCommGroup (lp (fun _ : Idx d => ℝ) 2))

instance : InnerProductSpace ℝ (FeatSp d) :=
  inferInstanceAs (InnerProductSpace ℝ (lp (fun _ : Idx d => ℝ) 2))

instance : CompleteSpace (FeatSp d) :=
  inferInstanceAs (CompleteSpace (lp (fun _ : Idx d => ℝ) 2))

instance : MeasurableSpace (FeatSp d) := borel _

instance : BorelSpace (FeatSp d) := ⟨rfl⟩

instance : TopologicalSpace.SeparableSpace (FeatSp d) :=
  separable_lp (ι := Idx d)

instance : SecondCountableTopology (FeatSp d) :=
  UniformSpace.secondCountable_of_separable _

/-- The coordinate of a feature-coefficient vector. -/
def coord (f : FeatSp d) (i : Idx d) : ℝ := (show lp (fun _ : Idx d => ℝ) 2 from f) i

theorem norm_sq (f : FeatSp d) : ‖f‖ ^ 2 = ∑' i, coord f i ^ 2 :=
  lp_norm_sq (show lp (fun _ : Idx d => ℝ) 2 from f)

theorem summable_sq (f : FeatSp d) : Summable fun i => coord f i ^ 2 :=
  lp_sq_summable (show lp (fun _ : Idx d => ℝ) 2 from f)

/-- Build a feature-coefficient vector from dominated coordinates. -/
def mk (g : Idx d → ℝ) (b : Idx d → ℝ) (hb : Summable b) (hg : ∀ i, g i ^ 2 ≤ b i) : FeatSp d :=
  mkLp g b hb hg

theorem coord_mk (g : Idx d → ℝ) (b : Idx d → ℝ) (hb : Summable b) (hg : ∀ i, g i ^ 2 ≤ b i)
    (i : Idx d) : coord (mk g b hb hg) i = g i := rfl

theorem ext_coord {f f' : FeatSp d} (h : ∀ i, coord f i = coord f' i) : f = f' := by
  have : (show lp (fun _ : Idx d => ℝ) 2 from f) = show lp (fun _ : Idx d => ℝ) 2 from f' :=
    lp.ext (funext h)
  exact this

end FeatSp

/-- The joint space `H^{-m}_0 ⊕ ℓ²(Idx d)` with the `ℓ²`-product structure. -/
abbrev JSp (d : ℕ) (m : ℝ) : Type := WithLp 2 (NegSobolev d m × FeatSp d)

example (d : ℕ) (m : ℝ) : InnerProductSpace ℝ (JSp d m) := inferInstance
example (d : ℕ) (m : ℝ) : CompleteSpace (JSp d m) := inferInstance
example (d : ℕ) (m : ℝ) : MeasurableSpace (JSp d m) := inferInstance
example (d : ℕ) (m : ℝ) : BorelSpace (JSp d m) := inferInstance
example (d : ℕ) (m : ℝ) : SecondCountableTopology (JSp d m) := inferInstance


section Ymap

open HRS Torus

variable {d : ℕ} {m : ℝ}

theorem coord_sq_le_ofMeasureDiff (hm : (d : ℝ) < 2 * m) (μ ν : Measure (Torus d))
    [IsProbabilityMeasure μ] [IsProbabilityMeasure ν] (k : NonzeroLattice d) :
    NegSobolev.coord (NegSobolev.ofMeasureDiff m μ ν) k ^ 2 ≤
      8 * Lattice.jp k.1 ^ (-(2 * m)) := by
  rw [show NegSobolev.coord (NegSobolev.ofMeasureDiff m μ ν) k = _ from
    coord_ofMeasureDiff hm μ ν k, mul_pow, Torus.jp_rpow_sq,
    show 2 * -m = -(2 * m) by ring]
  have h1 := Torus.abs_measureRealCoeff_le μ k
  have h2 := Torus.abs_measureRealCoeff_le ν k
  simp only [measure_univ, ENNReal.toReal_one, mul_one] at h1 h2
  have h3 : |Torus.measureRealCoeff μ k - Torus.measureRealCoeff ν k| ≤ 2 * Real.sqrt 2 := by
    calc _ ≤ _ := abs_sub _ _
      _ ≤ Real.sqrt 2 + Real.sqrt 2 := add_le_add h1 h2
      _ = _ := by ring
  have h4 : (Torus.measureRealCoeff μ k - Torus.measureRealCoeff ν k) ^ 2 ≤ 8 := by
    have := pow_le_pow_left₀ (abs_nonneg _) h3 2
    rw [sq_abs] at this
    calc _ ≤ _ := this
      _ = 8 := by rw [mul_pow, Real.sq_sqrt (by norm_num)]; norm_num
  have hj : 0 ≤ Lattice.jp k.1 ^ (-(2 * m)) := Real.rpow_nonneg (Torus.jp_pos _).le _
  nlinarith

theorem NegSobolev.ext_coord' {F F' : NegSobolev d m} (h : ∀ k, NegSobolev.coord F k = NegSobolev.coord F' k) :
    F = F' := by
  have : (show lp (fun _ : NonzeroLattice d => ℝ) 2 from F) =
      show lp (fun _ : NonzeroLattice d => ℝ) 2 from F' := lp.ext (funext h)
  exact this

/-- `δ_x - μ` in `H^{-m}_0`. -/
def Ye (m : ℝ) (μ : Measure (Torus d)) (x : Torus d) : NegSobolev d m :=
  NegSobolev.ofMeasureDiff m (Measure.dirac x) μ

theorem measureRealCoeff_dirac (x : Torus d) (k : NonzeroLattice d) :
    Torus.measureRealCoeff (Measure.dirac x) k = Torus.realMode k x := by
  unfold Torus.measureRealCoeff
  exact integral_dirac' _ _ (continuous_realMode' k).stronglyMeasurable

theorem coord_Ye (hm : (d : ℝ) < 2 * m) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (x : Torus d) (k : NonzeroLattice d) :
    NegSobolev.coord (Ye m μ x) k =
      Lattice.jp k.1 ^ (-m) * (Torus.realMode k x - Torus.measureRealCoeff μ k) := by
  unfold Ye
  rw [coord_ofMeasureDiff hm, measureRealCoeff_dirac]

theorem continuous_Ye (hm : (d : ℝ) < 2 * m) (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    Continuous (Ye m μ) := by
  classical
  have hb : Summable fun k : NonzeroLattice d => 8 * Lattice.jp k.1 ^ (-(2 * m)) :=
    (summable_jp_rpow (d := d) m hm).mul_left 8
  have hg : ∀ (x : Torus d) (k : NonzeroLattice d),
      NegSobolev.coord (Ye m μ x) k ^ 2 ≤ 8 * Lattice.jp k.1 ^ (-(2 * m)) :=
    fun x k => coord_sq_le_ofMeasureDiff hm (Measure.dirac x) μ k
  have hc := continuous_mkLp (Z := Torus d) (ι := NonzeroLattice d)
    (fun x k => NegSobolev.coord (Ye m μ x) k) _ hb hg (fun k => by
      simp only [coord_Ye hm]
      exact continuous_const.mul ((continuous_realMode' k).sub continuous_const))
  have e : ∀ x, Ye m μ x = (mkLp (fun k => NegSobolev.coord (Ye m μ x) k) _ hb (hg x) :
      lp (fun _ : NonzeroLattice d => ℝ) 2) := fun x => NegSobolev.ext_coord' (fun k => rfl)
  have e' : Ye m μ = fun x => (mkLp (fun k => NegSobolev.coord (Ye m μ x) k) _ hb (hg x) :
      lp (fun _ : NonzeroLattice d => ℝ) 2) := funext e
  rw [e']
  exact hc

end Ymap


section Yfeat

open HRS Torus

variable {d : ℕ} {a : Lattice d → ℝ}

theorem Zfeat_sq_le (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (i : Idx d) (x : Torus d) :
    Zfeat μ a i x ^ 2 ≤ 4 * (fbound a i * fbound a i) := by
  have h := abs_Zfeat_le μ (a := a) i x
  have h0 : 0 ≤ fbound a i := fbound_nonneg i
  have := pow_le_pow_left₀ (abs_nonneg _) h 2
  rw [sq_abs] at this
  nlinarith

/-- The centred feature vector `Z(x) = (Z_i(x))_i ∈ ℓ²(Idx d)`. -/
def Yf (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (μ : Measure (Torus d)) [IsProbabilityMeasure μ]
    (x : Torus d) : FeatSp d :=
  FeatSp.mk (fun i => Zfeat μ a i x) (fun i => 4 * (fbound a i * fbound a i))
    ((summable_fbound_sq ha0 has).mul_left 4) (fun i => Zfeat_sq_le μ i x)

theorem coord_Yf (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (x : Torus d) (i : Idx d) :
    FeatSp.coord (Yf ha0 has μ x) i = Zfeat μ a i x := rfl

theorem continuous_Yf (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] : Continuous (Yf ha0 has μ) := by
  classical
  have hc := continuous_mkLp (Z := Torus d) (ι := Idx d)
    (fun x i => Zfeat μ a i x) _ ((summable_fbound_sq ha0 has).mul_left 4)
    (fun x i => Zfeat_sq_le μ i x) (fun i => continuous_Zfeat μ i)
  exact hc

theorem norm_sq_Yf_le (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (x : Torus d) :
    ‖Yf ha0 has μ x‖ ^ 2 ≤ 4 * ∑' i : Idx d, fbound a i * fbound a i := by
  rw [FeatSp.norm_sq, ← tsum_mul_left]
  exact Summable.tsum_le_tsum (fun i => Zfeat_sq_le μ i x) (FeatSp.summable_sq _)
    ((summable_fbound_sq ha0 has).mul_left 4)

end Yfeat


section Yjoint

open HRS Torus

variable {d : ℕ} {m : ℝ} {a : Lattice d → ℝ}

/-- The summand `Y(x) = (δ_x - μ, Z(x)) ∈ H^{-m}_0 ⊕ ℓ²`. -/
def Yj (m : ℝ) (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] (x : Torus d) : JSp d m :=
  WithLp.toLp 2 (Ye m μ x, Yf ha0 has μ x)

theorem continuous_Yj (hm : (d : ℝ) < 2 * m) (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] : Continuous (Yj m ha0 has μ) :=
  (WithLp.prod_continuous_toLp 2 _ _).comp
    ((continuous_Ye hm μ).prodMk (continuous_Yf ha0 has μ))

/-- The uniform bound on `‖Y‖`. -/
def Mconst (d : ℕ) (m : ℝ) (a : Lattice d → ℝ) : ℝ :=
  Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) +
    4 * ∑' i : Idx d, fbound a i * fbound a i)

theorem Mconst_nonneg : 0 ≤ Mconst d m a := Real.sqrt_nonneg _

theorem norm_Yj_le (hm : (d : ℝ) < 2 * m) (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (x : Torus d) :
    ‖Yj m ha0 has μ x‖ ≤ Mconst d m a := by
  unfold Mconst Yj
  refine Real.le_sqrt_of_sq_le ?_
  rw [WithLp.prod_norm_sq_eq_of_L2]
  refine add_le_add ?_ (norm_sq_Yf_le ha0 has μ x)
  have h := norm_ofMeasureDiff_le hm (Measure.dirac x) μ
  have h0 : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) :=
    tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos _).le _
  have h8 : 0 ≤ 8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) := by linarith
  have : ‖Ye m μ x‖ ^ 2 ≤ 8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) := by
    calc ‖Ye m μ x‖ ^ 2 ≤ Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))) ^ 2 :=
          pow_le_pow_left₀ (norm_nonneg _) h 2
      _ = _ := Real.sq_sqrt h8
  exact this

end Yjoint


section Mean

open HRS Torus

variable {d : ℕ} {m : ℝ} {a : Lattice d → ℝ}

/-- The coordinate functional on `FeatSp`. -/
def fcoordCLM (i : Idx d) : FeatSp d →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun F => FeatSp.coord F i, map_add' := fun _ _ => rfl,
      map_smul' := fun _ _ => rfl }
    1 (fun F => by
      have := lp.norm_apply_le_norm (by norm_num : (2 : ℝ≥0∞) ≠ 0)
        (show lp (fun _ : Idx d => ℝ) 2 from F) i
      show ‖(show lp (fun _ : Idx d => ℝ) 2 from F) i‖ ≤ 1 * ‖F‖
      rw [one_mul]; exact this)

theorem fcoordCLM_apply (i : Idx d) (F : FeatSp d) : fcoordCLM i F = FeatSp.coord F i := rfl

theorem integral_Ye_eq_zero (hm : (d : ℝ) < 2 * m) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] : ∫ x, Ye m μ x ∂μ = 0 := by
  have hfst : Integrable (fun x => Ye m μ x) μ :=
    Integrable.of_bound (continuous_Ye hm μ).aestronglyMeasurable
      (Real.sqrt (8 * ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m))))
      (Filter.Eventually.of_forall fun x => norm_ofMeasureDiff_le hm (Measure.dirac x) μ)
  refine NegSobolev.ext_coord' fun k => ?_
  have h := ContinuousLinearMap.integral_comp_comm (negCoordCLM (m := m) k) hfst (μ := μ)
  have h0 : NegSobolev.coord (0 : NegSobolev d m) k = 0 := rfl
  rw [h0, ← negCoordCLM_apply, ← h]
  simp only [negCoordCLM_apply, coord_Ye hm]
  rw [integral_const_mul]
  have : ∫ x, (Torus.realMode k x - Torus.measureRealCoeff μ k) ∂μ = 0 := by
    rw [integral_sub, integral_const]
    · simp [Torus.measureRealCoeff]
    · exact (continuous_realMode' k).integrable_of_hasCompactSupport
        (HasCompactSupport.of_compactSpace _)
    · exact integrable_const _
  rw [this, mul_zero]

theorem integral_Yf_eq_zero (ha0 : ∀ k, 0 ≤ a k) (has : Summable a) (μ : Measure (Torus d))
    [IsProbabilityMeasure μ] : ∫ x, Yf ha0 has μ x ∂μ = 0 := by
  have hsnd : Integrable (fun x => Yf ha0 has μ x) μ :=
    Integrable.of_bound (continuous_Yf ha0 has μ).aestronglyMeasurable
      (Real.sqrt (4 * ∑' i : Idx d, fbound a i * fbound a i))
      (Filter.Eventually.of_forall fun x => by
        refine Real.le_sqrt_of_sq_le ?_
        exact norm_sq_Yf_le ha0 has μ x)
  refine FeatSp.ext_coord fun i => ?_
  have h := ContinuousLinearMap.integral_comp_comm (fcoordCLM (d := d) i) hsnd (μ := μ)
  have h0 : FeatSp.coord (0 : FeatSp d) i = 0 := rfl
  rw [h0, ← fcoordCLM_apply, ← h]
  simp only [fcoordCLM_apply, coord_Yf]
  unfold Zfeat mfeat
  rw [integral_sub, integral_const]
  · simp
  · exact (continuous_feat (a := a) i).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  · exact integrable_const _

theorem integral_Yj_eq_zero (hm : (d : ℝ) < 2 * m) (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] :
    ∫ x, Yj m ha0 has μ x ∂μ = 0 := by
  have hint : Integrable (Yj m ha0 has μ) μ :=
    Integrable.of_bound (continuous_Yj hm ha0 has μ).aestronglyMeasurable (Mconst d m a)
      (Filter.Eventually.of_forall fun x => norm_Yj_le hm ha0 has μ x)
  have h1 := ContinuousLinearMap.integral_comp_comm (WithLp.fstL 2 ℝ (NegSobolev d m) (FeatSp d))
    hint (μ := μ)
  have h2 := ContinuousLinearMap.integral_comp_comm (WithLp.sndL 2 ℝ (NegSobolev d m) (FeatSp d))
    hint (μ := μ)
  simp only [WithLp.fstL_apply, WithLp.sndL_apply] at h1 h2
  have h1' : (∫ x, Yj m ha0 has μ x ∂μ).fst = 0 := by
    rw [← integral_Ye_eq_zero hm μ]; exact h1.symm
  have h2' : (∫ x, Yj m ha0 has μ x ∂μ).snd = 0 := by
    rw [← integral_Yf_eq_zero ha0 has μ]; exact h2.symm
  apply WithLp.ofLp_injective 2
  exact Prod.ext h1' h2'

end Mean


section Subspaces

open HRS Torus

variable {d : ℕ} {m : ℝ}

open Classical in
/-- The linear embedding of the first factor. -/
def Phi1 (d : ℕ) (m : ℝ) : NegSobolev d m →ₗ[ℝ] JSp d m :=
  (WithLp.linearEquiv 2 ℝ (NegSobolev d m × FeatSp d)).symm.toLinearMap ∘ₗ
    LinearMap.inl ℝ (NegSobolev d m) (FeatSp d)

/-- The linear embedding of the second factor. -/
def Phi2 (d : ℕ) (m : ℝ) : FeatSp d →ₗ[ℝ] JSp d m :=
  (WithLp.linearEquiv 2 ℝ (NegSobolev d m × FeatSp d)).symm.toLinearMap ∘ₗ
    LinearMap.inr ℝ (NegSobolev d m) (FeatSp d)

theorem Phi1_apply (e : NegSobolev d m) : Phi1 d m e = WithLp.toLp 2 (e, (0 : FeatSp d)) := rfl

theorem Phi2_apply (f : FeatSp d) : Phi2 d m f = WithLp.toLp 2 ((0 : NegSobolev d m), f) := rfl

/-- Unit vectors. -/
def singleE (d : ℕ) (m : ℝ) (k : NonzeroLattice d) : NegSobolev d m :=
  (lp.single 2 k (1 : ℝ) : lp (fun _ : NonzeroLattice d => ℝ) 2)

/-- Unit vectors. -/
def singleF (d : ℕ) (i : Idx d) : FeatSp d :=
  (lp.single 2 i (1 : ℝ) : lp (fun _ : Idx d => ℝ) 2)

open Classical in
/-- Finite-dimensional coordinate subspace. -/
def Ksub (d : ℕ) (m : ℝ) (S₁ : Finset (NonzeroLattice d)) (S₂ : Finset (Idx d)) :
    Submodule ℝ (JSp d m) :=
  Submodule.span ℝ
    ((fun k => Phi1 d m (singleE d m k)) '' (S₁ : Set (NonzeroLattice d)) ∪
     (fun i => Phi2 d m (singleF d i)) '' (S₂ : Set (Idx d)))

theorem finiteDimensional_Ksub (S₁ : Finset (NonzeroLattice d)) (S₂ : Finset (Idx d)) :
    FiniteDimensional ℝ (Ksub d m S₁ S₂) := by
  classical
  unfold Ksub
  exact FiniteDimensional.span_of_finite ℝ
    (((Set.toFinite _).image _).union ((Set.toFinite _).image _))

open Classical in
/-- Coordinate truncation in `H^{-m}_0`. -/
def truncE (S : Finset (NonzeroLattice d)) (e : NegSobolev d m) : NegSobolev d m :=
  truncLp S (show lp (fun _ : NonzeroLattice d => ℝ) 2 from e)

open Classical in
/-- Coordinate truncation in `FeatSp`. -/
def truncF (S : Finset (Idx d)) (f : FeatSp d) : FeatSp d :=
  truncLp S (show lp (fun _ : Idx d => ℝ) 2 from f)

open Classical in
theorem coord_truncE (S : Finset (NonzeroLattice d)) (e : NegSobolev d m) (k : NonzeroLattice d) :
    NegSobolev.coord (truncE S e) k = if k ∈ S then NegSobolev.coord e k else 0 :=
  truncLp_apply S (show lp (fun _ : NonzeroLattice d => ℝ) 2 from e) k

open Classical in
theorem coord_truncF (S : Finset (Idx d)) (f : FeatSp d) (i : Idx d) :
    FeatSp.coord (truncF S f) i = if i ∈ S then FeatSp.coord f i else 0 :=
  truncLp_apply S (show lp (fun _ : Idx d => ℝ) 2 from f) i

open Classical in
theorem Phi1_truncE_mem (S₁ : Finset (NonzeroLattice d)) (S₂ : Finset (Idx d)) (e : NegSobolev d m) :
    Phi1 d m (truncE S₁ e) ∈ Ksub d m S₁ S₂ := by
  have h : truncE S₁ e = ∑ i ∈ S₁, NegSobolev.coord e i • singleE d m i := rfl
  rw [h, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inl ⟨i, hi, rfl⟩))

open Classical in
theorem Phi2_truncF_mem (S₁ : Finset (NonzeroLattice d)) (S₂ : Finset (Idx d)) (f : FeatSp d) :
    Phi2 d m (truncF S₂ f) ∈ Ksub d m S₁ S₂ := by
  have h : truncF S₂ f = ∑ i ∈ S₂, FeatSp.coord f i • singleF d i := rfl
  rw [h, map_sum]
  refine Submodule.sum_mem _ fun i hi => ?_
  rw [map_smul]
  exact Submodule.smul_mem _ _ (Submodule.subset_span (Or.inr ⟨i, hi, rfl⟩))


instance instHOP (S₁ : Finset (NonzeroLattice d)) (S₂ : Finset (Idx d)) :
    (Ksub d m S₁ S₂).HasOrthogonalProjection := by
  haveI := finiteDimensional_Ksub (m := m) S₁ S₂
  haveI : CompleteSpace (Ksub d m S₁ S₂) := FiniteDimensional.complete ℝ _
  infer_instance

open Classical in
theorem sub_starProjection_sq_le (S₁ : Finset (NonzeroLattice d)) (S₂ : Finset (Idx d))
    (v : JSp d m) (bE : NonzeroLattice d → ℝ) (bF : Idx d → ℝ) (hbE : Summable bE)
    (hbF : Summable bF) (hvE : ∀ k, NegSobolev.coord v.fst k ^ 2 ≤ bE k)
    (hvF : ∀ i, FeatSp.coord v.snd i ^ 2 ≤ bF i) :
    ‖v - (Ksub d m S₁ S₂).starProjection v‖ ^ 2 ≤
      ∑' k : {x // x ∉ S₁}, bE k + ∑' i : {x // x ∉ S₂}, bF i := by
  set u : JSp d m := Phi1 d m (truncE S₁ v.fst) + Phi2 d m (truncF S₂ v.snd) with hu
  have hum : u ∈ Ksub d m S₁ S₂ :=
    Submodule.add_mem _ (Phi1_truncE_mem S₁ S₂ _) (Phi2_truncF_mem S₁ S₂ _)
  have h1 : ‖v - (Ksub d m S₁ S₂).starProjection v‖ ≤ ‖v - u‖ := by
    rw [Submodule.starProjection_minimal]
    exact ciInf_le (f := fun x : Ksub d m S₁ S₂ => ‖v - x‖) ⟨0, fun _ ⟨y, hy⟩ => hy ▸ norm_nonneg _⟩
      ⟨u, hum⟩
  have h2 : ‖v - u‖ ^ 2 = ‖v.fst - truncE S₁ v.fst‖ ^ 2 + ‖v.snd - truncF S₂ v.snd‖ ^ 2 := by
    rw [WithLp.prod_norm_sq_eq_of_L2]
    congr 2 <;> simp [hu, Phi1_apply, Phi2_apply]
  have h3 : ‖v.fst - truncE S₁ v.fst‖ ^ 2 ≤ ∑' k : {x // x ∉ S₁}, bE k :=
    norm_sub_truncLp_sq_le (show lp (fun _ : NonzeroLattice d => ℝ) 2 from v.fst) S₁ bE hbE hvE
  have h4 : ‖v.snd - truncF S₂ v.snd‖ ^ 2 ≤ ∑' i : {x // x ∉ S₂}, bF i :=
    norm_sub_truncLp_sq_le (show lp (fun _ : Idx d => ℝ) 2 from v.snd) S₂ bF hbF hvF
  calc ‖v - (Ksub d m S₁ S₂).starProjection v‖ ^ 2 ≤ ‖v - u‖ ^ 2 :=
        pow_le_pow_left₀ (norm_nonneg _) h1 2
    _ ≤ _ := by rw [h2]; exact add_le_add h3 h4

end Subspaces


section Tails

open HRS Torus

variable {d : ℕ} {m : ℝ} {a : Lattice d → ℝ}

open Classical in
/-- An exhausting sequence of finite sets of lattice frequencies. -/
def seqE (d : ℕ) : ℕ → Finset (NonzeroLattice d) :=
  Classical.choose (Filter.exists_seq_tendsto (Filter.atTop : Filter (Finset (NonzeroLattice d))))

open Classical in
theorem tendsto_seqE (d : ℕ) : Tendsto (seqE d) atTop atTop :=
  Classical.choose_spec (Filter.exists_seq_tendsto (Filter.atTop : Filter (Finset (NonzeroLattice d))))

open Classical in
/-- An exhausting sequence of finite sets of feature indices. -/
def seqF (d : ℕ) : ℕ → Finset (Idx d) :=
  Classical.choose (Filter.exists_seq_tendsto (Filter.atTop : Filter (Finset (Idx d))))

open Classical in
theorem tendsto_seqF (d : ℕ) : Tendsto (seqF d) atTop atTop :=
  Classical.choose_spec (Filter.exists_seq_tendsto (Filter.atTop : Filter (Finset (Idx d))))

/-- The finite-dimensional approximating subspaces. -/
abbrev Kseq (d : ℕ) (m : ℝ) (n : ℕ) : Submodule ℝ (JSp d m) := Ksub d m (seqE d n) (seqF d n)

/-- The tail modulus. -/
def tauSeq (d : ℕ) (m : ℝ) (a : Lattice d → ℝ) (n : ℕ) : ℝ :=
  ∑' k : {x // x ∉ seqE d n}, 8 * Lattice.jp k.1.1 ^ (-(2 * m)) +
    ∑' i : {x // x ∉ seqF d n}, 4 * (fbound a i * fbound a i)

theorem tendsto_tauSeq : Tendsto (tauSeq d m a) atTop (𝓝 0) := by
  have h1 := (tendsto_tsum_compl_atTop_zero (fun k : NonzeroLattice d =>
    8 * Lattice.jp k.1 ^ (-(2 * m)))).comp (tendsto_seqE d)
  have h2 := (tendsto_tsum_compl_atTop_zero (fun i : Idx d =>
    4 * (fbound a i * fbound a i))).comp (tendsto_seqF d)
  have := h1.add h2
  rw [add_zero] at this
  exact this

theorem tail_Yj (hm : (d : ℝ) < 2 * m) (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (μ : Measure (Torus d)) [IsProbabilityMeasure μ] (n : ℕ) (x : Torus d) :
    ‖Yj m ha0 has μ x - (Kseq d m n).starProjection (Yj m ha0 has μ x)‖ ^ 2 ≤ tauSeq d m a n := by
  unfold Kseq tauSeq
  refine sub_starProjection_sq_le (seqE d n) (seqF d n) (Yj m ha0 has μ x) _ _
    ((summable_jp_rpow (d := d) m hm).mul_left 8) ((summable_fbound_sq ha0 has).mul_left 4)
    (fun k => ?_) (fun i => ?_)
  · exact coord_sq_le_ofMeasureDiff hm (Measure.dirac x) μ k
  · exact Zfeat_sq_le μ i x

end Tails


section Instantiate

open HRS Torus

variable {d : ℕ} {m : ℝ} {a : Lattice d → ℝ}

/-- The norm of the feature component. -/
def qJ (d : ℕ) (m : ℝ) (v : JSp d m) : ℝ := ‖v.snd‖

/-- The `E`-component. -/
def TJ (d : ℕ) (m : ℝ) (v : JSp d m) : NegSobolev d m := v.fst

theorem norm_fst_le (z : JSp d m) : ‖z.fst‖ ≤ ‖z‖ := by
  have := WithLp.prod_norm_sq_eq_of_L2 z
  nlinarith [norm_nonneg z, norm_nonneg z.fst, norm_nonneg z.snd, sq_nonneg ‖z.snd‖]

theorem norm_snd_le (z : JSp d m) : ‖z.snd‖ ≤ ‖z‖ := by
  have := WithLp.prod_norm_sq_eq_of_L2 z
  nlinarith [norm_nonneg z, norm_nonneg z.fst, norm_nonneg z.snd, sq_nonneg ‖z.fst‖]

theorem measurable_qJ : Measurable (qJ d m) :=
  (continuous_norm.comp (WithLp.continuous_snd 2 _ _)).measurable

theorem measurable_TJ : Measurable (TJ d m) :=
  (WithLp.continuous_fst 2 _ _).measurable

theorem qJ_lip (x y : JSp d m) : |qJ d m x - qJ d m y| ≤ ‖x - y‖ := by
  unfold qJ
  refine (abs_norm_sub_norm_le _ _).trans ?_
  rw [← WithLp.sub_snd]
  exact norm_snd_le _

theorem qJ_abs_le (v : JSp d m) : |qJ d m v| ≤ ‖v‖ := by
  unfold qJ
  rw [abs_of_nonneg (norm_nonneg _)]
  exact norm_snd_le _

theorem TJ_lip (x y : JSp d m) : ‖TJ d m x - TJ d m y‖ ≤ ‖x - y‖ := by
  unfold TJ
  rw [← WithLp.sub_fst]
  exact norm_fst_le _

/-- The tilted CLT transfer for the joint summands `Y_ρ`, uniform in the density. -/
theorem joint_transfer (hm : (d : ℝ) < 2 * m) (ha0 : ∀ k, 0 ≤ a k) (has : Summable a)
    (B : ℝ) (hB : 0 ≤ B) :
    ∀ ε > 0, ∃ N₀ : ℕ, ∀ N ≥ N₀, ∀ (μ : Measure (Torus d)) [IsProbabilityMeasure μ],
      ∀ β ∈ Set.Icc (0 : ℝ) B, ∀ Γ : Measure (JSp d m), HRS.IsCenteredGaussian Γ →
        (∀ x y, ProbabilityTheory.covarianceBilin Γ x y =
          ProbabilityTheory.covarianceBilin (μ.map (Yj m ha0 has μ)) x y) →
        wassersteinE 2 ((tiltMeasure (tw (qJ d m) β) Γ).map (TJ d m))
          ((tiltMeasure (tw (qJ d m) β)
            ((Measure.pi fun _ : Fin N => μ).map (Ssum (Yj m ha0 has μ) N))).map (TJ d m)) ≤
          ENNReal.ofReal ε := by
  intro ε hε
  obtain ⟨N₀, hN₀⟩ := tilt_clt_transfer (X := Torus d) (qJ d m) measurable_qJ qJ_lip qJ_abs_le
    (TJ d m) measurable_TJ TJ_lip (Kseq d m) (fun n => finiteDimensional_Ksub _ _) (tauSeq d m a)
    tendsto_tauSeq (Mconst d m a) Mconst_nonneg B hB ε hε
  refine ⟨N₀, fun N hN μ _ β hβ Γ hΓ hcov => ?_⟩
  exact hN₀ N hN μ (Yj m ha0 has μ) (continuous_Yj hm ha0 has μ).measurable
    (norm_Yj_le hm ha0 has μ) (integral_Yj_eq_zero hm ha0 has μ)
    (fun n x => tail_Yj hm ha0 has μ n x) β hβ Γ hΓ hcov

end Instantiate


section SsumMeas

variable {X : Type} [MeasurableSpace X]
  {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
  [MeasurableSpace H] [BorelSpace H] [SecondCountableTopology H]

theorem measurable_Ssum' {Y : X → H} (hY : Measurable Y) (N : ℕ) : Measurable (Ssum Y N) := by
  unfold Ssum
  have h : Measurable fun z : Fin N → X => ∑ j, Y (z j) :=
    Finset.measurable_sum _ fun j _ => hY.comp (measurable_pi_apply j)
  exact h.const_smul (Real.sqrt N)⁻¹

end SsumMeas

end HRS.StaticLimitAux
