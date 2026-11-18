import HRS.Equilibrium.PairCorrection
import HRS.Energy.StaticLimitGauss
import HRS.Kernel.ResponseD1
import HRS.PDE.Fourier

open MeasureTheory Filter Topology ProbabilityTheory

noncomputable section

namespace HRS.StaticLimitsAux

variable {d : ℕ}

theorem density_bounds {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ a Λ : ℝ, 0 < a ∧ ∀ x, a ≤ ρ x ∧ ρ x ≤ Λ := by
  have hc : Continuous ρ := StaticLimitAux.continuous_of_smooth hρ.smooth
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn Set.univ_nonempty hc.continuousOn
  obtain ⟨x1, -, hx1⟩ := isCompact_univ.exists_isMaxOn Set.univ_nonempty hc.continuousOn
  exact ⟨ρ x0, ρ x1, hρ.pos x0, fun x =>
    ⟨hx0 (Set.mem_univ x), hx1 (Set.mem_univ x)⟩⟩

theorem integrable_cont {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace f)

theorem var_bounds {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {a Λ : ℝ} (ha : 0 < a)
    (hb : ∀ x, a ≤ ρ x ∧ ρ x ≤ Λ) {φ : Torus d → ℝ} (hφ : Continuous φ)
    (h0 : Torus.mean φ = 0) :
    a * ∫ x, φ x ^ 2 ≤ l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) φ)
        (projMean (withDensityReal ρ) φ) ∧
      l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) φ)
        (projMean (withDensityReal ρ) φ) ≤ Λ * ∫ x, φ x ^ 2 := by
  have hρc : Continuous ρ := StaticLimitAux.continuous_of_smooth hρ.smooth
  have hρ0 := hρ.density.nonneg
  have hρm := hρ.density.measurable
  have hΛ : 0 ≤ Λ := le_trans (hρ0 (Classical.arbitrary _)) (hb _).2
  set m := pair (withDensityReal ρ) φ with hm
  have hmeq : m = ∫ x, ρ x * φ x := by
    rw [hm, pair, integral_withDensityReal_eq ρ hρm hρ0]
  have hint1 : Integrable (fun x => ρ x * φ x) := integrable_cont (hρc.mul hφ)
  have hint2 : Integrable (fun x => ρ x * φ x ^ 2) := integrable_cont (hρc.mul (hφ.pow 2))
  have hintρ : Integrable ρ := integrable_cont hρc
  have hintφ2 : Integrable (fun x => φ x ^ 2) := integrable_cont (hφ.pow 2)
  have hintφ : Integrable φ := integrable_cont hφ
  have hV : l2Inner (withDensityReal ρ) (projMean (withDensityReal ρ) φ)
      (projMean (withDensityReal ρ) φ) = ∫ x, ρ x * (φ x - m) ^ 2 := by
    rw [l2Inner, integral_withDensityReal_eq ρ hρm hρ0]
    simp [projMean, ← hm, sq]
  rw [hV]
  have hexp : ∫ x, ρ x * (φ x - m) ^ 2
      = (∫ x, ρ x * φ x ^ 2) - 2 * m * (∫ x, ρ x * φ x) + m ^ 2 * (∫ x, ρ x) := by
    have : (fun x => ρ x * (φ x - m) ^ 2) =
        fun x => (ρ x * φ x ^ 2 - 2 * m * (ρ x * φ x)) + m ^ 2 * ρ x := by
      funext x; ring
    have e1 := integral_add (hint2.sub (hint1.const_mul (2 * m))) (hintρ.const_mul (m ^ 2))
    have e2 := integral_sub hint2 (hint1.const_mul (2 * m))
    simp only [Pi.sub_apply] at e1 e2
    rw [this, e1, e2, integral_const_mul, integral_const_mul]
  rw [hρ.density.integral_one, ← hmeq] at hexp
  constructor
  · have h1 : ∫ x, a * (φ x - m) ^ 2 ≤ ∫ x, ρ x * (φ x - m) ^ 2 :=
      integral_mono (((hintφ2.sub (hintφ.const_mul (2 * m))).add
        (integrable_const (m ^ 2))).const_mul a |>.congr (Eventually.of_forall fun x => by
          simp only [Pi.add_apply, Pi.sub_apply]; ring))
        (integrable_cont (hρc.mul ((hφ.sub continuous_const).pow 2)))
        fun x => mul_le_mul_of_nonneg_right (hb x).1 (sq_nonneg _)
    have h2 : ∫ x, a * (φ x - m) ^ 2 = a * ((∫ x, φ x ^ 2) + m ^ 2) := by
      have : (fun x => a * (φ x - m) ^ 2) =
          fun x => a * (φ x ^ 2 - (2 * m) * φ x + m ^ 2) := by funext x; ring
      have e1 := integral_add (hintφ2.sub (hintφ.const_mul (2 * m))) (integrable_const (m ^ 2))
      have e2 := integral_sub hintφ2 (hintφ.const_mul (2 * m))
      simp only [Pi.sub_apply] at e1 e2
      rw [this, integral_const_mul, e1, e2, integral_const_mul]
      have h0' : ∫ x, φ x = 0 := h0
      simp [h0']
    rw [h2] at h1
    nlinarith [sq_nonneg m]
  · have h3 : ∫ x, ρ x * φ x ^ 2 ≤ ∫ x, Λ * φ x ^ 2 :=
      integral_mono hint2 (hintφ2.const_mul Λ)
        fun x => mul_le_mul_of_nonneg_right (hb x).2 (sq_nonneg _)
    rw [integral_const_mul] at h3
    rw [hexp]; nlinarith [sq_nonneg m]

theorem comparable_of_susc {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ)
    (hβ : 0 ≤ β) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) :
    ∃ c C : ℝ, 0 < c ∧ ∀ φ : Torus d → ℝ, Torus.IsSmooth φ → Torus.mean φ = 0 →
      c * ∫ x, φ x ^ 2 ≤ susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β φ φ ∧
      susceptibilityCov (periodicRiesz d s) (withDensityReal ρ) β φ φ ≤ C * ∫ x, φ x ^ 2 := by
  obtain ⟨a, Λ, ha, hb⟩ := density_bounds hρ
  obtain ⟨c, C, hc, H⟩ := susceptibilityCov_bounds hd hs0 hsd ρ hρ.density Λ (fun x => (hb x).2) β hβ
  haveI := isProb_withDensityReal hρ.density
  refine ⟨c * a, max C 0 * Λ, mul_pos hc ha, fun φ hφ h0 => ?_⟩
  have hcont := StaticLimitAux.continuous_of_smooth hφ
  have hml : MemLp φ 2 (withDensityReal ρ) := by
    obtain ⟨M, hM⟩ := (isCompact_univ.exists_bound_of_continuousOn hcont.continuousOn)
    exact MemLp.of_bound hcont.aestronglyMeasurable M
      (Filter.Eventually.of_forall fun x => hM x (Set.mem_univ x))
  obtain ⟨hlo, hup⟩ := var_bounds hρ ha hb hcont h0
  obtain ⟨h1, h2⟩ := H φ hml
  have hnn : 0 ≤ ∫ x, φ x ^ 2 := integral_nonneg fun x => sq_nonneg _
  constructor
  · calc c * a * ∫ x, φ x ^ 2 = c * (a * ∫ x, φ x ^ 2) := by ring
      _ ≤ _ := le_trans (mul_le_mul_of_nonneg_left hlo hc.le) h1
  · have hΛ0 : 0 ≤ Λ := le_trans ha.le (hb (Classical.arbitrary _)).1 |>.trans (hb _).2
    calc _ ≤ C * _ := h2
      _ ≤ max C 0 * _ := mul_le_mul_of_nonneg_right (le_max_left _ _)
            (le_trans (by positivity : 0 ≤ a * ∫ x, φ x ^ 2) hlo |> fun h =>
              le_trans (mul_nonneg ha.le hnn) hlo)
      _ ≤ max C 0 * (Λ * ∫ x, φ x ^ 2) := mul_le_mul_of_nonneg_left hup (le_max_right _ _)
      _ = _ := by ring

/-! ### Positivity of `J` -/

theorem isCk_two_of_smooth {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) : Torus.IsCk 2 φ :=
  ContDiff.of_le (show ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift φ) from hφ)
    (by norm_cast)

theorem continuous_partialDeriv {ψ : Torus d → ℝ} (hψ : Torus.IsCk 1 ψ) (i : Fin d) :
    Continuous (Torus.partialDeriv i ψ) := by
  refine Torus.continuous_of_continuous_lift ?_
  rw [HRS.PDE.lift_partialDeriv i ψ hψ]
  exact ((show ContDiff ℝ 1 (Torus.lift ψ) from hψ).continuous_fderiv one_ne_zero).clm_apply
    continuous_const

theorem clm_ext_basis {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]
    (L M : Euc d →L[ℝ] F)
    (h : ∀ j : Fin d, L (EuclideanSpace.single j 1) = M (EuclideanSpace.single j 1)) : L = M := by
  ext v
  have hv : v = ∑ j, v j • (EuclideanSpace.single j (1 : ℝ) : Euc d) := by
    ext k; simp [Finset.sum_apply, Pi.single_apply]
  rw [hv]
  simp only [map_sum, map_smul, h]

theorem const_of_second_zero {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ)
    (h : ∀ i j x, Torus.partialDeriv i (Torus.partialDeriv j φ) x = 0) (x y : Torus d) :
    φ x = φ y := by
  have h2 := isCk_two_of_smooth hφ
  have h1 : Torus.IsCk 1 φ := h2.of_le (by norm_num)
  set f := Torus.lift φ with hf
  have hfc : ContDiff ℝ 2 f := h2
  have hdf : Differentiable ℝ f := hfc.differentiable (by norm_num)
  -- each directional derivative is constant
  have hg : ∀ j : Fin d, ∀ z : Euc d, fderiv ℝ f z (EuclideanSpace.single j 1)
      = fderiv ℝ f 0 (EuclideanSpace.single j 1) := by
    intro j z
    have hlj := HRS.PDE.lift_partialDeriv j φ h1
    have hψ : Torus.IsCk 1 (Torus.partialDeriv j φ) := HRS.PDE.isCk_one_partialDeriv j φ h2
    have hdiff : Differentiable ℝ (Torus.lift (Torus.partialDeriv j φ)) :=
      (show ContDiff ℝ 1 _ from hψ).differentiable one_ne_zero
    have hz : fderiv ℝ (Torus.lift (Torus.partialDeriv j φ)) = 0 := by
      funext w
      refine clm_ext_basis _ _ fun i => ?_
      have := HRS.PDE.lift_partialDeriv i (Torus.partialDeriv j φ) hψ
      have e := congrFun this w
      exact e.symm.trans (h i j (Torus.mk w))
    have hc := is_const_of_fderiv_eq_zero hdiff (fun w => by simp [hz]) z 0
    rw [hlj] at hc
    exact hc
  have hfd : ∀ z, fderiv ℝ f z = fderiv ℝ f 0 :=
    fun z => clm_ext_basis _ _ fun j => hg j z
  have hconst : ∀ z, f z = f 0 + fderiv ℝ f 0 z := by
    intro z
    have hd : Differentiable ℝ (fun w => f w - fderiv ℝ f 0 w) :=
      hdf.sub (fderiv ℝ f 0).differentiable
    have hz : ∀ w, fderiv ℝ (fun w => f w - fderiv ℝ f 0 w) w = 0 := by
      intro w
      rw [fderiv_fun_sub (hdf w) (fderiv ℝ f 0).differentiableAt, hfd w]
      simp
    have := is_const_of_fderiv_eq_zero hd (fun w => hz w) z 0
    simp at this
    linarith
  have hl0 : fderiv ℝ f 0 = 0 := by
    refine clm_ext_basis _ _ fun j => ?_
    have hp := Torus.lift_periodic φ 0 (Pi.single j 1)
    have he : Lattice.toEuc (Pi.single j (1 : ℤ) : Lattice d) =
        (EuclideanSpace.single j 1 : Euc d) := by
      ext k
      by_cases hk : k = j <;> simp [Lattice.toEuc, Pi.single_apply, hk]
    have hp' : f (EuclideanSpace.single j 1) = f 0 := by simpa [hf, he] using hp
    have := hconst (EuclideanSpace.single j 1)
    simp
    linarith
  have hall : ∀ z, f z = f 0 := fun z => by rw [hconst z, hl0]; simp
  have hx : φ x = f (Torus.rep x) := by simp [hf, Torus.lift, Torus.mk_rep]
  have hy : φ y = f (Torus.rep y) := by simp [hf, Torus.lift, Torus.mk_rep]
  rw [hx, hy, hall (Torus.rep x), hall (Torus.rep y)]

theorem continuous_second {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) (i j : Fin d) :
    Continuous (Torus.partialDeriv i (Torus.partialDeriv j φ)) :=
  continuous_partialDeriv (HRS.PDE.isCk_one_partialDeriv j φ (isCk_two_of_smooth hφ)) i

theorem continuous_laplacian {φ : Torus d → ℝ} (hφ : Torus.IsSmooth φ) :
    Continuous (Torus.laplacian φ) := by
  have : Torus.laplacian φ = fun x => ∑ j, Torus.partialDeriv j (Torus.partialDeriv j φ) x :=
    funext (HRS.PDE.laplacian_eq_sum φ (isCk_two_of_smooth hφ))
  rw [this]
  exact continuous_finset_sum _ fun j _ => continuous_second hφ j j

theorem sphereArea_pos (hd : 2 ≤ d) : 0 < sphereArea d := by
  unfold sphereArea
  have : 0 < Real.Gamma ((d : ℝ) / 2) := Real.Gamma_pos_of_pos (by
    have : (2 : ℝ) ≤ d := by exact_mod_cast hd
    linarith)
  positivity

/-! ### Symmetric half-probability (Example 5.11, explicit case) -/

theorem circle_singleton_null (x : UnitAddCircle) : (volume : Measure UnitAddCircle) {x} = 0 := by
  refine le_antisymm ?_ bot_le
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  have hx : ({x} : Set UnitAddCircle) ⊆ Metric.closedBall x (ε / 2 : ℝ) := by
    intro y hy; rw [Set.mem_singleton_iff.mp hy]; exact Metric.mem_closedBall_self (by positivity)
  calc (volume : Measure UnitAddCircle) {x} ≤ volume (Metric.closedBall x ((ε : ℝ) / 2)) := measure_mono hx
    _ = ENNReal.ofReal (min 1 (2 * ((ε : ℝ) / 2))) := by rw [AddCircle.volume_closedBall]
    _ ≤ ε := by
      calc _ ≤ ENNReal.ofReal ε := ENNReal.ofReal_le_ofReal (by
              refine (min_le_right _ _).trans (le_of_eq ?_); ring)
        _ = ε := by simp
    _ ≤ 0 + ε := by simp

theorem circle_finite_null (S : Set UnitAddCircle) (hS : S.Finite) :
    (volume : Measure UnitAddCircle) S = 0 := by
  have : NullSingletonClass (volume : Measure UnitAddCircle) := ⟨circle_singleton_null⟩
  exact hS.measure_zero _

theorem circle_re_null (c : ℝ) :
    (volume : Measure UnitAddCircle) {t : UnitAddCircle | (fourier (1:ℤ) t).re = c} = 0 := by
  apply circle_finite_null
  have hinj : Function.Injective (fun t : UnitAddCircle => fourier (1:ℤ) t) := by
    intro a b h
    simp only [fourier_one] at h
    exact AddCircle.injective_toCircle one_ne_zero (Subtype.ext h)
  have hfin : Set.Finite {w : ℂ | w.re = c ∧ ‖w‖ = 1} := by
    refine (Set.toFinite {(⟨c, Real.sqrt (1 - c^2)⟩ : ℂ), ⟨c, -Real.sqrt (1 - c^2)⟩}).subset ?_
    rintro w ⟨h1, h2⟩
    have h3 : w.im ^ 2 = 1 - c ^ 2 := by
      have := Complex.sq_norm w
      rw [h2, Complex.normSq_apply, h1] at this
      nlinarith
    have h4 : 0 ≤ 1 - c ^ 2 := by rw [← h3]; positivity
    have h5 : w.im = Real.sqrt (1 - c^2) ∨ w.im = -Real.sqrt (1 - c^2) := by
      have : w.im ^ 2 = (Real.sqrt (1 - c^2)) ^ 2 := by rw [Real.sq_sqrt h4, h3]
      exact sq_eq_sq_iff_eq_or_eq_neg.mp this
    rcases h5 with h | h
    · left; exact Complex.ext h1 h
    · right; exact Complex.ext h1 h
  exact (hfin.preimage hinj.injOn).subset fun t ht => ⟨ht, by simp⟩

theorem mode_e0 {d : ℕ} (j : Fin d) (u : Torus d) :
    Torus.cosMode (Pi.single j 1 : HRS.Lattice d) u = (fourier (1:ℤ) (u j)).re := by
  unfold Torus.cosMode Torus.mode UnitAddTorus.mFourier
  simp only [ContinuousMap.coe_mk]
  rw [Finset.prod_eq_single j]
  · simp
  · intro i _ hi; simp [Pi.single_apply, hi]
  · simp

theorem null_cos_sum (n : ℕ) {d : ℕ} (j : Fin d) :
    (volume : Measure (Config d (n+1)))
      {X | ∑ i, Torus.cosMode (Pi.single j 1 : HRS.Lattice d) (X i) = 0} = 0 := by
  have mp := measurePreserving_piFinSuccAbove (fun _ : Fin (n+1) => (volume : Measure (Torus d))) 0
  set S' : Set (Torus d × (Fin n → Torus d)) :=
    {p | Torus.cosMode (Pi.single j 1 : HRS.Lattice d) p.1 +
      ∑ k, Torus.cosMode (Pi.single j 1 : HRS.Lattice d) (p.2 k) = 0} with hS'
  have hmeas : MeasurableSet S' := by
    have hc : Continuous (Torus.cosMode (Pi.single j 1 : HRS.Lattice d)) :=
      Complex.continuous_re.comp (Torus.continuous_mode _)
    refine measurableSet_eq_fun ?_ measurable_const
    exact (hc.measurable.comp measurable_fst).add
      (Finset.measurable_sum _ fun k _ => hc.measurable.comp ((measurable_pi_apply k).comp measurable_snd))
  have hpre : {X : Config d (n+1) | ∑ i, Torus.cosMode (Pi.single j 1 : HRS.Lattice d) (X i) = 0}
      = (MeasurableEquiv.piFinSuccAbove (fun _ : Fin (n+1) => Torus d) 0) ⁻¹' S' := by
    ext X
    simp only [Set.mem_setOf_eq, Set.mem_preimage, hS', MeasurableEquiv.piFinSuccAbove_apply,
      Fin.sum_univ_succ, Fin.succAbove_zero]
    rfl
  rw [hpre]
  show (Measure.pi fun _ : Fin (n+1) => (volume : Measure (Torus d))) _ = 0
  rw [mp.measure_preimage_equiv, Measure.prod_apply_symm hmeas]
  have hfib : ∀ y : Fin n → Torus d,
      (volume : Measure (Torus d)) ((fun x => (x, y)) ⁻¹' S') = 0 := by
    intro y
    set c := ∑ k, Torus.cosMode (Pi.single j 1 : HRS.Lattice d) (y k) with hc
    have e1 : (fun x => (x, y)) ⁻¹' S' =
        (fun x : Torus d => x j) ⁻¹' {t : UnitAddCircle | (fourier (1:ℤ) t).re = -c} := by
      ext x
      simp only [hS', Set.mem_preimage, Set.mem_setOf_eq, mode_e0]
      have hc2 : c = ∑ k, (fourier (1:ℤ) (y k j)).re := by simp only [hc, mode_e0]
      constructor <;> intro h <;> linarith
    rw [e1]
    have hmp := measurePreserving_eval (fun _ : Fin d => (volume : Measure UnitAddCircle)) j
    have hm : MeasurableSet {t : UnitAddCircle | (fourier (1:ℤ) t).re = -c} :=
      (isClosed_eq (Complex.continuous_re.comp (fourier (1:ℤ)).continuous) continuous_const).measurableSet
    have := hmp.measure_preimage hm.nullMeasurableSet
    refine (this.trans ?_)
    exact circle_re_null (-c)
  simp [hfib]


theorem prob_half {d N : ℕ} (P : Measure (Config d N)) [IsProbabilityMeasure P]
    (t : Torus d) (hinv : P.map (shiftEquiv t : Config d N ≃ᵐ Config d N) = P)
    (Z : Config d N → ℝ) (hZ : Measurable Z) (hneg : ∀ X, Z (shiftEquiv t X) = -Z X)
    (hnull : P {X | Z X = 0} = 0) : (P {X | 0 < Z X}).toReal = 1 / 2 := by
  have h1 : P {X | 0 < Z X} = P {X | Z X < 0} := by
    have hm : MeasurableSet {X | Z X < 0} := measurableSet_lt hZ measurable_const
    have := congrArg (fun Q => Q {X | Z X < 0}) hinv
    rw [Measure.map_apply (shiftEquiv t).measurable hm] at this
    rw [← this]
    congr 1
    ext X; simp [hneg]
  have h2 : P {X | 0 < Z X} + P {X | Z X < 0} + P {X | Z X = 0} = 1 := by
    have e : (Set.univ : Set (Config d N)) = {X | 0 < Z X} ∪ {X | Z X < 0} ∪ {X | Z X = 0} := by
      ext X; simp only [Set.mem_univ, Set.mem_union, Set.mem_setOf_eq, true_iff]
      rcases lt_trichotomy (Z X) 0 with h | h | h
      · exact Or.inl (Or.inr h)
      · exact Or.inr h
      · exact Or.inl (Or.inl h)
    have hA : MeasurableSet {X | 0 < Z X} := measurableSet_lt measurable_const hZ
    have hB : MeasurableSet {X | Z X < 0} := measurableSet_lt hZ measurable_const
    have hC : MeasurableSet {X | Z X = 0} := measurableSet_eq_fun hZ measurable_const
    rw [← measure_univ (μ := P), e, measure_union _ hC, measure_union _ hB]
    · exact Set.disjoint_left.2 fun X hX hX' => by
        have h1 : 0 < Z X := hX
        have h2 : Z X < 0 := hX'
        linarith
    · exact Set.disjoint_left.2 fun X hX hX' => by
        have h3 : Z X = 0 := hX'
        rcases hX with h | h
        · have h4 : 0 < Z X := h
          linarith
        · have h4 : Z X < 0 := h
          linarith
  rw [hnull, add_zero, ← h1] at h2
  have h3 : P {X | 0 < Z X} = 1 / 2 := by
    have : (2 : ENNReal) * P {X | 0 < Z X} = 1 := by rw [two_mul]; exact h2
    exact (ENNReal.eq_div_iff (by norm_num) (by norm_num)).2 this
  rw [h3]; simp

theorem gibbs_prob {d N : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (c β : ℝ)
    (hβ : 0 ≤ β) : IsProbabilityMeasure (canonicalGibbs (periodicRiesz d s) (fun _ => c) N β) := by
  set g := periodicRiesz d s with hg
  have hint := integrable_exp_canonical (N := N) hd hs0 hsd c β hβ
  have hZ : 0 < canonicalPartition g (fun _ => c) N β := by
    unfold canonicalPartition
    refine (integral_pos_iff_support_of_nonneg (fun _ => (Real.exp_pos _).le) hint).mpr ?_
    have : Function.support (fun X : Config d N =>
        Real.exp (-β * canonicalHamiltonian g (fun _ => c) X)) = Set.univ := by
      ext X; simp [(Real.exp_pos _).ne']
    rw [this]; simp
  refine ⟨?_⟩
  unfold canonicalGibbs
  rw [Measure.smul_apply, withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ,
    smul_eq_mul]
  have := ofReal_integral_eq_lintegral_ofReal hint
    (Filter.Eventually.of_forall fun X => (Real.exp_pos _).le)
  unfold canonicalPartition at hZ ⊢
  rw [← this]
  exact ENNReal.inv_mul_cancel (by simpa using hZ) ENNReal.ofReal_ne_top

theorem gibbs_inv {d N : ℕ} (g : Torus d → ℝ) (c β : ℝ) (t : Torus d) :
    (canonicalGibbs g (fun _ => c) N β).map (shiftEquiv t : Config d N ≃ᵐ Config d N)
      = canonicalGibbs g (fun _ => c) N β := by
  unfold canonicalGibbs
  rw [Measure.map_smul]
  congr 1
  refine map_withDensity_of_measurePreserving (shiftEquiv t) volume (shiftEquiv_measurePreserving t) _ ?_
  intro X
  have := canonicalHamiltonian_shift g c t X
  simp only [this]
  exact (shiftEquiv t).measurable.aemeasurable

theorem gibbs_ac {d N : ℕ} (g V : Torus d → ℝ) (β : ℝ) :
    canonicalGibbs g V N β ≪ (volume : Measure (Config d N)) := by
  unfold canonicalGibbs
  exact (withDensity_absolutelyContinuous _ _).smul_left _

theorem cos_half {d : ℕ} (j : Fin d) (x : Torus d) :
    Torus.cosMode (Pi.single j 1 : HRS.Lattice d)
      (Torus.mk (EuclideanSpace.single j (1/2 : ℝ)) + x) =
    - Torus.cosMode (Pi.single j 1 : HRS.Lattice d) x := by
  conv_lhs => rw [← Torus.mk_rep x, ← Torus.mk_add, Torus.cosMode_mk]
  conv_rhs => rw [← Torus.mk_rep x, Torus.cosMode_mk]
  rw [Torus.dot_add]
  have : Lattice.dot (Pi.single j 1 : HRS.Lattice d) (EuclideanSpace.single j (1/2 : ℝ)) = 1/2 := by
    simp [Lattice.dot, Pi.single_apply]
  rw [this, mul_add, show 2 * Real.pi * (1/2 : ℝ) = Real.pi by ring, add_comm Real.pi,
    Real.cos_add_pi]

theorem pair_cos_zero {d : ℕ} (j : Fin d) :
    ∫ x : Torus d, Torus.cosMode (Pi.single j 1 : HRS.Lattice d) x = 0 := by
  have h1 : ∫ x : Torus d, Torus.cosMode (Pi.single j 1 : HRS.Lattice d)
      (Torus.mk (EuclideanSpace.single j (1/2 : ℝ)) + x) =
      ∫ x : Torus d, Torus.cosMode (Pi.single j 1 : HRS.Lattice d) x :=
    integral_add_left_eq_self (μ := (volume : Measure (Torus d))) _ _
  simp only [cos_half, integral_neg] at h1
  linarith

theorem prob_cos {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 ≤ β)
    (j : Fin d) (n : ℕ) :
    (canonicalGibbs (periodicRiesz d s) (fun _ => (0:ℝ)) (n+1) β
      {X | 0 < Real.sqrt ((n+1 : ℕ) : ℝ) * ((1 / ((n+1 : ℕ) : ℝ)) *
        ∑ i, (fun x => Real.sqrt 2 * Torus.cosMode (Pi.single j 1 : HRS.Lattice d) x) (X i) -
        pair volume (fun x => Real.sqrt 2 * Torus.cosMode (Pi.single j 1 : HRS.Lattice d) x))}).toReal
      = 1 / 2 := by
  haveI := gibbs_prob (N := n+1) hd hs0 hsd 0 β hβ
  set P := canonicalGibbs (periodicRiesz d s) (fun _ => (0:ℝ)) (n+1) β with hP
  have hc : Continuous (Torus.cosMode (Pi.single j 1 : HRS.Lattice d)) :=
    Complex.continuous_re.comp (Torus.continuous_mode _)
  have hp0 : pair volume (fun x => Real.sqrt 2 * Torus.cosMode (Pi.single j 1 : HRS.Lattice d) x) = 0 := by
    unfold pair
    rw [integral_const_mul, pair_cos_zero, mul_zero]
  simp only [hp0, sub_zero]
  have hNpos : (0 : ℝ) < ((n+1 : ℕ) : ℝ) := by positivity
  set Z : Config d (n+1) → ℝ := fun X => Real.sqrt ((n+1 : ℕ) : ℝ) * ((1 / ((n+1 : ℕ) : ℝ)) *
        ∑ i, Real.sqrt 2 * Torus.cosMode (Pi.single j 1 : HRS.Lattice d) (X i)) with hZ
  have hZm : Measurable Z := by
    refine measurable_const.mul (measurable_const.mul (Finset.measurable_sum _ fun i _ => ?_))
    exact measurable_const.mul (hc.measurable.comp (measurable_pi_apply i))
  have hneg : ∀ X, Z (shiftEquiv (Torus.mk (EuclideanSpace.single j (1/2 : ℝ))) X) = -Z X := by
    intro X
    simp only [hZ, shiftEquiv_apply, cos_half, mul_neg, Finset.sum_neg_distrib]
  have hnull : P {X | Z X = 0} = 0 := by
    refine gibbs_ac _ _ _ ?_
    refine measure_mono_null ?_ (null_cos_sum n j)
    intro X hX
    simp only [Set.mem_setOf_eq, hZ] at hX ⊢
    have h1 : Real.sqrt ((n+1 : ℕ) : ℝ) ≠ 0 := (Real.sqrt_pos.2 hNpos).ne'
    have h2 : (1 / ((n+1 : ℕ) : ℝ)) ≠ 0 := by positivity
    rcases mul_eq_zero.1 hX with h | h
    · exact absurd h h1
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h h2
    rw [← Finset.mul_sum] at h
    rcases mul_eq_zero.1 h with h | h
    · exact absurd h (by positivity)
    · exact h
  exact prob_half P _ (gibbs_inv _ _ _ _) Z hZm hneg hnull

theorem isPosHalf_single {d : ℕ} (j : Fin d) : Lattice.IsPosHalf (Pi.single j 1 : HRS.Lattice d) := by
  unfold Lattice.IsPosHalf
  refine ⟨j, fun i hi => ?_, ?_⟩
  · have : i ≠ j := ne_of_lt hi
    show (0 : ℤ) = (Pi.single j 1 : HRS.Lattice d) i
    simp [this]
  · show (0 : ℤ) < (Pi.single j 1 : HRS.Lattice d) j
    simp

theorem integral_sq_cos {d : ℕ} (j : Fin d) :
    ∫ x : Torus d, (Real.sqrt 2 * Torus.cosMode (Pi.single j 1 : HRS.Lattice d) x) ^ 2 = 1 := by
  have hne : (Pi.single j 1 : HRS.Lattice d) ≠ 0 := by
    intro h
    have := congrFun h j
    simp at this
  have := Torus.realMode_orthonormal ⟨_, hne⟩ ⟨_, hne⟩
  simp only [Torus.realMode, if_pos (isPosHalf_single j), if_true] at this
  simpa [sq] using this

theorem mode_neg_arg {d : ℕ} (k : HRS.Lattice d) (u : Torus d) :
    Torus.mode k (-u) = Torus.mode (-k) u := by
  have h1 : Torus.mode k (-u) * Torus.mode k u = 1 := by
    rw [← Torus.mode_add_arg, neg_add_cancel]
    simp [Torus.mode, UnitAddTorus.mFourier]
  have h2 := Torus.mode_neg_lattice k u
  have hne : Torus.mode k u ≠ 0 := by
    intro h; rw [h, mul_zero] at h2; exact zero_ne_one h2
  exact mul_right_cancel₀ hne (h1.trans h2.symm)

theorem conv_mode {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (k : HRS.Lattice d)
    (x : Torus d) :
    ∫ y, ((periodicRiesz d s (x - y) : ℝ) : ℂ) * Torus.mode k y =
      Torus.mode k x * ((rieszCoeff d s k : ℝ) : ℂ) := by
  have : (volume : Measure (Torus d)).IsNegInvariant :=
    MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
  have h1 := integral_sub_left_eq_self (μ := (volume : Measure (Torus d)))
    (fun u => ((periodicRiesz d s u : ℝ) : ℂ) * Torus.mode k (x - u)) x
  simp only [sub_sub_cancel] at h1
  rw [h1]
  have h2 : ∀ u, ((periodicRiesz d s u : ℝ) : ℂ) * Torus.mode k (x - u) =
      Torus.mode k x * (Torus.mode (-k) u * ((periodicRiesz d s u : ℝ) : ℂ)) := by
    intro u
    rw [sub_eq_add_neg, Torus.mode_add_arg, mode_neg_arg]; ring
  simp_rw [h2]
  rw [integral_const_mul, KernelAux.integral_periodicRiesz_mode hd hs0 hsd k]

theorem conv_cos {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (k : HRS.Lattice d)
    (x : Torus d) :
    ∫ y, periodicRiesz d s (x - y) * Torus.cosMode k y =
      rieszCoeff d s k * Torus.cosMode k x := by
  have hg : Integrable (periodicRiesz d s) := (integral_periodicRiesz hd hs0 hsd).1
  have : (volume : Measure (Torus d)).IsNegInvariant :=
    MeasureTheory.Measure.pi.isNegInvariant (fun _ : Fin d => (volume : Measure UnitAddCircle))
  have hi : Integrable (fun y => ((periodicRiesz d s (x - y) : ℝ) : ℂ) * Torus.mode k y) := by
    have h1 : Integrable (fun y => ((periodicRiesz d s (x - y) : ℝ) : ℂ)) :=
      (hg.comp_sub_left x).ofReal
    refine h1.mul_bdd (c := 1) (Torus.continuous_mode k).aestronglyMeasurable ?_
    exact Filter.Eventually.of_forall fun y => by simp [Torus.mode, UnitAddTorus.mFourier]
  have := congrArg Complex.re (conv_mode hd hs0 hsd k x)
  have h3 := integral_re hi
  simp only [RCLike.re_to_complex] at h3
  rw [← h3] at this
  simp only [Torus.cosMode]
  simpa [Complex.mul_re, mul_comm] using this

theorem susc_cos {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (β : ℝ) (hβ : 0 < β)
    (j : Fin d) :
    susceptibilityCov (periodicRiesz d s) volume β
      (fun x => Real.sqrt 2 * Torus.cosMode (Pi.single j 1 : HRS.Lattice d) x)
      (fun x => Real.sqrt 2 * Torus.cosMode (Pi.single j 1 : HRS.Lattice d) x) =
    1 / (1 + β * rieszCoeff d s (Pi.single j 1 : HRS.Lattice d)) := by
  set e : HRS.Lattice d := Pi.single j 1 with he
  set g := periodicRiesz d s with hgdef
  set ψ : Torus d → ℝ := fun x => Real.sqrt 2 * Torus.cosMode e x with hψdef
  set lam := rieszCoeff d s e with hlam
  have hlam0 : 0 ≤ lam := by
    have hne : e ≠ 0 := by
      intro h; have := congrFun h j; simp [he] at this
    exact (rieszCoeff_pos hd hs0 hsd e hne).le
  have hc : Continuous (Torus.cosMode e) := Complex.continuous_re.comp (Torus.continuous_mode _)
  have hψc : Continuous ψ := continuous_const.mul hc
  have hψb : ∀ x, |ψ x| ≤ Real.sqrt 2 := fun x => by
    rw [hψdef]; simp only
    rw [abs_mul, abs_of_nonneg (Real.sqrt_nonneg _)]
    exact mul_le_of_le_one_right (Real.sqrt_nonneg _) (abs_cosMode_le e x)
  have hψm : MemLp ψ 2 (volume : Measure (Torus d)) :=
    MemLp.of_bound hψc.aestronglyMeasurable (Real.sqrt 2) (Filter.Eventually.of_forall fun x => by
      simpa using hψb x)
  have hpair : pair volume ψ = 0 := by
    unfold pair; rw [hψdef]; simp only; rw [integral_const_mul, pair_cos_zero, mul_zero]
  have hKψ : ∀ x, ∫ y, g (x - y) * ψ y = lam * ψ x := by
    intro x
    have : (fun y => g (x - y) * ψ y) = fun y => Real.sqrt 2 * (g (x - y) * Torus.cosMode e y) := by
      funext y; simp only [hψdef]; ring
    rw [this, integral_const_mul, conv_cos hd hs0 hsd e x]
    simp only [hψdef]; ring
  have ha : 0 < 1 + β * lam := by positivity
  set a : ℝ := 1 / (1 + β * lam) with hadef
  have ha1 : a * (1 + β * lam) = 1 := by rw [hadef]; field_simp
  set h : Torus d → ℝ := fun x => a * ψ x with hh
  have hhc : Continuous h := continuous_const.mul hψc
  have e1 : ∀ x, ∫ y, g (x - y) * h y = a * lam * ψ x := by
    intro x
    have : (fun y => g (x - y) * h y) = fun y => a * (g (x - y) * ψ y) := by
      funext y; simp only [hh]; ring
    rw [this, integral_const_mul, hKψ x]; ring
  have hKh : ∀ x, Kop g volume h x = a * lam * ψ x := by
    intro x
    unfold Kop projMean
    have e2 : pair volume (fun x => ∫ y, g (x - y) * h y ∂volume) = 0 := by
      have : (fun x => ∫ y, g (x - y) * h y ∂volume) = fun x => a * lam * ψ x := funext e1
      rw [this]; unfold pair; rw [integral_const_mul]
      have : ∫ x, ψ x = 0 := hpair
      rw [this, mul_zero]
    show (∫ y, g (x - y) * h y ∂volume) - pair volume (fun x => ∫ y, g (x - y) * h y ∂volume) = _
    rw [e2, sub_zero]; exact e1 x
  have hresp : IsResponse g volume β ψ h := by
    refine ⟨?_, ?_, Filter.Eventually.of_forall fun x => ?_⟩
    · exact MemLp.of_bound hhc.aestronglyMeasurable (a * Real.sqrt 2) (Filter.Eventually.of_forall fun x => by
        simp only [hh, Real.norm_eq_abs, abs_mul, abs_of_pos (show 0 < a by positivity)]
        exact mul_le_mul_of_nonneg_left (hψb x) (by positivity))
    · unfold pair; simp only [hh]; rw [integral_const_mul]
      have : ∫ x, ψ x = 0 := hpair
      rw [this, mul_zero]
    · rw [hKh x]; simp only [hh, projMean, hpair]
      have : a * ψ x + β * (a * lam * ψ x) = (a * (1 + β * lam)) * ψ x := by ring
      rw [this, ha1]; ring
  have hvol : withDensityReal (fun _ : Torus d => (1:ℝ)) = volume := by
    unfold withDensityReal; simp
  have hprob : IsProbDensity (fun _ : Torus d => (1:ℝ)) :=
    ⟨fun _ => zero_le_one, measurable_const, by simp⟩
  obtain ⟨h0, hh0, huniq⟩ := exists_unique_response_one_le (by omega : 1 ≤ d) hs0 hsd
    (fun _ => 1) hprob 1 (fun _ => le_rfl) β hβ.le ψ (by rw [hvol]; exact hψm)
  rw [hvol] at hh0 huniq
  have hex : ∃ h', IsResponse g volume β ψ h' := ⟨h, hresp⟩
  have hch : IsResponse g volume β ψ (responseInverse g volume β ψ) := by
    unfold responseInverse; rw [dif_pos hex]; exact hex.choose_spec
  have hae : responseInverse g volume β ψ =ᵐ[volume] h :=
    (huniq _ hch).trans (huniq _ hresp).symm
  unfold susceptibilityCov l2Inner
  have : ∀ᵐ x ∂(volume : Measure (Torus d)), projMean volume ψ x * responseInverse g volume β ψ x
      = a * (ψ x) ^ 2 := by
    filter_upwards [hae] with x hx
    rw [hx]; simp only [projMean, hpair, hh]; ring
  rw [integral_congr_ae this, integral_const_mul]
  have h2 : ∫ x, (ψ x) ^ 2 = 1 := integral_sq_cos j
  rw [h2, hadef]; ring

theorem rieszCoeff_single {d : ℕ} (s : ℝ) (j : Fin d) :
    rieszCoeff d s (Pi.single j 1 : HRS.Lattice d) = rieszConst d s * (2 * Real.pi) ^ (s - d) := by
  have hne : (Pi.single j 1 : HRS.Lattice d) ≠ 0 := by
    intro h; have := congrFun h j; simp at this
  have hn : Lattice.enorm (Pi.single j 1 : HRS.Lattice d) = 1 := by
    unfold Lattice.enorm Lattice.toEuc
    rw [EuclideanSpace.norm_eq]
    simp [Pi.single_apply, Finset.sum_ite_eq]
  simp only [rieszCoeff, if_neg hne, hn, mul_one]

end HRS.StaticLimitsAux
