import HRS.PDE.MeanFieldThermalExist

/-!
# Existence for the Fejér-truncated thermal equation (package MF-01, packet P2b1)

`truncKernel d s N = F_N ⋆ g` is a finite trigonometric sum with positive coefficients.  The
truncated thermal equation `ρ = exp(-β(V + truncKernel ⋆ ρ)) / Z` is solved by minimising the
finite-dimensional convex functional
`J(a) = ½ ∑ a_i²/λ_i + β⁻¹ log ∫ exp(-β(V + ∑ a_i φ_i))`
(Plan §3.1): the abstract part (`exists_dual_critical`) works for any finite family of continuous
mean-zero functions `φ_i` and positive weights `λ_i`; the torus part identifies
`truncKernel(x - y) = ∑_i λ_i φ_i(x) φ_i(y)` with `φ = cos, sin` modes.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.MFThermalExist

variable {d : ℕ}

/-! ### Abstract finite-dimensional dual problem -/

section Dual

variable {ι : Type*} [Fintype ι]

/-- The trigonometric (finite) combination `∑_j a_j φ_j`. -/
def uSum (φ : ι → Torus d → ℝ) (a : ι → ℝ) (x : Torus d) : ℝ := ∑ j, a j * φ j x

theorem continuous_uSum {φ : ι → Torus d → ℝ} (hφ : ∀ i, Continuous (φ i)) (a : ι → ℝ) :
    Continuous (uSum φ a) := by
  unfold uSum
  exact continuous_finsetSum _ fun j _ => continuous_const.mul (hφ j)

theorem uSum_add (φ : ι → Torus d → ℝ) (a b : ι → ℝ) (x : Torus d) :
    uSum φ (a + b) x = uSum φ a x + uSum φ b x := by
  simp [uSum, add_mul, Finset.sum_add_distrib]

theorem uSum_single (φ : ι → Torus d → ℝ) [DecidableEq ι] (i : ι) (t : ℝ) (x : Torus d) :
    uSum φ (t • Pi.single i 1) x = t * φ i x := by
  simp [uSum, Pi.single_apply]

/-- The partition function `Z(a) = ∫ exp(-β(V + ∑ a_j φ_j))`. -/
def partFn (φ : ι → Torus d → ℝ) (V : Torus d → ℝ) (β : ℝ) (a : ι → ℝ) : ℝ :=
  ∫ x, Real.exp (-β * (V x + uSum φ a x))

variable {φ : ι → Torus d → ℝ} {V : Torus d → ℝ} {β : ℝ}

theorem integrable_of_cont {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  integrable_of_continuous' hf

theorem partFn_pos (hφ : ∀ i, Continuous (φ i)) (hV : Continuous V) (a : ι → ℝ) :
    0 < partFn φ V β a := by
  have hc : Continuous fun x => Real.exp (-β * (V x + uSum φ a x)) := by
    have := continuous_uSum hφ a
    fun_prop
  obtain ⟨x0, -, hx0⟩ := isCompact_univ.exists_isMinOn (Set.univ_nonempty (α := Torus d))
    hc.continuousOn
  unfold partFn
  have h1 : ∫ _x : Torus d, Real.exp (-β * (V x0 + uSum φ a x0)) ≤
      ∫ x, Real.exp (-β * (V x + uSum φ a x)) :=
    integral_mono (integrable_const _) (integrable_of_cont hc)
      (fun x => hx0 (Set.mem_univ x))
  simp only [integral_const, probReal_univ, one_smul] at h1
  exact lt_of_lt_of_le (Real.exp_pos _) h1

theorem continuous_partFn (hφ : ∀ i, Continuous (φ i)) (hV : Continuous V) :
    Continuous (partFn φ V β) := by
  have h := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Torus d)))
    (f := fun (a : ι → ℝ) (x : Torus d) => Real.exp (-β * (V x + uSum φ a x)))
    (by
      have : Continuous fun p : (ι → ℝ) × Torus d =>
          Real.exp (-β * (V p.2 + ∑ j, p.1 j * φ j p.2)) := by
        have hh : ∀ j, Continuous fun p : (ι → ℝ) × Torus d => p.1 j * φ j p.2 := fun j =>
          ((continuous_apply j).comp continuous_fst).mul ((hφ j).comp continuous_snd)
        have := continuous_finsetSum Finset.univ (fun j _ => hh j)
        fun_prop
      exact this) (s := Set.univ) isCompact_univ
  have e : partFn φ V β = fun a => ∫ x in Set.univ, Real.exp (-β * (V x + uSum φ a x)) := by
    funext a; simp [partFn, Measure.restrict_univ]
  rw [e]; exact h

theorem integral_uSum (hφ : ∀ i, Continuous (φ i)) (hφ0 : ∀ i, ∫ x, φ i x = 0) (a : ι → ℝ) :
    ∫ x, uSum φ a x = 0 := by
  unfold uSum
  have hI : ∀ j ∈ (Finset.univ : Finset ι), Integrable fun x => a j * φ j x := fun j _ =>
    integrable_of_cont (continuous_const.mul (hφ j))
  rw [integral_finsetSum _ hI]
  refine Finset.sum_eq_zero fun j _ => ?_
  rw [integral_const_mul, hφ0 j, mul_zero]

/-- Jensen lower bound for the log-partition function: `log Z(a) ≥ -β ∫ V`. -/
theorem log_partFn_ge (hφ : ∀ i, Continuous (φ i)) (hφ0 : ∀ i, ∫ x, φ i x = 0)
    (hV : Continuous V) (a : ι → ℝ) :
    -β * ∫ x, V x ≤ Real.log (partFn φ V β a) := by
  have hu := continuous_uSum hφ a
  set f : Torus d → ℝ := fun x => -β * (V x + uSum φ a x) with hf
  have hfc : Continuous f := by rw [hf]; fun_prop
  have hm : ∫ x, f x = -β * ∫ x, V x := by
    rw [hf]
    simp only
    rw [integral_const_mul, integral_add (integrable_of_cont hV) (integrable_of_cont hu),
      integral_uSum hφ hφ0, add_zero]
  have hpt : ∀ x, Real.exp (-β * ∫ y, V y) * (f x - (-β * ∫ y, V y) + 1) ≤ Real.exp (f x) := by
    intro x
    have h1 := Real.add_one_le_exp (f x - (-β * ∫ y, V y))
    have h2 : Real.exp (f x) = Real.exp (-β * ∫ y, V y) * Real.exp (f x - (-β * ∫ y, V y)) := by
      rw [← Real.exp_add]; congr 1; ring
    rw [h2]
    exact mul_le_mul_of_nonneg_left h1 (Real.exp_pos _).le
  have hint : Integrable fun x => Real.exp (-β * ∫ y, V y) * (f x - (-β * ∫ y, V y) + 1) :=
    integrable_of_cont (by fun_prop)
  have h3 := integral_mono hint (integrable_of_cont (hfc.rexp)) hpt
  have hI1 : ∫ x, (f x - (-β * ∫ y, V y) + 1) = 1 := by
    have i1 : Integrable fun x => f x - (-β * ∫ y, V y) :=
      (integrable_of_cont hfc).sub (integrable_const _)
    rw [integral_add i1 (integrable_const _), integral_sub (integrable_of_cont hfc) (integrable_const _), hm]
    simp
  rw [integral_const_mul, hI1, mul_one] at h3
  have h4 : Real.exp (-β * ∫ y, V y) ≤ partFn φ V β a := by
    simpa [partFn, hf] using h3
  exact (Real.le_log_iff_exp_le (partFn_pos hφ hV a)).2 h4

/-- The dual functional `J(a) = ½ ∑ a_j²/λ_j + β⁻¹ log Z(a)`. -/
def Jfun (φ : ι → Torus d → ℝ) (V : Torus d → ℝ) (β : ℝ) (lam : ι → ℝ) (a : ι → ℝ) : ℝ :=
  (1 / 2) * ∑ j, a j ^ 2 / lam j + β⁻¹ * Real.log (partFn φ V β a)

theorem norm_sq_le_sum_sq (a : ι → ℝ) : ‖a‖ ^ 2 ≤ ∑ j, a j ^ 2 := by
  have h : ‖a‖ ≤ Real.sqrt (∑ j, a j ^ 2) :=
    (pi_norm_le_iff_of_nonneg (Real.sqrt_nonneg _)).2 fun j => by
      rw [Real.norm_eq_abs]
      exact Real.abs_le_sqrt (Finset.single_le_sum (f := fun j => a j ^ 2)
        (fun i _ => sq_nonneg _) (Finset.mem_univ j))
  calc ‖a‖ ^ 2 ≤ Real.sqrt (∑ j, a j ^ 2) ^ 2 := pow_le_pow_left₀ (norm_nonneg _) h 2
    _ = ∑ j, a j ^ 2 := Real.sq_sqrt (Finset.sum_nonneg fun i _ => sq_nonneg _)

theorem continuous_Jfun {lam : ι → ℝ} (hφ : ∀ i, Continuous (φ i))
    (hV : Continuous V) : Continuous (Jfun φ V β lam) := by
  unfold Jfun
  refine Continuous.add ?_ (continuous_const.mul ?_)
  · refine continuous_const.mul (continuous_finsetSum _ fun j _ => ?_)
    exact ((continuous_apply j).pow 2).div_const _
  · exact (continuous_partFn hφ hV).log fun a => (partFn_pos hφ hV a).ne'

theorem exists_min_Jfun {lam : ι → ℝ} (hlam : ∀ i, 0 < lam i) (hφ : ∀ i, Continuous (φ i))
    (hφ0 : ∀ i, ∫ x, φ i x = 0) (hV : Continuous V) (hβ : 0 < β) :
    ∃ a : ι → ℝ, ∀ b, Jfun φ V β lam a ≤ Jfun φ V β lam b := by
  refine (continuous_Jfun hφ hV).exists_forall_le ?_
  set L : ℝ := ∑ j, lam j + 1 with hL
  have hLpos : 0 < L := by
    have : 0 ≤ ∑ j, lam j := Finset.sum_nonneg fun j _ => (hlam j).le
    linarith
  have hlamL : ∀ j, lam j ≤ L := fun j => by
    have := Finset.single_le_sum (f := lam) (fun i _ => (hlam i).le) (Finset.mem_univ j)
    linarith
  have hlow : ∀ a : ι → ℝ, (1 / 2) * (‖a‖ ^ 2 / L) + -∫ x, V x ≤ Jfun φ V β lam a := by
    intro a
    have h1 : ‖a‖ ^ 2 / L ≤ ∑ j, a j ^ 2 / lam j := by
      calc ‖a‖ ^ 2 / L ≤ (∑ j, a j ^ 2) / L := div_le_div_of_nonneg_right (norm_sq_le_sum_sq a) hLpos.le
        _ = ∑ j, a j ^ 2 / L := by rw [Finset.sum_div]
        _ ≤ ∑ j, a j ^ 2 / lam j := Finset.sum_le_sum fun j _ =>
            div_le_div_of_nonneg_left (sq_nonneg _) (hlam j) (hlamL j)
    have h2 := log_partFn_ge (β := β) hφ hφ0 hV a
    have h3 : -∫ x, V x ≤ β⁻¹ * Real.log (partFn φ V β a) := by
      have := mul_le_mul_of_nonneg_left h2 (inv_nonneg.2 hβ.le)
      have e : β⁻¹ * (-β * ∫ x, V x) = -∫ x, V x := by field_simp
      linarith
    unfold Jfun
    nlinarith
  have h1 : Tendsto (fun a : ι → ℝ => ‖a‖) (cocompact _) atTop := tendsto_norm_cocompact_atTop
  have h2 : Tendsto (fun r : ℝ => (1 / 2) * (r ^ 2 / L) + -∫ x, V x) atTop atTop := by
    refine tendsto_atTop_add_const_right _ _ ?_
    exact Tendsto.const_mul_atTop (by norm_num)
      (Tendsto.atTop_div_const hLpos (tendsto_pow_atTop two_ne_zero))
  exact tendsto_atTop_mono hlow (h2.comp h1)

theorem hasDerivAt_partFn_dir [DecidableEq ι] (hφ : ∀ i, Continuous (φ i)) (hV : Continuous V)
    (a : ι → ℝ) (i : ι) :
    HasDerivAt (fun t : ℝ => partFn φ V β (a + t • Pi.single i 1))
      (∫ x, Real.exp (-β * (V x + uSum φ a x)) * (-β * φ i x)) 0 := by
  have hu := continuous_uSum hφ a
  set c : Torus d → ℝ := fun x => V x + uSum φ a x with hc
  have hcc : Continuous c := hV.add hu
  obtain ⟨Bc, hBc⟩ := isCompact_univ.exists_bound_of_continuousOn hcc.continuousOn
  obtain ⟨Bp, hBp⟩ := isCompact_univ.exists_bound_of_continuousOn (hφ i).continuousOn
  have e : (fun t : ℝ => partFn φ V β (a + t • Pi.single i 1)) =
      fun t => ∫ x, Real.exp (-β * (c x + t * φ i x)) := by
    funext t
    unfold partFn
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only [uSum_add, uSum_single, hc]
    ring_nf
  rw [e]
  have hF : ∀ t : ℝ, Continuous fun x => Real.exp (-β * (c x + t * φ i x)) := fun t => by
    have := hcc; have := hφ i; fun_prop
  have key := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := (volume : Measure (Torus d)))
    (F := fun (t : ℝ) (x : Torus d) => Real.exp (-β * (c x + t * φ i x)))
    (F' := fun (t : ℝ) (x : Torus d) => Real.exp (-β * (c x + t * φ i x)) * (-β * φ i x))
    (x₀ := 0) (s := Metric.ball (0:ℝ) 1) (bound := fun _ => Real.exp (|β| * (|Bc| + |Bp|)) * (|β| * |Bp|))
    (Metric.ball_mem_nhds _ one_pos) (Filter.Eventually.of_forall fun t => (hF t).aestronglyMeasurable)
    (integrable_of_cont (hF 0))
    (by have := hF 0; have := hφ i; exact ((hF 0).mul (continuous_const.mul (hφ i))).aestronglyMeasurable)
    (Filter.Eventually.of_forall fun x t ht => by
      have ht' : |t| < 1 := by simpa [Metric.mem_ball, Real.dist_eq] using ht
      have h1 : |c x| ≤ |Bc| := by
        have := hBc x (Set.mem_univ x)
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_abs_self _)
      have h2 : |φ i x| ≤ |Bp| := by
        have := hBp x (Set.mem_univ x)
        rw [Real.norm_eq_abs] at this
        exact this.trans (le_abs_self _)
      have h3 : |-β * (c x + t * φ i x)| ≤ |β| * (|Bc| + |Bp|) := by
        rw [abs_mul, abs_neg]
        refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
        calc |c x + t * φ i x| ≤ |c x| + |t * φ i x| := abs_add_le _ _
          _ ≤ |Bc| + |Bp| := by
            rw [abs_mul]
            have : |t| * |φ i x| ≤ 1 * |Bp| :=
              mul_le_mul ht'.le h2 (abs_nonneg _) zero_le_one
            linarith
      rw [Real.norm_eq_abs, abs_mul, abs_of_pos (Real.exp_pos _), abs_mul, abs_neg]
      refine mul_le_mul (Real.exp_le_exp.2 ((le_abs_self _).trans h3))
        (mul_le_mul_of_nonneg_left h2 (abs_nonneg _)) (by positivity) (Real.exp_pos _).le)
    (integrable_const _)
    (Filter.Eventually.of_forall fun x t _ => by
      have h1 : HasDerivAt (fun t : ℝ => -β * (c x + t * φ i x)) (-β * (1 * φ i x)) t := by
        have := ((hasDerivAt_id t).mul_const (φ i x)).const_add (c x)
        simpa using this.const_mul (-β)
      simpa [mul_one, one_mul] using h1.exp)
  simpa using key.2

theorem hasDerivAt_quad [DecidableEq ι] {lam : ι → ℝ} (a : ι → ℝ) (i : ι) :
    HasDerivAt (fun t : ℝ => (1 / 2) * ∑ j, (a + t • (Pi.single i (1 : ℝ) : ι → ℝ)) j ^ 2 / lam j)
      (a i / lam i) 0 := by
  have h : ∀ j ∈ (Finset.univ : Finset ι),
      HasDerivAt (fun t : ℝ => (a + t • (Pi.single i (1 : ℝ) : ι → ℝ)) j ^ 2 / lam j)
        (2 * a j * ((Pi.single i (1 : ℝ) : ι → ℝ) j) / lam j) 0 := by
    intro j _
    have h1 : HasDerivAt (fun t : ℝ => a j + t * (Pi.single i (1 : ℝ) : ι → ℝ) j) ((Pi.single i (1 : ℝ) : ι → ℝ) j) 0 := by
      simpa using ((hasDerivAt_id (0 : ℝ)).mul_const ((Pi.single i (1 : ℝ) : ι → ℝ) j)).const_add (a j)
    have h2 := (h1.pow 2).div_const (lam j)
    simp only [Pi.add_apply, Pi.smul_apply, smul_eq_mul]
    convert h2 using 1
    simp
  have := (HasDerivAt.fun_sum h).const_mul (1 / 2 : ℝ)
  convert this using 1
  simp [Pi.single_apply, ite_div, Finset.sum_ite_eq']
  ring

/-- Euler–Lagrange equations of the dual problem:
`a_i = λ_i ⟨φ_i, ρ⟩` with `ρ = exp(-β(V + ∑ a_j φ_j)) / Z`. -/
theorem exists_dual_critical {lam : ι → ℝ} (hlam : ∀ i, 0 < lam i) (hφ : ∀ i, Continuous (φ i))
    (hφ0 : ∀ i, ∫ x, φ i x = 0) (hV : Continuous V) (hβ : 0 < β) :
    ∃ a : ι → ℝ, ∀ i, a i = lam i *
      ∫ x, φ i x * (Real.exp (-β * (V x + uSum φ a x)) / partFn φ V β a) := by
  classical
  obtain ⟨a, ha⟩ := exists_min_Jfun hlam hφ hφ0 hV hβ
  refine ⟨a, fun i => ?_⟩
  have hZ : 0 < partFn φ V β a := partFn_pos hφ hV a
  have hd1 := hasDerivAt_quad (lam := lam) a i
  have hd2 := hasDerivAt_partFn_dir (β := β) hφ hV a i
  have hd3 := hd2.log (by simpa using hZ.ne')
  have hder := hd1.add (hd3.const_mul β⁻¹)
  have hmin : IsLocalMin (fun t : ℝ => Jfun φ V β lam (a + t • Pi.single i 1)) 0 :=
    Filter.Eventually.of_forall fun t => by simpa using ha (a + t • Pi.single i 1)
  have h0 := hmin.hasDerivAt_eq_zero hder
  simp only [zero_smul, add_zero] at h0
  have hD : ∫ x, Real.exp (-β * (V x + uSum φ a x)) * (-β * φ i x) =
      -β * ∫ x, φ i x * Real.exp (-β * (V x + uSum φ a x)) := by
    rw [← integral_const_mul]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  have hR : ∫ x, φ i x * (Real.exp (-β * (V x + uSum φ a x)) / partFn φ V β a) =
      (∫ x, φ i x * Real.exp (-β * (V x + uSum φ a x))) / partFn φ V β a := by
    rw [← integral_div]
    refine integral_congr_ae (Filter.Eventually.of_forall fun x => ?_)
    simp only; ring
  rw [hR]
  rw [hD] at h0
  have hl := (hlam i).ne'
  have hb := hβ.ne'
  field_simp at h0 ⊢
  linarith

end Dual

/-! ### The Fejér-smoothed kernel -/

section Trunc

variable {s : ℝ}

-- `truncKernel` and `convFun_comm` are in `HRS/PDE/MeanFieldThermalExist.lean`.

theorem truncKernel_eq (d : ℕ) (s : ℝ) (N : ℕ) :
    truncKernel d s N = convFun (periodicRiesz d s) (fejer N) :=
  funext fun x => convFun_comm _ _ x

theorem continuous_truncKernel (F : MFInputs.MFKernelFacts d s) (N : ℕ) :
    Continuous (truncKernel d s N) := by
  rw [truncKernel_eq]
  exact MFAux.continuous_convFun F.integrable (fejer_continuous N)

/-- `F_N ⋆ g ≥ -B` when `g ≥ -B`. -/
theorem truncKernel_ge (F : MFInputs.MFKernelFacts d s) {N : ℕ} (hN : 0 < N) {B : ℝ}
    (hB : ∀ x, -B ≤ periodicRiesz d s x) (x : Torus d) : -B ≤ truncKernel d s N x :=
  convFun_fejer_ge hN F.integrable hB x

theorem exists_truncKernel_ge (F : MFInputs.MFKernelFacts d s) :
    ∃ B : ℝ, ∀ N' : ℕ, 0 < N' → ∀ x, -B ≤ truncKernel d s N' x := by
  obtain ⟨B, hB⟩ := F.bddBelow
  exact ⟨B, fun N' hN' x => truncKernel_ge F hN' hB x⟩

/-- The coefficient `ĝ(k) w_N(k)` of `F_N ⋆ g`. -/
def truncCoeff (d : ℕ) (s : ℝ) (N : ℕ) (k : Lattice d) : ℝ :=
  rieszCoeff d s k * ∏ i : Fin d, max (1 - |(k i : ℝ)| / N) 0

theorem coeffOf_truncKernel (F : MFInputs.MFKernelFacts d s) {N : ℕ} (hN : 0 < N)
    (k : Lattice d) : coeffOf (truncKernel d s N) k = (truncCoeff d s N k : ℂ) := by
  rw [truncKernel_eq]
  have := MFAux.funFourierCoeff_convFun F.integrable (fejer_continuous (d := d) N) k
  unfold coeffOf
  rw [this, F.fourierCoeff k]
  have h2 := coeffOf_fejer (d := d) N hN k
  unfold coeffOf at h2
  rw [h2]
  unfold truncCoeff
  push_cast
  rfl

theorem integral_truncKernel (F : MFInputs.MFKernelFacts d s) {N : ℕ} (hN : 0 < N) :
    ∫ x, truncKernel d s N x = 0 := by
  have h := coeffOf_truncKernel F hN 0
  unfold coeffOf at h
  rw [funFourierCoeff_eq_int] at h
  have h0 : truncCoeff d s N 0 = 0 := by simp [truncCoeff, rieszCoeff]
  simp only [h0, neg_zero, UnitAddTorus.mFourier_zero, ContinuousMap.one_apply, one_mul, Complex.ofReal_zero] at h
  rw [integral_complex_ofReal] at h
  exact_mod_cast h

/-- The finite index set `I_N = {k ≠ 0 : |k_i| < N}`. -/
def boxIdx (d N : ℕ) : Finset (Lattice d) :=
  (Fintype.piFinset fun _ : Fin d => Finset.Ioo (-(N : ℤ)) N).filter (· ≠ 0)

theorem mem_boxIdx {N : ℕ} {k : Lattice d} : k ∈ boxIdx d N ↔ k ≠ 0 ∧ ∀ i, |k i| < N := by
  unfold boxIdx
  simp only [Finset.mem_filter, Fintype.mem_piFinset, Finset.mem_Ioo, abs_lt]
  constructor
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩
  · rintro ⟨h1, h2⟩; exact ⟨h2, h1⟩

theorem neg_mem_boxIdx {N : ℕ} {k : Lattice d} : -k ∈ boxIdx d N ↔ k ∈ boxIdx d N := by
  simp [mem_boxIdx]

theorem truncCoeff_neg (N : ℕ) (k : Lattice d) : truncCoeff d s N (-k) = truncCoeff d s N k := by
  simp [truncCoeff, rieszCoeff_neg]

theorem truncCoeff_eq_zero {N : ℕ} (hN0 : 0 < N) {k : Lattice d} (hk : k ∉ boxIdx d N) :
    truncCoeff d s N k = 0 := by
  by_cases h0 : k = 0
  · simp [truncCoeff, rieszCoeff, h0]
  · have : ∃ i, N ≤ |k i| := by
      by_contra h
      push Not at h
      exact hk (mem_boxIdx.2 ⟨h0, h⟩)
    obtain ⟨i, hi⟩ := this
    unfold truncCoeff
    rw [Finset.prod_eq_zero (Finset.mem_univ i), mul_zero]
    have hN : (0 : ℝ) < N := by exact_mod_cast hN0
    have : (N : ℝ) ≤ |(k i : ℝ)| := by
      rw [← Int.cast_abs]; exact_mod_cast hi
    have : 1 - |(k i : ℝ)| / N ≤ 0 := by
      rw [sub_nonpos, le_div_iff₀ hN]; linarith
    exact max_eq_right this

theorem truncCoeff_pos (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) {N : ℕ} {k : Lattice d}
    (hk : k ∈ boxIdx d N) : 0 < truncCoeff d s N k := by
  obtain ⟨hk0, hkN⟩ := mem_boxIdx.1 hk
  unfold truncCoeff
  refine mul_pos (rieszCoeff_pos' hd hs0 hsd k hk0) (Finset.prod_pos fun i _ => ?_)
  have hN : (0 : ℝ) < N := by
    have := hkN i
    have h0 : (0 : ℤ) < N := lt_of_le_of_lt (abs_nonneg _) this
    exact_mod_cast h0
  have : |(k i : ℝ)| < N := by
    rw [← Int.cast_abs]; exact_mod_cast hkN i
  have : 0 < 1 - |(k i : ℝ)| / N := by
    rw [sub_pos, div_lt_one hN]; exact this
  exact lt_max_of_lt_left this

theorem coeffOf_cosMode_smul (c : ℝ) (k k' : Lattice d) :
    coeffOf (fun z => c * Torus.cosMode k z) k' =
      (c : ℂ) * ((if k = k' then 1 else 0) + (if k = -k' then 1 else 0)) / 2 := by
  unfold coeffOf
  rw [funFourierCoeff_eq_int]
  have hcos : ∀ z : Torus d, ((Torus.cosMode k z : ℝ) : ℂ) =
      (Torus.mode k z + Torus.mode (-k) z) / 2 := by
    intro z
    rw [Torus.cosMode, Complex.re_eq_add_conj, Torus.mode_neg]
  have e : ∀ z : Torus d, UnitAddTorus.mFourier (-k') z * ((c * Torus.cosMode k z : ℝ) : ℂ) =
      (c / 2 : ℂ) * (Torus.mode (-k') z * Torus.mode k z + Torus.mode (-k') z * Torus.mode (-k) z) := by
    intro z
    push_cast
    rw [hcos]
    show Torus.mode (-k') z * _ = _
    ring
  simp_rw [e]
  rw [integral_const_mul, integral_add (Torus.integrable_mode_mul _ _) (Torus.integrable_mode_mul _ _),
    Torus.integral_mode_mul, Torus.integral_mode_mul]
  have h1 : (-k' + k = 0) ↔ k = k' := by
    rw [neg_add_eq_zero]; exact eq_comm
  have h2 : (-k' + -k = 0) ↔ k = -k' := by
    constructor
    · intro h; rw [eq_neg_iff_add_eq_zero, add_comm]; rw [← neg_add, neg_eq_zero] at h; exact h
    · intro h; rw [h]; abel
  simp only [h1, h2]
  ring

/-- `F_N ⋆ g` is the finite trigonometric sum `∑_{k ∈ I_N} ĝ(k) w_N(k) cos(2π k·x)`. -/
theorem truncKernel_eq_sum (F : MFInputs.MFKernelFacts d s) {N : ℕ} (hN : 0 < N) :
    truncKernel d s N = fun z => ∑ k ∈ boxIdx d N, truncCoeff d s N k * Torus.cosMode k z := by
  have hcont : Continuous fun z : Torus d =>
      ∑ k ∈ boxIdx d N, truncCoeff d s N k * Torus.cosMode k z :=
    continuous_finsetSum _ fun k _ => continuous_const.mul (Torus.continuous_cosMode k)
  refine MFAux.eq_of_funFourierCoeff_eq (continuous_truncKernel F N) hcont fun k' => ?_
  have h1 := coeffOf_truncKernel F hN k'
  change coeffOf (truncKernel d s N) k' = coeffOf _ k'
  rw [h1, MFAux.coeffOf_sum (boxIdx d N) (fun k z => truncCoeff d s N k * Torus.cosMode k z)
    (fun k => continuous_const.mul (Torus.continuous_cosMode k)) k']
  simp_rw [coeffOf_cosMode_smul]
  have e : ∀ x : Lattice d, (truncCoeff d s N x : ℂ) *
      ((if x = k' then 1 else 0) + (if x = -k' then 1 else 0)) / 2 =
      ((if x = k' then (truncCoeff d s N x : ℂ) else 0) +
        (if x = -k' then (truncCoeff d s N x : ℂ) else 0)) / 2 := by
    intro x; split_ifs <;> ring
  simp_rw [e]
  rw [← Finset.sum_div, Finset.sum_add_distrib, Finset.sum_ite_eq', Finset.sum_ite_eq']
  by_cases hk : k' ∈ boxIdx d N
  · have hk' : -k' ∈ boxIdx d N := neg_mem_boxIdx.2 hk
    simp only [hk, hk', ite_true]
    have := truncCoeff_neg (s := s) N k'
    rw [show (truncCoeff d s N (-k') : ℂ) = truncCoeff d s N k' by exact_mod_cast this]
    ring
  · have hk' : -k' ∉ boxIdx d N := fun h => hk (neg_mem_boxIdx.1 h)
    simp only [hk, hk', ite_false, truncCoeff_eq_zero hN hk]
    simp

theorem cosMode_sub (k : Lattice d) (x y : Torus d) :
    Torus.cosMode k (x - y) = Torus.cosMode k x * Torus.cosMode k y +
      Torus.sinMode k x * Torus.sinMode k y := by
  have h : Torus.mode k (x - y) = Torus.mode k x * conj (Torus.mode k y) := by
    have h1 := Torus.mode_add_arg k (x - y) y
    rw [sub_add_cancel] at h1
    have h2 := Torus.mode_neg_lattice k y
    rw [Torus.mode_neg] at h2
    calc Torus.mode k (x - y) = Torus.mode k (x - y) * (conj (Torus.mode k y) * Torus.mode k y) := by
          rw [h2, mul_one]
      _ = (Torus.mode k (x - y) * Torus.mode k y) * conj (Torus.mode k y) := by ring
      _ = _ := by rw [← h1]
  unfold Torus.cosMode
  rw [h]
  simp [Complex.mul_re, Torus.sinMode]

theorem integral_cosMode {k : Lattice d} (hk : k ≠ 0) : ∫ x, Torus.cosMode k x = 0 := by
  have h := Torus.integral_mode k
  simp only [hk, ite_false] at h
  have := integral_re (Torus.integrable_mode k)
  unfold Torus.cosMode
  rw [h] at this
  simpa using this

theorem integral_sinMode {k : Lattice d} (hk : k ≠ 0) : ∫ x, Torus.sinMode k x = 0 := by
  have h := Torus.integral_mode k
  simp only [hk, ite_false] at h
  have := integral_im (Torus.integrable_mode k)
  unfold Torus.sinMode
  rw [h] at this
  simpa using this

/-- The pair form `F_N ⋆ g (x - y) = ∑_{k ∈ I_N} ĝ(k) w_N(k) (cos_k(x) cos_k(y) + sin_k(x) sin_k(y))`. -/
theorem truncKernel_sub (F : MFInputs.MFKernelFacts d s) {N : ℕ} (hN : 0 < N) (x y : Torus d) :
    truncKernel d s N (x - y) = ∑ k ∈ boxIdx d N, truncCoeff d s N k *
      (Torus.cosMode k x * Torus.cosMode k y + Torus.sinMode k x * Torus.sinMode k y) := by
  rw [truncKernel_eq_sum F hN]
  exact Finset.sum_congr rfl fun k _ => by rw [cosMode_sub]

end Trunc

/-! ### Existence for the truncated thermal equation -/

/-- **Existence for the Fejér-truncated thermal equation** (Plan §3.1): for every `N ≥ 1`
there is a continuous positive probability density `ρ` with
`ρ = exp(-β(V + (F_N ⋆ g) ⋆ ρ)) / Z`. -/
theorem exists_truncated_thermal (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d)
    (F : MFInputs.MFKernelFacts d s) (V : Torus d → ℝ) (hV : Continuous V) (β : ℝ) (hβ : 0 < β)
    (N : ℕ) (hN : 0 < N) :
    ∃ ρ : Torus d → ℝ, Continuous ρ ∧ (∀ x, 0 < ρ x) ∧ ∫ x, ρ x = 1 ∧
      ∀ x, ρ x = Real.exp (-β * (V x + convFun (truncKernel d s N) ρ x)) /
        ∫ y, Real.exp (-β * (V y + convFun (truncKernel d s N) ρ y)) := by
  classical
  set I := boxIdx d N with hI
  let φ : (↥I × Bool) → Torus d → ℝ := fun p x =>
    if p.2 then Torus.cosMode p.1 x else Torus.sinMode p.1 x
  let lam : (↥I × Bool) → ℝ := fun p => truncCoeff d s N p.1
  have hφ : ∀ i, Continuous (φ i) := fun p => by
    by_cases h : p.2
    · simpa [φ, h] using Torus.continuous_cosMode p.1.1
    · simpa [φ, h] using Torus.continuous_sinMode p.1.1
  have hφ0 : ∀ i, ∫ x, φ i x = 0 := fun p => by
    have hk : p.1.1 ≠ 0 := (mem_boxIdx.1 p.1.2).1
    by_cases h : p.2
    · simpa [φ, h] using integral_cosMode hk
    · simpa [φ, h] using integral_sinMode hk
  have hlam : ∀ i, 0 < lam i := fun p => truncCoeff_pos hd hs0 hsd p.1.2
  obtain ⟨a, ha⟩ := exists_dual_critical (β := β) hlam hφ hφ0 hV hβ
  set Z := partFn φ V β a with hZ
  have hZpos : 0 < Z := partFn_pos hφ hV a
  have hu := continuous_uSum hφ a
  set ρ : Torus d → ℝ := fun x => Real.exp (-β * (V x + uSum φ a x)) / Z with hρ
  have hρc : Continuous ρ := by rw [hρ]; have := hu; fun_prop
  have hpair : ∀ x y, truncKernel d s N (x - y) = ∑ i, lam i * φ i x * φ i y := by
    intro x y
    rw [truncKernel_sub F hN, Fintype.sum_prod_type]
    simp only [Fintype.sum_bool, φ, lam, ite_true, Bool.false_eq_true, ite_false]
    rw [← Finset.sum_coe_sort I]
    refine Finset.sum_congr rfl fun k _ => by ring
  have hkey : ∀ x, convFun (truncKernel d s N) ρ x = uSum φ a x := by
    intro x
    unfold convFun
    have e : ∀ y, truncKernel d s N (x - y) * ρ y =
        ∑ i, (lam i * φ i x) * (φ i y * ρ y) := fun y => by
      rw [hpair, Finset.sum_mul]
      exact Finset.sum_congr rfl fun i _ => by ring
    simp_rw [e]
    have hint : ∀ i ∈ (Finset.univ : Finset (↥I × Bool)),
        Integrable fun y => (lam i * φ i x) * (φ i y * ρ y) := fun i _ =>
      integrable_of_cont (continuous_const.mul ((hφ i).mul hρc))
    rw [integral_finsetSum _ hint]
    unfold uSum
    refine Finset.sum_congr rfl fun i _ => ?_
    rw [integral_const_mul, ha i]
    simp only [hρ]
    ring
  refine ⟨ρ, hρc, fun x => div_pos (Real.exp_pos _) hZpos, ?_, ?_⟩
  · simp only [hρ]
    rw [integral_div]
    exact div_self hZpos.ne'
  · intro x
    have hfun : convFun (truncKernel d s N) ρ = uSum φ a := funext hkey
    simp only [hfun]
    rfl

end HRS.PDE.MFThermalExist
