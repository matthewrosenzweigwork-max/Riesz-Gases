import HRS.Dynamics.Setup

/-!
# Gradient of the periodic Riesz kernel: torus geometry and pointwise kernel facts

Auxiliary file of `HRS/Kernel/GradConv.lean`.  It contains verbatim copies of the small torus
definitions of `HRS/PDE/Convention.lean` (`centeredRep`, `tdist`, ...), elementary geometry of
the centered representative, and the pointwise facts about `∇g` (`periodicRieszGrad`):
measurability, oddness, bounds (also uniform for the heat regularisations).
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.KernelGrad

variable {d : ℕ}

/-! ### Verbatim copies of definitions of `HRS/PDE/Convention.lean` and `HRS/PDE/Fourier.lean` -/

/-- The centered representative in `(-1/2, 1/2]^d` of a point of the torus. -/
def centeredRep (z : Torus d) : Euc d :=
  WithLp.toLp 2 fun i => if (Torus.rep z) i ≤ 1 / 2 then (Torus.rep z) i else (Torus.rep z) i - 1

/-- The Euclidean distance `|x - y|` on the torus: the norm of the centered representative of
`x - y` (this is the quotient distance, and `{|x-y| ≤ 1/4}` is the ball used in
`B:eq:nabla-g-convolution`). -/
def tdist (x y : Torus d) : ℝ := ‖centeredRep (x - y)‖

/-- A Lipschitz function on the torus with constant `L`. -/
def IsLipschitz (L : ℝ) (a : Torus d → ℝ) : Prop := ∀ x y, |a x - a y| ≤ L * tdist x y

/-- Smoothness away from the origin (for kernels): `C^∞` on `{z ≠ 0}` through the lift
(`((⊤ : ℕ∞) : WithTop ℕ∞)` is `C^∞`; `⊤ : WithTop ℕ∞` would be analyticity, ISSUES §E). -/
def IsSmoothOffZero {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] (κ : Torus d → E) : Prop :=
  ContDiffOn ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (Torus.lift κ) {x : Euc d | Torus.mk x ≠ 0}

/-- Fourier coefficient sequences `(F̂(k))_{k ∈ ℤ^d}`: the representation of a distribution on
`𝕋^d` used by the PDE layer. -/
abbrev Coeff (d : ℕ) := Lattice d → ℂ

/-- The Fourier coefficients `φ̂(k) = ∫ φ(x) e^{-2πik·x} dx` of a real function (line 10055). -/
def coeffOf (φ : Torus d → ℝ) : Coeff d :=
  fun k => Torus.funFourierCoeff (fun x => (φ x : ℂ)) k

/-- `∂_j` as the multiplier `2πi k_j`. -/
def derivCoeff (j : Fin d) (c : Coeff d) : Coeff d :=
  fun k => (2 * Real.pi * Complex.I * (k j : ℂ)) * c k

/-- `g *` as the multiplier `ĝ(k) = rieszCoeff d s k` (`H:eq:kernel`, lines 421–423;
`ĝ(0) = 0`). -/
def rieszMult (d : ℕ) (s : ℝ) (c : Coeff d) : Coeff d :=
  fun k => ((rieszCoeff d s k : ℝ) : ℂ) * c k

/-- `∂_i g *` as the multiplier `2πi k_i ĝ(k)`: the distributional convolution with the force,
which agrees with the cancellation convention `B:eq:nabla-g-convolution` (lines 10092–10101). -/
def gradRieszCoeff (d : ℕ) (s : ℝ) (i : Fin d) (c : Coeff d) : Coeff d :=
  derivCoeff i (rieszMult d s c)

/-- The box `{k : |k|_∞ ≤ n}`. -/
def InBox (n : ℕ) (k : Lattice d) : Prop := ∀ i, |k i| ≤ (n : ℤ)

/-- `c` is a trigonometric polynomial of degree `≤ n` (supported in the box). -/
def IsTrigPoly (n : ℕ) (c : Coeff d) : Prop := ∀ k, c k ≠ 0 → InBox n k

/-! ### Elementary geometry of the centered representative -/

theorem centeredRep_apply (z : Torus d) (i : Fin d) :
    centeredRep z i = if (Torus.rep z) i ≤ 1 / 2 then (Torus.rep z) i else (Torus.rep z) i - 1 := rfl

theorem rep_mem (z : Torus d) (i : Fin d) : 0 ≤ Torus.rep z i ∧ Torus.rep z i < 1 := by
  have := (AddCircle.equivIco (1 : ℝ) 0 (z i)).2
  simpa [Torus.rep] using this

theorem abs_centeredRep_le (z : Torus d) (i : Fin d) : |centeredRep z i| ≤ 1 / 2 := by
  obtain ⟨h0, h1⟩ := rep_mem z i
  rw [centeredRep_apply]
  split_ifs with h
  · rw [abs_of_nonneg h0]; exact h
  · push Not at h
    rw [abs_of_neg (by linarith)]; linarith

theorem mk_centeredRep (z : Torus d) : Torus.mk (centeredRep z) = z := by
  conv_rhs => rw [← Torus.mk_rep z]
  funext i
  simp only [Torus.mk, centeredRep_apply]
  split_ifs with h
  · rfl
  · rw [AddCircle.coe_sub, show (((1:ℝ)) : UnitAddCircle) = 0 from AddCircle.coe_period (1:ℝ), sub_zero]


theorem norm_apply_eq (z : Torus d) (i : Fin d) : ‖z i‖ = |centeredRep z i| := by
  have h := congrFun (mk_centeredRep z) i
  have hc := abs_centeredRep_le z i
  have : ‖((centeredRep z i : ℝ) : UnitAddCircle)‖ = |centeredRep z i| := by
    rw [AddCircle.norm_coe_eq_abs_iff (1:ℝ) one_ne_zero]
    simpa using hc
  rw [← this]
  rw [← h]
  rfl

theorem norm_le_iff {r : ℝ} (hr : 0 ≤ r) (z : Torus d) : ‖z‖ ≤ r ↔ ∀ i, |centeredRep z i| ≤ r := by
  rw [pi_norm_le_iff_of_nonneg hr]
  simp only [norm_apply_eq]

theorem tdist_zero_right (z : Torus d) : tdist z 0 = ‖centeredRep z‖ := by
  simp [tdist]

theorem norm_le_tdist (z : Torus d) : ‖z‖ ≤ tdist z 0 := by
  rw [tdist_zero_right, norm_le_iff (norm_nonneg _)]
  intro i
  have := PiLp.norm_apply_le (centeredRep z) i
  simpa using this

theorem tdist_nonneg (x y : Torus d) : 0 ≤ tdist x y := norm_nonneg _

theorem abs_apply_eq_of_mk {y : Euc d} (hy : ∀ i, |y i| ≤ 1 / 2) (i : Fin d) :
    |centeredRep (Torus.mk y) i| = |y i| := by
  rw [← norm_apply_eq]
  have : ((y i : ℝ) : UnitAddCircle) = (Torus.mk y) i := rfl
  rw [← this, AddCircle.norm_coe_eq_abs_iff (1:ℝ) one_ne_zero]
  simpa using hy i

theorem tdist_mk {y : Euc d} (hy : ∀ i, |y i| ≤ 1 / 2) : tdist (Torus.mk y) 0 = ‖y‖ := by
  rw [tdist_zero_right, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs, sq_abs, sq_abs]
  have := abs_apply_eq_of_mk hy i
  rw [← sq_abs, this, sq_abs]

theorem tdist_neg (z : Torus d) : tdist (-z) 0 = tdist z 0 := by
  rw [tdist_zero_right, tdist_zero_right, EuclideanSpace.norm_eq, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, Real.norm_eq_abs, ← norm_apply_eq, ← norm_apply_eq]
  simp

theorem tdist_pos {z : Torus d} (hz : z ≠ 0) : 0 < tdist z 0 := by
  rcases (tdist_nonneg z 0).lt_or_eq with h | h
  · exact h
  · exfalso
    apply hz
    rw [tdist_zero_right] at h
    have h0 : centeredRep z = 0 := norm_eq_zero.mp h.symm
    rw [← mk_centeredRep z, h0]
    funext i; simp [Torus.mk]

theorem exists_mk_box (z : Torus d) : ∃ y : Euc d, Torus.mk y = z ∧ ∀ i, |y i| ≤ 1 / 2 :=
  ⟨centeredRep z, mk_centeredRep z, abs_centeredRep_le z⟩


theorem mk_add (x y : Euc d) : Torus.mk (x + y) = Torus.mk x + Torus.mk y := by
  funext i
  simp [Torus.mk]

theorem mk_sub (x y : Euc d) : Torus.mk (x - y) = Torus.mk x - Torus.mk y := by
  funext i
  simp [Torus.mk]

theorem isOpenQuotientMap_mk : IsOpenQuotientMap (Torus.mk : Euc d → Torus d) := by
  have h1 : IsOpenQuotientMap
      (Pi.map (fun _ : Fin d => ((↑) : ℝ → UnitAddCircle))) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  have h2 := h1.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  exact h2

theorem continuous_of_lift {E : Type*} [TopologicalSpace E] {f : Torus d → E}
    (h : Continuous (Torus.lift f)) : Continuous f :=
  isOpenQuotientMap_mk.isQuotientMap.continuous_iff.2 h

/-! ### Pointwise facts about the heat regularisations and about `∇g` -/

section Kernel

variable {s : ℝ}

theorem mk_neg (y : Euc d) : Torus.mk (-y) = -Torus.mk y := by
  funext i
  simp [Torus.mk]

theorem sinMode_neg_arg (k : Lattice d) (x : Torus d) :
    Torus.sinMode k (-x) = - Torus.sinMode k x := by
  obtain ⟨y, rfl, -⟩ := exists_mk_box x
  rw [← mk_neg, Torus.sinMode_mk, Torus.sinMode_mk]
  have : Lattice.dot k (-y) = - Lattice.dot k y := by
    simp [Lattice.dot, Finset.sum_neg_distrib]
  rw [this, mul_neg, Real.sin_neg]

theorem heatRieszGrad_neg (ε : ℝ) (x : Torus d) :
    heatRieszGrad d s ε (-x) = - heatRieszGrad d s ε x := by
  unfold heatRieszGrad
  rw [← tsum_neg]
  refine tsum_congr fun k => ?_
  rw [sinMode_neg_arg]
  simp only [mul_neg, neg_neg, neg_smul]

theorem heatRieszGrad_zero_arg (ε : ℝ) : heatRieszGrad d s ε 0 = 0 := by
  unfold heatRieszGrad
  have h : ∀ k : Lattice d, Torus.sinMode k 0 = 0 := by
    intro k
    have := sinMode_neg_arg (d := d) k 0
    simp only [neg_zero] at this
    linarith
  simp [h]

theorem heat_tendsto (hsd : s < d) (x : Torus d) :
    Tendsto (fun ε => heatRieszGrad d s ε x) (𝓝[>] 0) (𝓝 (periodicRieszGrad d s x)) := by
  by_cases hx : x = 0
  · subst hx
    have h0 : (fun ε => heatRieszGrad d s ε 0) = fun _ => (0 : Euc d) := by
      funext ε; exact heatRieszGrad_zero_arg ε
    rw [h0]
    have : periodicRieszGrad d s 0 = 0 := by
      unfold periodicRieszGrad
      rw [h0]
      exact (tendsto_const_nhds (x := (0 : Euc d)) (f := 𝓝[>] (0 : ℝ))).limUnder_eq
    rw [this]
    exact tendsto_const_nhds
  · obtain ⟨y, rfl, hy⟩ := exists_mk_box x
    have hy0 : y ≠ 0 := by
      rintro rfl
      apply hx
      funext i; simp [Torus.mk]
    rw [HRS.KernelAux.periodicRieszGrad_eq hsd y hy hy0]
    have h : Tendsto (fun ε => WithLp.ofLp (heatRieszGrad d s ε (Torus.mk y))) (𝓝[>] 0)
        (𝓝 (fun j => HRS.KernelAux.gradComp s j (Torus.mk y))) :=
      tendsto_pi_nhds.mpr fun j => HRS.KernelAux.heatGrad_comp_tendsto hsd y hy hy0 j
    exact ((PiLp.continuous_toLp 2 _).tendsto _).comp h

theorem periodicRieszGrad_neg_of_lt (hsd : s < d) (x : Torus d) :
    periodicRieszGrad d s (-x) = -periodicRieszGrad d s x := by
  have h1 := heat_tendsto hsd (-x)
  have h2 := (heat_tendsto hsd x).neg
  simp_rw [heatRieszGrad_neg] at h1
  exact tendsto_nhds_unique h1 h2

theorem continuous_heatRieszGrad (hsd : s < d) {ε : ℝ} (hε : 0 < ε) :
    Continuous (heatRieszGrad d s ε : Torus d → Euc d) := by
  unfold heatRieszGrad
  refine continuous_tsum (u := fun k : Lattice d => (|rieszConst d s| * 2 * Real.pi) *
    (Lattice.enorm k ^ 1 * Real.exp (-ε * Lattice.enorm k ^ 2))) (fun k => ?_)
    ((HRS.KernelAux.summable_pow_gauss_lattice d hε 1).mul_left _) (fun k x => ?_)
  · have := Torus.continuous_sinMode (d := d) k
    exact ((by fun_prop : Continuous fun x : Torus d => -(rieszCoeff d s k *
      Real.exp (-ε * Lattice.enorm k ^ 2) * 2 * Real.pi * Torus.sinMode k x)).smul continuous_const)
  · rw [norm_smul, Real.norm_eq_abs, abs_neg, abs_mul, abs_mul, abs_mul, abs_mul,
      abs_of_pos (Real.exp_pos _), abs_of_pos Real.pi_pos]
    have h1 := HRS.KernelAux.abs_rieszCoeff_le d s hsd k
    have h2 : |Torus.sinMode k x| ≤ 1 := (Complex.abs_im_le_norm _).trans (Torus.norm_mode k x).le
    have h3 : ‖Lattice.toEuc k‖ = Lattice.enorm k := rfl
    rw [h3, pow_one, abs_two]
    have : 0 ≤ Lattice.enorm k := norm_nonneg _
    calc |rieszCoeff d s k| * Real.exp (-ε * Lattice.enorm k ^ 2) * 2 * Real.pi * |Torus.sinMode k x| *
          Lattice.enorm k ≤ |rieszConst d s| * Real.exp (-ε * Lattice.enorm k ^ 2) * 2 * Real.pi * 1 *
          Lattice.enorm k := by gcongr
      _ = _ := by ring

theorem measurable_periodicRieszGrad (hsd : s < d) : Measurable (periodicRieszGrad d s : Torus d → Euc d) := by
  have hm : ∀ n : ℕ, Measurable (heatRieszGrad d s (1 / ((n : ℝ) + 1)) : Torus d → Euc d) := fun n =>
    (continuous_heatRieszGrad hsd (by positivity)).measurable
  refine measurable_of_tendsto_metrizable hm (tendsto_pi_nhds.mpr fun x => ?_)
  have h1 := heat_tendsto hsd x
  have h2 : Tendsto (fun n : ℕ => 1 / ((n : ℝ) + 1)) atTop (𝓝[>] 0) :=
    tendsto_nhdsWithin_iff.mpr ⟨tendsto_one_div_add_atTop_nhds_zero_nat,
      Eventually.of_forall fun n => by simp only [Set.mem_Ioi]; positivity⟩
  exact h1.comp h2

theorem periodicRieszGrad_bound_tdist_aux (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, ∀ z : Torus d, z ≠ 0 →
      ‖periodicRieszGrad d s z‖ ≤ C * (tdist z 0 ^ (-s - 1) + 1) := by
  obtain ⟨C, hC⟩ := periodicRiesz_grad_bound hd hs0 hsd
  refine ⟨C, fun z hz => ?_⟩
  obtain ⟨y, rfl, hy⟩ := exists_mk_box z
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hz
    funext i; simp [Torus.mk]
  rw [tdist_mk hy]
  exact hC y hy0 hy

end Kernel

/-! ### Uniform bounds for the heat regularisations of `∇g` -/

section HeatBound

variable {s : ℝ}

theorem integrableOn_min_rpow {a n c : ℝ} (ha : 0 < a) (han : a < n) (hc : 0 ≤ c) :
    IntegrableOn (fun v : ℝ => v ^ (a - 1) * min c (v ^ (-n))) (Ioi 0) := by
  have h1 : IntegrableOn (fun v : ℝ => v ^ (a - 1) * min c (v ^ (-n))) (Ioc 0 1) := by
    have h : IntegrableOn (fun v : ℝ => c * v ^ (a - 1)) (Ioc 0 1) := by
      have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1) (r := a - 1) (by linarith))
      rw [intervalIntegrable_iff_integrableOn_Ioc_of_le zero_le_one] at this
      exact this.const_mul c
    refine h.mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      fun_prop
    · refine (ae_restrict_iff' measurableSet_Ioc).mpr (Eventually.of_forall fun v hv => ?_)
      have hv0 : 0 < v := hv.1
      have hp : 0 < v ^ (a - 1) := Real.rpow_pos_of_pos hv0 _
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := le_min hc (Real.rpow_nonneg hv0.le (-n)); positivity)]
      rw [mul_comm c]
      exact mul_le_mul_of_nonneg_left (min_le_left _ _) hp.le
  have h2 : IntegrableOn (fun v : ℝ => v ^ (a - 1) * min c (v ^ (-n))) (Ioi 1) := by
    have h : IntegrableOn (fun v : ℝ => v ^ (a - 1 + -n)) (Ioi 1) :=
      integrableOn_Ioi_rpow_of_lt (by linarith) zero_lt_one
    refine h.mono' ?_ ?_
    · refine Measurable.aestronglyMeasurable ?_
      fun_prop
    · refine (ae_restrict_iff' measurableSet_Ioi).mpr (Eventually.of_forall fun v hv => ?_)
      have hv0 : 0 < v := lt_trans zero_lt_one hv
      have hp : 0 < v ^ (a - 1) := Real.rpow_pos_of_pos hv0 _
      rw [Real.norm_eq_abs, abs_of_nonneg (by have := le_min hc (Real.rpow_nonneg hv0.le (-n)); positivity),
        Real.rpow_add hv0]
      exact mul_le_mul_of_nonneg_left (min_le_right _ _) hp.le
  have := h1.union h2
  rwa [Ioc_union_Ioi_eq_Ioi zero_le_one] at this

theorem min_rpow_scaling {a n c θ : ℝ} (hθ : 0 < θ) {t : ℝ} (ht : 0 < t) :
    t ^ (a - 1) * min (c * θ ^ (-n)) (t ^ (-n)) =
      θ ^ (a - 1 - n) * ((θ⁻¹ * t) ^ (a - 1) * min c ((θ⁻¹ * t) ^ (-n))) := by
  obtain ⟨w, hw, rfl⟩ : ∃ w : ℝ, 0 < w ∧ t = θ * w := ⟨θ⁻¹ * t, by positivity, by field_simp⟩
  have hw' : θ⁻¹ * (θ * w) = w := by field_simp
  rw [hw', Real.mul_rpow hθ.le hw.le, Real.mul_rpow hθ.le hw.le]
  have hθn : 0 ≤ θ ^ (-n) := Real.rpow_nonneg hθ.le _
  have : min (c * θ ^ (-n)) (θ ^ (-n) * w ^ (-n)) = θ ^ (-n) * min c (w ^ (-n)) := by
    rw [mul_comm c]; exact (mul_min_of_nonneg _ _ hθn).symm
  rw [this, show a - 1 - n = (a - 1) + (-n) by ring, Real.rpow_add hθ]
  ring

theorem integral_min_rpow {a n c θ : ℝ} (ha : 0 < a) (han : a < n) (hc : 0 ≤ c) (hθ : 0 < θ) :
    IntegrableOn (fun t : ℝ => t ^ (a - 1) * min (c * θ ^ (-n)) (t ^ (-n))) (Ioi 0) ∧
    ∫ t in Ioi (0:ℝ), t ^ (a - 1) * min (c * θ ^ (-n)) (t ^ (-n)) =
      θ ^ (a - n) * ∫ v in Ioi (0:ℝ), v ^ (a - 1) * min c (v ^ (-n)) := by
  set F : ℝ → ℝ := fun v => v ^ (a - 1) * min c (v ^ (-n)) with hF
  have hEq : ∀ t ∈ Ioi (0:ℝ), t ^ (a - 1) * min (c * θ ^ (-n)) (t ^ (-n)) =
      θ ^ (a - 1 - n) * F (θ⁻¹ * t) := fun t ht => min_rpow_scaling hθ ht
  have hθi : 0 < θ⁻¹ := inv_pos.mpr hθ
  constructor
  · have h1 : IntegrableOn (fun t => F (θ⁻¹ * t)) (Ioi 0) :=
      (integrableOn_Ioi_comp_mul_left_iff F 0 hθi).mpr (by
        rw [mul_zero]; exact integrableOn_min_rpow ha han hc)
    have h2 : IntegrableOn (fun t => θ ^ (a - 1 - n) * F (θ⁻¹ * t)) (Ioi 0) := h1.const_mul _
    exact h2.congr_fun (fun t ht => (hEq t ht).symm) measurableSet_Ioi
  · rw [setIntegral_congr_fun measurableSet_Ioi hEq, integral_const_mul,
      integral_comp_mul_left_Ioi F 0 hθi, mul_zero, inv_inv, smul_eq_mul, ← mul_assoc,
      ← Real.rpow_add_one hθ.ne']
    congr 2
    ring


open scoped Real in
theorem heat_comp_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (j : Fin d) :
    ∃ C1 C2 : ℝ, 0 ≤ C1 ∧ 0 ≤ C2 ∧ ∀ ε : ℝ, 0 < ε → ∀ y : Euc d, (∀ i, |y i| ≤ 1 / 2) → y ≠ 0 →
      |heatRieszGrad d s ε (Torus.mk y) j| ≤ C1 * ‖y‖ ^ (-s - 1) + C2 := by
  obtain ⟨K, hK0, hK⟩ := HRS.KernelAux.psiG_small_bound (d := d) j
  obtain ⟨M1, hM10, hM1⟩ := HRS.KernelAux.psiG_large_bound (d := d) j
  set a : ℝ := ((d:ℝ) - s) / 2 with ha_def
  have ha : 0 < a := by rw [ha_def]; linarith
  set n : ℝ := (d:ℝ) / 2 + 1 with hn_def
  have hn : 0 < n := by rw [hn_def]; positivity
  have han : a < n := by rw [ha_def, hn_def]; linarith
  set c : ℝ := n ^ n * Real.exp (-n) with hc_def
  have hc0 : 0 ≤ c := by positivity
  set P : ℝ := 2 * π ^ 2 * Real.sqrt π ^ d with hP
  have hP0 : 0 ≤ P := by positivity
  set A := HRS.KernelAux.subA d s with hA
  have hA0 : 0 ≤ A := HRS.KernelAux.subA_nonneg hd hs0 hsd
  set C0 : ℝ := ∫ v in Ioi (0:ℝ), v ^ (a - 1) * min c (v ^ (-n)) with hC0
  have hC00 : 0 ≤ C0 := by
    refine setIntegral_nonneg measurableSet_Ioi fun v hv => ?_
    have hv0 : (0:ℝ) < v := hv
    have := le_min hc0 (Real.rpow_nonneg hv0.le (-n))
    have := Real.rpow_pos_of_pos hv0 (a - 1)
    positivity
  set θ2 : ℝ := π ^ 2 / 8 with hθ2
  have hθ2p : 0 < θ2 := by positivity
  refine ⟨A * (P * C0 * π ^ (-(s + 2))), A * (P * K * (θ2 ^ (a - n) * C0) + M1 * Real.Gamma a),
    by positivity, by have := (Real.Gamma_pos_of_pos ha).le; positivity,
    fun ε hε y hy hy0 => ?_⟩
  have hr : 0 < ‖y‖ := norm_pos_iff.mpr hy0
  set θ1 : ℝ := π ^ 2 * ‖y‖ ^ 2 with hθ1
  have hθ1p : 0 < θ1 := by positivity
  set m1 : ℝ → ℝ := fun u => min (c * θ1 ^ (-n)) (u ^ (-n)) with hm1
  set m2 : ℝ → ℝ := fun u => min (c * θ2 ^ (-n)) (u ^ (-n)) with hm2
  set Bm : ℝ → ℝ := fun t => P * ‖y‖ * m1 t + P * K * m2 t + M1 * Real.exp (-t) with hBm
  -- antitone majorants
  have hmono : ∀ (X : ℝ) {t u : ℝ}, 0 < t → t ≤ u → min X (u ^ (-n)) ≤ min X (t ^ (-n)) := by
    intro X t u ht htu
    exact min_le_min_left _ (Real.rpow_le_rpow_of_nonpos ht htu (by linarith))
  have hexpmin : ∀ (θ : ℝ), 0 < θ → ∀ u : ℝ, 0 < u →
      u ^ (-n) * Real.exp (-θ / u) ≤ min (c * θ ^ (-n)) (u ^ (-n)) := by
    intro θ hθ u hu
    refine le_min (HRS.KernelAux.t_pow_exp_bound hn hθ hu) ?_
    have : Real.exp (-θ / u) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      have : 0 ≤ θ / u := by positivity
      rw [neg_div]; linarith
    have hp := Real.rpow_nonneg hu.le (-n)
    nlinarith
  have hpsi : ∀ u : ℝ, 0 < u → |HRS.KernelAux.psiG j (Torus.mk y) u| ≤ Bm u := by
    intro u hu
    have h1 : 0 ≤ P * ‖y‖ * m1 u := by
      have := le_min (mul_nonneg hc0 (Real.rpow_nonneg hθ1p.le (-n))) (Real.rpow_nonneg hu.le (-n))
      positivity
    have h2 : 0 ≤ P * K * m2 u := by
      have := le_min (mul_nonneg hc0 (Real.rpow_nonneg hθ2p.le (-n))) (Real.rpow_nonneg hu.le (-n))
      positivity
    have h3 : 0 ≤ M1 * Real.exp (-u) := by positivity
    rcases le_or_gt u 1 with hu1 | hu1
    · have h := hK y hy u hu hu1
      have hpow : Real.sqrt (π / u) ^ d * (2 * π ^ 2 / u) = P * u ^ (-n) := by
        rw [HRS.KernelAux.sqrt_div_pow_eq d hu, hP, div_eq_mul_inv (2 * π ^ 2), ← Real.rpow_neg_one u,
          hn_def]
        have : Real.sqrt π ^ d * u ^ (-(d:ℝ)/2) * (2 * π ^ 2 * u ^ (-1:ℝ)) =
            2 * π ^ 2 * Real.sqrt π ^ d * (u ^ (-(d:ℝ)/2) * u ^ (-1:ℝ)) := by ring
        rw [this, ← Real.rpow_add hu]
        congr 2; ring
      have e1 : Real.exp (-(π ^ 2 * ‖y‖ ^ 2 / u)) = Real.exp (-θ1 / u) := by rw [hθ1, neg_div]
      have e2 : Real.exp (-(π ^ 2 / (8 * u))) = Real.exp (-θ2 / u) := by
        rw [hθ2]; congr 1; field_simp
      rw [hpow, e1, e2] at h
      refine h.trans ?_
      have k1 := hexpmin θ1 hθ1p u hu
      have k2 := hexpmin θ2 hθ2p u hu
      have : P * u ^ (-n) * (‖y‖ * Real.exp (-θ1 / u) + K * Real.exp (-θ2 / u)) =
          P * ‖y‖ * (u ^ (-n) * Real.exp (-θ1 / u)) + P * K * (u ^ (-n) * Real.exp (-θ2 / u)) := by ring
      rw [this]
      simp only [hBm]
      have := mul_le_mul_of_nonneg_left k1 (mul_nonneg hP0 hr.le)
      have := mul_le_mul_of_nonneg_left k2 (mul_nonneg hP0 hK0)
      simp only [hm1, hm2]
      linarith
    · have h := hM1 (Torus.mk y) u hu1.le
      refine h.trans ?_
      simp only [hBm]
      linarith [mul_comm M1 (Real.exp (-u))]
  have hBanti : ∀ t ε : ℝ, 0 < t → 0 ≤ ε → Bm (t + ε) ≤ Bm t := by
    intro t ε ht hε
    simp only [hBm, hm1, hm2]
    have e1 := hmono (c * θ1 ^ (-n)) ht (show t ≤ t + ε by linarith)
    have e2 := hmono (c * θ2 ^ (-n)) ht (show t ≤ t + ε by linarith)
    have e3 : Real.exp (-(t + ε)) ≤ Real.exp (-t) := Real.exp_le_exp.mpr (by linarith)
    have := mul_le_mul_of_nonneg_left e1 (mul_nonneg hP0 hr.le)
    have := mul_le_mul_of_nonneg_left e2 (mul_nonneg hP0 hK0)
    have := mul_le_mul_of_nonneg_left e3 hM10
    linarith
  -- integrals
  obtain ⟨hi1, hv1⟩ := integral_min_rpow ha han hc0 hθ1p
  obtain ⟨hi2, hv2⟩ := integral_min_rpow ha han hc0 hθ2p
  have hGi := Real.GammaIntegral_convergent ha
  have heq : ∀ t : ℝ, t ^ (a - 1) * Bm t = P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n))) +
      P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n))) +
      M1 * (Real.exp (-t) * t ^ (a - 1)) := by
    intro t; simp only [hBm, hm1, hm2]; ring
  have hBi : IntegrableOn (fun t => t ^ (a - 1) * Bm t) (Ioi 0) := by
    have h : IntegrableOn (fun t : ℝ => P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n))) +
      P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n))) +
      M1 * (Real.exp (-t) * t ^ (a - 1))) (Ioi 0) :=
      ((hi1.const_mul _).add (hi2.const_mul _)).add (hGi.const_mul _)
    exact h.congr_fun (fun t _ => (heq t).symm) measurableSet_Ioi
  have hBint : ∫ t in Ioi (0:ℝ), t ^ (a - 1) * Bm t =
      P * ‖y‖ * (θ1 ^ (a - n) * C0) + P * K * (θ2 ^ (a - n) * C0) + M1 * Real.Gamma a := by
    rw [setIntegral_congr_fun measurableSet_Ioi (fun t _ => heq t)]
    have f1 : IntegrableOn (fun t : ℝ => P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n)))) (Ioi 0) :=
      hi1.const_mul _
    have f2 : IntegrableOn (fun t : ℝ => P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n)))) (Ioi 0) :=
      hi2.const_mul _
    have f3 : IntegrableOn (fun t : ℝ => M1 * (Real.exp (-t) * t ^ (a - 1))) (Ioi 0) := hGi.const_mul _
    have f12 : IntegrableOn (fun t : ℝ => P * ‖y‖ * (t ^ (a - 1) * min (c * θ1 ^ (-n)) (t ^ (-n))) +
        P * K * (t ^ (a - 1) * min (c * θ2 ^ (-n)) (t ^ (-n)))) (Ioi 0) := f1.add f2
    rw [integral_add f12 f3, integral_add f1 f2, integral_const_mul, integral_const_mul,
      integral_const_mul, hv1, hv2, ← Real.Gamma_eq_integral ha]
  have hint : |∫ t in Ioi (0:ℝ), t ^ (a - 1) * HRS.KernelAux.psiG j (Torus.mk y) (t + ε)| ≤
      ∫ t in Ioi (0:ℝ), t ^ (a - 1) * Bm t := by
    rw [← Real.norm_eq_abs]
    refine norm_integral_le_of_norm_le hBi ((ae_restrict_iff' measurableSet_Ioi).mpr
      (Eventually.of_forall fun t ht => ?_))
    have ht0 : (0:ℝ) < t := ht
    have hp := Real.rpow_pos_of_pos ht0 (a - 1)
    rw [Real.norm_eq_abs, abs_mul, abs_of_pos hp]
    exact mul_le_mul_of_nonneg_left ((hpsi (t + ε) (by linarith)).trans (hBanti t ε ht0 hε.le)) hp.le
  have hθ1pow : ‖y‖ * θ1 ^ (a - n) = π ^ (-(s + 2)) * ‖y‖ ^ (-s - 1) := by
    have hexp : a - n = -(s / 2 + 1) := by rw [ha_def, hn_def]; ring
    rw [hexp, hθ1, Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_natCast, ← Real.rpow_mul Real.pi_pos.le, ← Real.rpow_mul hr.le]
    have e3 : ‖y‖ * (π ^ ((2:ℕ) * -(s / 2 + 1) : ℝ) * ‖y‖ ^ ((2:ℕ) * -(s / 2 + 1) : ℝ)) =
        π ^ ((2:ℕ) * -(s / 2 + 1) : ℝ) * (‖y‖ ^ (1:ℝ) * ‖y‖ ^ ((2:ℕ) * -(s / 2 + 1) : ℝ)) := by
      rw [Real.rpow_one]; ring
    rw [e3, ← Real.rpow_add hr]
    congr 2 <;> push_cast <;> ring
  rw [HRS.KernelAux.heatRieszGrad_eq_integral hsd hε (Torus.mk y) j]
  change |A * _| ≤ _
  rw [abs_mul, abs_of_nonneg hA0]
  calc A * |∫ t in Ioi (0:ℝ), t ^ (a - 1) * HRS.KernelAux.psiG j (Torus.mk y) (t + ε)|
      ≤ A * (P * ‖y‖ * (θ1 ^ (a - n) * C0) + P * K * (θ2 ^ (a - n) * C0) + M1 * Real.Gamma a) := by
        gcongr
        exact hint.trans (le_of_eq hBint)
    _ = A * (P * C0 * (‖y‖ * θ1 ^ (a - n))) + A * (P * K * (θ2 ^ (a - n) * C0) + M1 * Real.Gamma a) := by ring
    _ = _ := by rw [hθ1pow]; ring


theorem heatRieszGrad_bound (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) :
    ∃ C : ℝ, ∀ ε : ℝ, 0 < ε → ∀ z : Torus d, z ≠ 0 →
      ‖heatRieszGrad d s ε z‖ ≤ C * (tdist z 0 ^ (-s - 1) + 1) := by
  choose C1 C2 hC1 hC2 hC using fun j => heat_comp_bound hd hs0 hsd j
  refine ⟨∑ j, (C1 j + C2 j), fun ε hε z hz => ?_⟩
  obtain ⟨y, rfl, hy⟩ := exists_mk_box z
  have hy0 : y ≠ 0 := by
    rintro rfl
    apply hz
    funext i; simp [Torus.mk]
  rw [tdist_mk hy]
  have h1 := HRS.KernelAux.norm_toLp_le_sum (WithLp.ofLp (heatRieszGrad d s ε (Torus.mk y)))
  rw [WithLp.toLp_ofLp] at h1
  refine h1.trans ?_
  have hr : 0 ≤ ‖y‖ ^ (-s - 1) := Real.rpow_nonneg (norm_nonneg _) _
  rw [Finset.sum_mul]
  refine Finset.sum_le_sum fun j _ => (hC j ε hε y hy hy0).trans ?_
  have := hC1 j
  have := hC2 j
  nlinarith

end HeatBound

end HRS.KernelGrad
