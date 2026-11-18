import HRS.MS.WrCalAux2

/-!
# HRS.MS.WrCal -- the calibration minimiser `t_N` over an abstract feature space (WR-11a, T4)

Packet WR-11a of `docs/WR_B_PLAN.md` (contract C2).  Euclidean port of
`HRS/Equilibrium/CalibratedReference.lean:82-104, 259-330, 390, 474, 503, 567` where the feature space
`ℝ^M` is replaced by an arbitrary real Hilbert space `H` (the minimiser comes from strong convexity and the
parallelogram law, `WrCalAux2`, not from compactness or weak lower semicontinuity).

Setting: `μ` a probability measure on `Euc d`, `Ψ : Euc d → H`, `Ξ = Ψ - ∫ Ψ dμ`,
`Yf t X = ∑ i ⟪t, Ξ (X i)⟫`, `R0 = pairGibbsLawE q N β μ` (the weak reference of an `EWeakKernel μ a q`),
`calibF t = N⁻¹ log E_{R0} exp (Yf t)`, `calibObj t = calibF t + ‖t‖²/(2β)`.

Adjustment with respect to the plan (documented, harmless): the hypothesis `FeatHyp Ψ k` of WR-10 is not
available in this worktree, and only its continuity field is used here, so it is replaced by the structure
`CalFeat Ψ B` (`Continuous Ψ` and `‖Ψ x‖ ≤ B`).  Any `FeatHyp Ψ k` with `‖Ψ x‖ ≤ B` gives `CalFeat Ψ B` by
its `cont` field.  Neither the inner-product identity `⟪Ψ x, Ψ y⟫ = k (x - y)` nor separability of `H` is
needed.  `H` is only assumed complete.  `EWeakKernel μ a q` is used with any real `a` (the partition
function bounds are applied to `max a 0`).

Exports (names in `HRS.MS.Wr`):
* defs `Xi`, `Yf`, `empXi`, `calibF`, `calibObj`, `tN`, `RN`, `Xibar`;
* `CalFeat.integrable_exp_Yf`, `CalFeat.measurable_Yf`, `CalFeat.abs_Yf_le` (boundedness of `exp (s * Yf t)`);
* `calibF_convexOn`, `calibObj_strongConvexOn` (`StrongConvexOn univ (1/β)`), `calibObj_hasDerivAt`
  (Gateaux derivative along every direction `v : H`);
* `exists_calib_min`, `calib_min_unique`, `tN_spec`;
* `tN_eq : tN = -β • Xibar`, `tN_norm_le : ‖tN‖ ≤ β ‖∫ empXi ∂R0‖`;
* `isProb_RN`, `RN_eq_withDensity` (density `w/Z0 * exp (Yf tN)/Z` against `Measure.pi`),
  `RN_absolutelyContinuous_pi`.
-/

set_option linter.unusedSectionVars false

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal

noncomputable section

namespace HRS.MS.Wr

variable {d : ℕ} {H : Type*} [NormedAddCommGroup H] [InnerProductSpace ℝ H]

/-- The centered features `Ξ = Ψ - μ(Ψ)`. -/
def Xi (μ : Measure (Euc d)) (Ψ : Euc d → H) (x : Euc d) : H := Ψ x - ∫ y, Ψ y ∂μ

/-- The linear statistic `∑_i ⟪t, Ξ (x_i)⟫`. -/
def Yf (μ : Measure (Euc d)) (Ψ : Euc d → H) {N : ℕ} (t : H) (X : Fin N → Euc d) : ℝ :=
  ∑ i, inner ℝ t (Xi μ Ψ (X i))

/-- The empirical average `μ_N(Ξ) = N⁻¹ ∑_i Ξ(x_i)`. -/
def empXi (μ : Measure (Euc d)) (Ψ : Euc d → H) {N : ℕ} (X : Fin N → Euc d) : H :=
  (1 / (N : ℝ)) • ∑ i, Xi μ Ψ (X i)

/-- The calibration function `f_N(t) = N⁻¹ log E_{R0}[exp ∑_i ⟪t, Ξ(x_i)⟫]`, `R0 = pairGibbsLawE q N β μ`. -/
def calibF (q : Euc d → Euc d → ℝ) (μ : Measure (Euc d)) (Ψ : Euc d → H) (β : ℝ) (N : ℕ) (t : H) : ℝ :=
  (1 / (N : ℝ)) * Real.log (∫ X, Real.exp (Yf μ Ψ t X) ∂(pairGibbsLawE q N β μ))

/-- The calibration objective `f_N(t) + ‖t‖²/(2β)`. -/
def calibObj (q : Euc d → Euc d → ℝ) (μ : Measure (Euc d)) (Ψ : Euc d → H) (β : ℝ) (N : ℕ)
    (t : H) : ℝ :=
  calibF q μ Ψ β N t + ‖t‖ ^ 2 / (2 * β)

open Classical in
/-- The calibration parameter `t_N`: a minimiser of `calibObj` (`0` if there is none; existence is
`exists_calib_min`, it is `Classical.choose` of that statement). -/
def tN (q : Euc d → Euc d → ℝ) (μ : Measure (Euc d)) (Ψ : Euc d → H) (β : ℝ) (N : ℕ) : H :=
  if h : ∃ t, ∀ s, calibObj q μ Ψ β N t ≤ calibObj q μ Ψ β N s then h.choose else 0

/-- The calibrated weak reference `R_N`: `R0` tilted by `∑_i ⟪t_N, Ξ(x_i)⟫`. -/
def RN (q : Euc d → Euc d → ℝ) (μ : Measure (Euc d)) (Ψ : Euc d → H) (β : ℝ) (N : ℕ) :
    Measure (Fin N → Euc d) :=
  (pairGibbsLawE q N β μ).tilted (Yf μ Ψ (tN q μ Ψ β N))

/-- `Ξ̄_N = E_{R_N}[μ_N(Ξ)]` (an `H`-valued Bochner integral). -/
def Xibar (q : Euc d → Euc d → ℝ) (μ : Measure (Euc d)) (Ψ : Euc d → H) (β : ℝ) (N : ℕ) : H :=
  ∫ X, empXi μ Ψ X ∂(RN q μ Ψ β N)

/-- Hypotheses on the feature map used by the calibration: continuity and a uniform bound (a
`FeatHyp Ψ k` with `‖Ψ x‖ ≤ B` gives this through its continuity field). -/
structure CalFeat (Ψ : Euc d → H) (B : ℝ) : Prop where
  cont : Continuous Ψ
  bound : ∀ x, ‖Ψ x‖ ≤ B

/-- The unnormalised statistic `S_X = ∑_i Ξ(x_i)`. -/
def wr11_S (μ : Measure (Euc d)) (Ψ : Euc d → H) {N : ℕ} (X : Fin N → Euc d) : H :=
  ∑ i, Xi μ Ψ (X i)

section Basic

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {Ψ : Euc d → H} {B : ℝ} {N : ℕ}

lemma CalFeat.B_nonneg (h : CalFeat Ψ B) : 0 ≤ B := (norm_nonneg _).trans (h.bound 0)

lemma CalFeat.integrable_Ψ (h : CalFeat Ψ B) : Integrable Ψ μ :=
  Integrable.of_bound h.cont.stronglyMeasurable.aestronglyMeasurable B
    (Eventually.of_forall h.bound)

lemma CalFeat.continuous_Xi (h : CalFeat Ψ B) : Continuous (Xi μ Ψ) :=
  h.cont.sub continuous_const

lemma CalFeat.norm_Xi_le [CompleteSpace H] (h : CalFeat Ψ B) (x : Euc d) : ‖Xi μ Ψ x‖ ≤ 2 * B := by
  unfold Xi
  have h1 : ‖∫ y, Ψ y ∂μ‖ ≤ B := by
    have := norm_integral_le_of_norm_le_const (μ := μ) (f := Ψ) (C := B)
      (Eventually.of_forall h.bound)
    simpa using this
  calc ‖Ψ x - ∫ y, Ψ y ∂μ‖ ≤ ‖Ψ x‖ + ‖∫ y, Ψ y ∂μ‖ := norm_sub_le _ _
    _ ≤ 2 * B := by linarith [h.bound x]

lemma CalFeat.continuous_S (h : CalFeat Ψ B) : Continuous (wr11_S μ Ψ (N := N)) := by
  unfold wr11_S
  exact continuous_finsetSum _ fun i _ => h.continuous_Xi.comp (continuous_apply i)

lemma CalFeat.wr11_bdd [CompleteSpace H] (h : CalFeat Ψ B) :
    Wr11Bdd (wr11_S μ Ψ (N := N)) (N * (2 * B)) where
  meas := h.continuous_S.stronglyMeasurable
  bound X := by
    unfold wr11_S
    calc ‖∑ i, Xi μ Ψ (X i)‖ ≤ ∑ i, ‖Xi μ Ψ (X i)‖ := norm_sum_le _ _
      _ ≤ ∑ _i : Fin N, 2 * B := Finset.sum_le_sum fun i _ => h.norm_Xi_le _
      _ = N * (2 * B) := by simp
  C_nonneg := by have := h.B_nonneg; positivity

lemma wr11_Yf_eq (t : H) (X : Fin N → Euc d) : Yf μ Ψ t X = wr11_Ya (wr11_S μ Ψ) t X := by
  unfold Yf wr11_Ya wr11_S
  rw [inner_sum]

lemma wr11_Yf_funext (t : H) : (Yf μ Ψ t : (Fin N → Euc d) → ℝ) = wr11_Ya (wr11_S μ Ψ) t :=
  funext (wr11_Yf_eq t)

lemma wr11_empXi_eq (X : Fin N → Euc d) : empXi μ Ψ X = (1 / (N : ℝ)) • wr11_S μ Ψ X := rfl

lemma CalFeat.measurable_Yf [CompleteSpace H] (h : CalFeat Ψ B) (t : H) :
    Measurable (Yf μ Ψ (N := N) t) := by
  rw [wr11_Yf_funext]
  exact wr11_measurable_Ya h.wr11_bdd.meas t

lemma CalFeat.abs_Yf_le [CompleteSpace H] (h : CalFeat Ψ B) (t : H) (X : Fin N → Euc d) :
    |Yf μ Ψ t X| ≤ ‖t‖ * (N * (2 * B)) := by
  rw [wr11_Yf_eq]
  exact wr11_abs_Ya_le h.wr11_bdd t X

/-- `exp (s * Yf t)` is integrable for every finite measure (the statistic is bounded). -/
lemma CalFeat.integrable_exp_Yf [CompleteSpace H] (h : CalFeat Ψ B) (P : Measure (Fin N → Euc d))
    [IsFiniteMeasure P] (t : H) (s : ℝ) :
    Integrable (fun X => Real.exp (s * Yf μ Ψ t X)) P := by
  simp_rw [wr11_Yf_eq]
  exact wr11_integrable_exp_Ya h.wr11_bdd t s

lemma CalFeat.integrable_empXi [CompleteSpace H] (h : CalFeat Ψ B) (P : Measure (Fin N → Euc d))
    [IsFiniteMeasure P] : Integrable (empXi μ Ψ) P := by
  have e : empXi μ Ψ = fun X : Fin N → Euc d => (1 / (N : ℝ)) • wr11_S μ Ψ X := rfl
  rw [e]
  exact (wr11_integrable_S (P := P) h.wr11_bdd).smul _

lemma Yf_zero (X : Fin N → Euc d) : Yf μ Ψ (0 : H) X = 0 := by simp [Yf]

lemma Yf_eq_inner (hN : 0 < N) (t : H) (X : Fin N → Euc d) :
    Yf μ Ψ t X = N * inner ℝ t (empXi μ Ψ X) := by
  rw [wr11_Yf_eq, wr11_empXi_eq]
  unfold wr11_Ya
  rw [real_inner_smul_right]
  have : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp

end Basic

section Ref

variable {μ : Measure (Euc d)} [IsProbabilityMeasure μ] {a : ℝ} {q : Euc d → Euc d → ℝ} {N : ℕ}
  {β : ℝ}

lemma EWeakKernel.wr11_mono {a a' : ℝ} (hK : EWeakKernel μ a q) (h : a ≤ a') : EWeakKernel μ a' q :=
  ⟨hK.meas, hK.symm, hK.nonneg, fun x => (hK.row x).trans (ENNReal.ofReal_le_ofReal h)⟩

/-- `R0 = pairGibbsLawE q N β μ` is a probability measure (`β ≥ 0`, `0 < N`). -/
lemma EWeakKernel.wr11_isProb_R0 (hK : EWeakKernel μ a q) (hβ : 0 ≤ β) (hN : 0 < N) :
    IsProbabilityMeasure (pairGibbsLawE q N β μ) := by
  have ha : 0 ≤ max a 0 := le_max_right _ _
  have hK' : EWeakKernel μ (max a 0) q := hK.wr11_mono (le_max_left _ _)
  obtain ⟨h0, htop⟩ := hK'.wr1_partition_pos_lt ha hβ hN
  refine ⟨?_⟩
  unfold pairGibbsLawE
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  simp_rw [div_eq_mul_inv]
  rw [lintegral_mul_const' _ _ (ENNReal.inv_ne_top.2 h0)]
  change pairPartitionE q N β μ * (pairPartitionE q N β μ)⁻¹ = 1
  exact ENNReal.mul_inv_cancel h0 htop

variable [CompleteSpace H] {Ψ : Euc d → H} {B : ℝ}

lemma calibF_eq (t : H) :
    calibF q μ Ψ β N t = (1 / (N : ℝ)) * wr11_cF (pairGibbsLawE q N β μ) (wr11_S μ Ψ) t := by
  unfold calibF wr11_cF wr11_Z
  simp_rw [wr11_Yf_eq]

lemma calibObj_eq :
    calibObj q μ Ψ β N = wr11_obj (1 / (N : ℝ)) β (pairGibbsLawE q N β μ) (wr11_S μ Ψ) := by
  funext t
  unfold calibObj wr11_obj
  rw [calibF_eq]

lemma calibF_zero (hK : EWeakKernel μ a q) (hβ : 0 ≤ β) (hN : 0 < N) : calibF q μ Ψ β N 0 = 0 := by
  haveI := hK.wr11_isProb_R0 hβ hN
  rw [calibF_eq, wr11_cF_zero, mul_zero]

/-- The partition function `∫ exp (Yf t) dR0` is positive. -/
lemma CalFeat.Z_pos (hK : EWeakKernel μ a q) (h : CalFeat Ψ B) (hβ : 0 ≤ β) (hN : 0 < N) (t : H) :
    0 < ∫ X, Real.exp (Yf μ Ψ t X) ∂(pairGibbsLawE q N β μ) := by
  haveI := hK.wr11_isProb_R0 hβ hN
  simp_rw [wr11_Yf_eq]
  exact wr11_Z_pos h.wr11_bdd t

lemma CalFeat.continuous_calibObj (hK : EWeakKernel μ a q) (h : CalFeat Ψ B) (hβ : 0 ≤ β)
    (hN : 0 < N) : Continuous (calibObj q μ Ψ β N) := by
  haveI := hK.wr11_isProb_R0 hβ hN
  rw [calibObj_eq]
  exact wr11_continuous_obj h.wr11_bdd _ _

/-- `calibF` is convex on `H`. -/
theorem calibF_convexOn (hK : EWeakKernel μ a q) (h : CalFeat Ψ B) (hβ : 0 ≤ β) (hN : 0 < N) :
    ConvexOn ℝ Set.univ (calibF q μ Ψ β N) := by
  haveI := hK.wr11_isProb_R0 hβ hN
  have e : calibF q μ Ψ β N = fun t => (1 / (N : ℝ)) • wr11_cF (pairGibbsLawE q N β μ) (wr11_S μ Ψ) t := by
    funext t; rw [calibF_eq, smul_eq_mul]
  rw [e]
  exact (wr11_convexOn_cF h.wr11_bdd).smul (by positivity)

/-- `calibObj` is `(1/β)`-strongly convex on all of `H`. -/
theorem calibObj_strongConvexOn (hK : EWeakKernel μ a q) (h : CalFeat Ψ B) (hβ : 0 < β) (hN : 0 < N) :
    StrongConvexOn Set.univ (1 / β) (calibObj q μ Ψ β N) := by
  haveI := hK.wr11_isProb_R0 hβ.le hN
  rw [calibObj_eq]
  exact wr11_strongConvexOn_obj h.wr11_bdd (by positivity) hβ

/-- Gateaux derivative of `calibObj` along every direction `v : H`
(`HRS/Equilibrium/CalibratedReference.lean:474` with coordinates replaced by `v`). -/
theorem calibObj_hasDerivAt (hK : EWeakKernel μ a q) (h : CalFeat Ψ B) (hβ : 0 < β) (hN : 0 < N)
    (t v : H) :
    HasDerivAt (fun s : ℝ => calibObj q μ Ψ β N (t + s • v))
      ((1 / (N : ℝ)) * ∫ X, Yf μ Ψ v X ∂((pairGibbsLawE q N β μ).tilted (Yf μ Ψ t)) +
        inner ℝ t v / β) 0 := by
  haveI := hK.wr11_isProb_R0 hβ.le hN
  have := wr11_hasDerivAt_obj (P := pairGibbsLawE q N β μ) (h.wr11_bdd (μ := μ) (N := N)) (1 / (N : ℝ)) β hβ t v
  rw [calibObj_eq, wr11_Yf_funext, wr11_Yf_funext]
  exact this

/-- **Existence of the calibration minimiser** (strong convexity + parallelogram law). -/
theorem exists_calib_min (hK : EWeakKernel μ a q) (h : CalFeat Ψ B) (hβ : 0 < β) (hN : 0 < N) :
    ∃ t, ∀ s, calibObj q μ Ψ β N t ≤ calibObj q μ Ψ β N s := by
  haveI := hK.wr11_isProb_R0 hβ.le hN
  rw [calibObj_eq]
  exact wr11_exists_obj_min h.wr11_bdd (by positivity) hβ

/-- The calibration minimiser is unique. -/
theorem calib_min_unique (hK : EWeakKernel μ a q) (h : CalFeat Ψ B) (hβ : 0 < β) (hN : 0 < N)
    {t₁ t₂ : H} (h₁ : ∀ s, calibObj q μ Ψ β N t₁ ≤ calibObj q μ Ψ β N s)
    (h₂ : ∀ s, calibObj q μ Ψ β N t₂ ≤ calibObj q μ Ψ β N s) : t₁ = t₂ := by
  haveI := hK.wr11_isProb_R0 hβ.le hN
  rw [calibObj_eq] at h₁ h₂
  exact wr11_obj_unique h.wr11_bdd (by positivity) hβ h₁ h₂

/-- `tN` is a minimiser of `calibObj`. -/
theorem tN_spec (hK : EWeakKernel μ a q) (h : CalFeat Ψ B) (hβ : 0 < β) (hN : 0 < N) (s : H) :
    calibObj q μ Ψ β N (tN q μ Ψ β N) ≤ calibObj q μ Ψ β N s := by
  have hex := exists_calib_min hK h hβ hN
  unfold tN
  rw [dif_pos hex]
  exact hex.choose_spec s

/-- **Stationarity**: `t_N = -β Ξ̄_N`. -/
theorem tN_eq (hK : EWeakKernel μ a q) (h : CalFeat Ψ B) (hβ : 0 < β) (hN : 0 < N) :
    tN q μ Ψ β N = -β • Xibar q μ Ψ β N := by
  haveI := hK.wr11_isProb_R0 hβ.le hN
  have hN' : (0 : ℝ) < 1 / (N : ℝ) := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hmin : ∀ s, wr11_obj (1 / (N : ℝ)) β (pairGibbsLawE q N β μ) (wr11_S μ Ψ) (tN q μ Ψ β N) ≤
      wr11_obj (1 / (N : ℝ)) β (pairGibbsLawE q N β μ) (wr11_S μ Ψ) s := by
    intro s; rw [← calibObj_eq]; exact tN_spec hK h hβ hN s
  have hst := wr11_stationary h.wr11_bdd hN' hβ hmin
  have hX : Xibar q μ Ψ β N = (1 / (N : ℝ)) • ∫ X, wr11_S μ Ψ X ∂(RN q μ Ψ β N) := by
    unfold Xibar
    simp_rw [wr11_empXi_eq]
    exact integral_smul _ _
  have hR : RN q μ Ψ β N = (pairGibbsLawE q N β μ).tilted (wr11_Ya (wr11_S μ Ψ) (tN q μ Ψ β N)) := by
    unfold RN; rw [wr11_Yf_funext]
  have hst' : tN q μ Ψ β N = -(β * (1 / (N : ℝ))) • ∫ X, wr11_S μ Ψ X ∂(RN q μ Ψ β N) := by
    rw [hR]; exact hst
  rw [hX]
  refine hst'.trans ?_
  rw [smul_smul]
  congr 1
  ring

/-- **Norm bound**: `‖t_N‖ ≤ β ‖E_{R0} μ_N(Ξ)‖`. -/
theorem tN_norm_le (hK : EWeakKernel μ a q) (h : CalFeat Ψ B) (hβ : 0 < β) (hN : 0 < N) :
    ‖tN q μ Ψ β N‖ ≤ β * ‖∫ X, empXi μ Ψ X ∂(pairGibbsLawE q N β μ)‖ := by
  haveI := hK.wr11_isProb_R0 hβ.le hN
  have hN' : (0 : ℝ) < 1 / (N : ℝ) := by
    have : (0 : ℝ) < N := by exact_mod_cast hN
    positivity
  have hmin : ∀ s, wr11_obj (1 / (N : ℝ)) β (pairGibbsLawE q N β μ) (wr11_S μ Ψ) (tN q μ Ψ β N) ≤
      wr11_obj (1 / (N : ℝ)) β (pairGibbsLawE q N β μ) (wr11_S μ Ψ) s := by
    intro s; rw [← calibObj_eq]; exact tN_spec hK h hβ hN s
  have := wr11_norm_le h.wr11_bdd hN' hβ hmin
  have e : ∫ X, empXi μ Ψ X ∂(pairGibbsLawE q N β μ) =
      (1 / (N : ℝ)) • ∫ X, wr11_S μ Ψ X ∂(pairGibbsLawE q N β μ) := by
    simp_rw [wr11_empXi_eq]
    exact integral_smul _ _
  rw [e, norm_smul, Real.norm_eq_abs, abs_of_pos hN']
  calc ‖tN q μ Ψ β N‖ ≤ β * (1 / (N : ℝ)) * ‖∫ ω, wr11_S μ Ψ ω ∂(pairGibbsLawE q N β μ)‖ := by
        simpa [mul_comm, mul_left_comm, mul_assoc] using this
    _ = _ := by ring

/-- The calibrated weak reference is a probability measure. -/
theorem isProb_RN (hK : EWeakKernel μ a q) (h : CalFeat Ψ B) (hβ : 0 ≤ β) (hN : 0 < N) :
    IsProbabilityMeasure (RN q μ Ψ β N) := by
  haveI := hK.wr11_isProb_R0 hβ hN
  unfold RN
  have := h.integrable_exp_Yf (μ := μ) (pairGibbsLawE q N β μ) (tN q μ Ψ β N) 1
  simp only [one_mul] at this
  exact isProbabilityMeasure_tilted this

/-- `R_N` has density `w/Z0 * exp (Yf t_N) / Z` with respect to `Measure.pi (fun _ => μ)`, where
`w = pairWeightE`, `Z0 = pairPartitionE`, `Z = ∫ exp (Yf t_N) dR0`. -/
theorem RN_eq_withDensity (hK : EWeakKernel μ a q) (h : CalFeat Ψ B) (hN : 0 < N) :
    RN q μ Ψ β N = (Measure.pi fun _ : Fin N => μ).withDensity
      (fun X => (pairWeightE q N β μ X / pairPartitionE q N β μ) *
        ENNReal.ofReal (Real.exp (Yf μ Ψ (tN q μ Ψ β N) X) /
          ∫ Y, Real.exp (Yf μ Ψ (tN q μ Ψ β N) Y) ∂(pairGibbsLawE q N β μ))) := by
  have hW : Measurable (pairWeightE q N β μ) := hK.wr1_measurable_pairWeight N β
  have hf : Measurable fun X : Fin N → Euc d => pairWeightE q N β μ X / pairPartitionE q N β μ :=
    hW.div_const _
  have hg : Measurable fun X : Fin N → Euc d => ENNReal.ofReal (Real.exp (Yf μ Ψ (tN q μ Ψ β N) X) /
      ∫ Y, Real.exp (Yf μ Ψ (tN q μ Ψ β N) Y) ∂(pairGibbsLawE q N β μ)) :=
    ENNReal.measurable_ofReal.comp
      ((Real.measurable_exp.comp (h.measurable_Yf _)).div_const _)
  exact (withDensity_mul _ hf hg).symm

/-- `R_N` is absolutely continuous with respect to `Measure.pi (fun _ => μ)`. -/
theorem RN_absolutelyContinuous_pi (hK : EWeakKernel μ a q) (h : CalFeat Ψ B) (hN : 0 < N) :
    RN q μ Ψ β N ≪ Measure.pi fun _ : Fin N => μ := by
  rw [RN_eq_withDensity hK h hN]
  exact withDensity_absolutelyContinuous _ _

end Ref

end HRS.MS.Wr
