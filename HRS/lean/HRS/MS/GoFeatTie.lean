import HRS.MS.GoFeatAux5

/-!
# S5.5 features: assembly (conditional on `t`-measurability)

See the report; helper names carry the prefix `s55f_`; namespace `HRS.MS.Go`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.Go
open HRS HRS.Whole HRS.MP.RdGen

variable {d : ℕ}

/-! ### Embeddings into `𝒦` -/

lemma s55f_norm_mk_le {m T : ℝ} (a a' b : _) :
    ‖(KSpace.mk a a' b : KSpace d m T)‖ ≤ ‖(a : OscDual d m)‖ + ‖(a' : L2Path d m T)‖ + ‖(b : OscDual d m)‖ := by
  unfold KSpace.mk
  show ‖(WithLp.toLp 2 (a, WithLp.toLp 2 (a', b)) :
    WithLp 2 (OscDual d m × WithLp 2 (L2Path d m T × OscDual d m)))‖ ≤ _
  rw [WithLp.prod_norm_eq_of_L2]
  change Real.sqrt (‖a‖ ^ 2 + ‖(WithLp.toLp 2 (a', b) : WithLp 2 (L2Path d m T × OscDual d m))‖ ^ 2) ≤ _
  rw [WithLp.prod_norm_eq_of_L2]
  change Real.sqrt (‖a‖ ^ 2 + Real.sqrt (‖a'‖ ^ 2 + ‖b‖ ^ 2) ^ 2) ≤ _
  have h1 : Real.sqrt (‖a'‖ ^ 2 + ‖b‖ ^ 2) ≤ ‖a'‖ + ‖b‖ :=
    Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [norm_nonneg a', norm_nonneg b]⟩
  have h2 : Real.sqrt (‖a‖ ^ 2 + Real.sqrt (‖a'‖ ^ 2 + ‖b‖ ^ 2) ^ 2) ≤ ‖a‖ + Real.sqrt (‖a'‖ ^ 2 + ‖b‖ ^ 2) :=
    Real.sqrt_le_iff.2 ⟨by positivity, by nlinarith [norm_nonneg a, Real.sqrt_nonneg (‖a'‖ ^ 2 + ‖b‖ ^ 2)]⟩
  linarith

/-- The continuous linear equivalence `𝒦 ≃ ℓ² × (L²_t × ℓ²)` (plain product). -/
def s55fE (m T : ℝ) : KSpace d m T ≃L[ℝ] (OscDual d m × (L2Path d m T × OscDual d m)) :=
  (WithLp.prodContinuousLinearEquiv 2 ℝ (OscDual d m) (WithLp 2 (L2Path d m T × OscDual d m))).trans
    (ContinuousLinearEquiv.prodCongr (ContinuousLinearEquiv.refl ℝ (OscDual d m))
      (WithLp.prodContinuousLinearEquiv 2 ℝ (L2Path d m T) (OscDual d m)))

lemma s55fE_symm_apply (m T : ℝ) (a : OscDual d m) (a' : L2Path d m T) (b : OscDual d m) :
    (s55fE (d := d) m T).symm (a, (a', b)) = KSpace.mk a a' b := rfl

/-- `a ↦ (a, 0, a)`. -/
def s55fΦ₁ (m T : ℝ) : OscDual d m →L[ℝ] KSpace d m T :=
  (s55fE (d := d) m T).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.prod (ContinuousLinearMap.id ℝ _)
      (ContinuousLinearMap.prod 0 (ContinuousLinearMap.id ℝ _)))

/-- `a' ↦ (0, a', 0)`. -/
def s55fΦ₂ (m T : ℝ) : L2Path d m T →L[ℝ] KSpace d m T :=
  (s55fE (d := d) m T).symm.toContinuousLinearMap.comp
    (ContinuousLinearMap.prod 0 (ContinuousLinearMap.prod (ContinuousLinearMap.id ℝ _) 0))

lemma s55fΦ₁_apply (m T : ℝ) (a : OscDual d m) : s55fΦ₁ (d := d) m T a = KSpace.mk a 0 a := rfl

lemma s55fΦ₂_apply (m T : ℝ) (a : L2Path d m T) : s55fΦ₂ (d := d) m T a = KSpace.mk 0 a 0 := rfl

lemma s55fΦ₁_norm (m T : ℝ) : ‖(s55fΦ₁ (d := d) m T)‖ ≤ 2 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun a => ?_
  rw [s55fΦ₁_apply]
  have := s55f_norm_mk_le (d := d) (m := m) (T := T) a 0 a
  simp only [norm_zero, add_zero] at this
  linarith

lemma s55fΦ₂_norm (m T : ℝ) : ‖(s55fΦ₂ (d := d) m T)‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ (by norm_num) fun a => ?_
  rw [s55fΦ₂_apply]
  have := s55f_norm_mk_le (d := d) (m := m) (T := T) 0 a 0
  simp only [norm_zero, zero_add, add_zero] at this
  linarith

lemma s55f_mk_eq {m T : ℝ} (a : OscDual d m) (a' : L2Path d m T) :
    (KSpace.mk a a' a : KSpace d m T) = s55fΦ₁ m T a + s55fΦ₂ m T a' := by
  rw [s55fΦ₁_apply, s55fΦ₂_apply, ← s55fE_symm_apply, ← s55fE_symm_apply, ← s55fE_symm_apply,
    ← map_add]
  simp

/-! ### Uniform bounds on the coordinates of the feature -/

lemma s55f_gradComp {n : ℕ} {f : Euc d → ℝ} (hf : ContDiff ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f) (a : Fin d) :
    ContDiff ℝ (n : WithTop ℕ∞) (fun x => gradComp a f x) ∧
    ∀ j ≤ n, ∀ x, ‖iteratedFDeriv ℝ j (fun x => gradComp a f x) x‖ ≤ ‖iteratedFDeriv ℝ (j + 1) f x‖ := by
  have e : (fun x => gradComp a f x) = fun x => fderiv ℝ f x (EuclideanSpace.single a (1 : ℝ)) := by
    funext y; exact movtr_gradient_apply f y a
  rw [e]
  refine ⟨((hf.fderiv_right (m := n) (by push_cast; exact le_rfl)).clm_apply contDiff_const),
    fun j hj x => ?_⟩
  have := rg_diruv (n := j) (φ := f) (hf.of_le (by exact_mod_cast Nat.succ_le_succ hj))
    (EuclideanSpace.single a 1) x
  rwa [rg_norm_single, one_mul] at this

theorem s55f_base_bound (b : WholeBounds d) (hb : b.Valid) :
    ∃ Cb : ℝ, 0 ≤ Cb ∧ ∀ (a : Fin d) (α : MultiIndex d),
      ContDiff ℝ (b.k : WithTop ℕ∞) (fun x => gradComp a (oscTestFun b.m α) x) ∧
      ∀ j ≤ b.k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => gradComp a (oscTestFun b.m α) x) x‖ ≤
        Cb * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  have hceil := s55f_ceil_half_le d
  have hJ : b.J = 4 * b.k + 4 * d + 40 := rfl
  have hc2 : ⌈(1 + (((b.k + 1 : ℕ) : ℝ))) / 2⌉₊ ≤ b.k + 1 := by
    rw [Nat.ceil_le]; push_cast
    have : (0 : ℝ) ≤ b.k := Nat.cast_nonneg _
    linarith
  obtain ⟨C0, hC0, hosc⟩ := s55_osc_bounds hb.hθ b.m 0 (b.k + 1) 1 (by norm_num) b.J (by omega) (by omega)
  refine ⟨(d : ℝ) ^ (b.k + 1) * C0, by positivity, fun a α => ?_⟩
  obtain ⟨hsm, -, hdec⟩ := hosc α
  have hφ : ContDiff ℝ ((b.k + 1 : ℕ) : WithTop ℕ∞) (oscTestFun b.m α) := s55_cd_of_inf _ hsm
  have hΛ0 : 0 ≤ C0 * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) :=
    mul_nonneg hC0 (Real.rpow_nonneg (oscEigenvalue_pos α).le _)
  have hnorm := s55f_decay_to_norm hφ hdec
  rw [max_eq_left hΛ0] at hnorm
  obtain ⟨hc, hbd⟩ := s55f_gradComp hφ a
  refine ⟨hc, fun j hj x => (hbd j hj x).trans ?_⟩
  have h1 := (hnorm (j + 1) (by omega) x).1
  have h2 : (d : ℝ) ^ (j + 1) ≤ (d : ℝ) ^ (b.k + 1) := pow_le_pow_right₀ hd1' (by omega)
  calc _ ≤ (d : ℝ) ^ (j + 1) * (C0 * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2)) := h1
    _ ≤ (d : ℝ) ^ (b.k + 1) * (C0 * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2)) :=
        mul_le_mul_of_nonneg_right h2 hΛ0
    _ = _ := by ring

theorem s55f_orbit_bound (b : WholeBounds d) (hb : b.Valid) :
    ∃ Co : ℝ, 0 ≤ Co ∧ ∀ (S : WholeSetup b) (N : ℕ) (a : Fin d) (r t : ℝ), 0 ≤ r → r ≤ t → t ≤ b.T →
      ∀ α : MultiIndex d,
      ContDiff ℝ (b.k : WithTop ℕ∞) (fun x => gradComp a
          (propagatorW (S.coeff N) r t (generatorW (S.coeff N) t (oscTestFun b.m α))) x) ∧
      ∀ j ≤ b.k, ∀ x, ‖iteratedFDeriv ℝ j (fun x => gradComp a
          (propagatorW (S.coeff N) r t (generatorW (S.coeff N) t (oscTestFun b.m α))) x) x‖ ≤
        Co * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) := by
  obtain ⟨Cg, hCg0, hCg⟩ := s55f_gen_ul b hb
  refine ⟨|b.K| * Cg, by positivity, fun S N a r t hr hrt htT α => ?_⟩
  have ht : t ∈ Set.Icc (0 : ℝ) b.T := ⟨hr.trans hrt, htT⟩
  obtain ⟨hψ, hul⟩ := hCg S N t ht α
  have hΛ0 : 0 ≤ Cg * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) :=
    mul_nonneg hCg0 (Real.rpow_nonneg (oscEigenvalue_pos α).le _)
  have hulfin : ulNormE (b.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) b.θ
      (generatorW (S.coeff N) t (oscTestFun b.m α)) < ⊤ :=
    lt_of_le_of_lt hul ENNReal.ofReal_lt_top
  obtain ⟨-, hmem, hcb⟩ := S.adjoint N r t hr hrt htT _ hψ hulfin
  have hulr : (ulNormE (b.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) b.θ
      (generatorW (S.coeff N) t (oscTestFun b.m α))).toReal ≤ Cg * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hul
    rwa [ENNReal.toReal_ofReal hΛ0] at this
  have hU := hmem.1
  obtain ⟨hc, hbd⟩ := s55f_gradComp (n := b.k) hU a
  refine ⟨hc, fun j hj x => (hbd j hj x).trans ?_⟩
  -- sup bound
  have hsup : ‖iteratedFDeriv ℝ (j + 1) (propagatorW (S.coeff N) r t
      (generatorW (S.coeff N) t (oscTestFun b.m α))) x‖ ≤
      cbNorm (b.k + 1) (propagatorW (S.coeff N) r t (generatorW (S.coeff N) t (oscTestFun b.m α))) := by
    unfold cbNorm
    have hbdd := hmem.2 (j + 1) (by omega)
    have h1 : ‖iteratedFDeriv ℝ (j + 1) (propagatorW (S.coeff N) r t
        (generatorW (S.coeff N) t (oscTestFun b.m α))) x‖ ≤
        ⨆ z, ‖iteratedFDeriv ℝ (j + 1) (propagatorW (S.coeff N) r t
        (generatorW (S.coeff N) t (oscTestFun b.m α))) z‖ := le_ciSup hbdd x
    refine h1.trans ?_
    exact Finset.single_le_sum (f := fun i => ⨆ z, ‖iteratedFDeriv ℝ i (propagatorW (S.coeff N) r t
      (generatorW (S.coeff N) t (oscTestFun b.m α))) z‖)
      (fun i _ => Real.iSup_nonneg fun _ => norm_nonneg _) (Finset.mem_range.2 (by omega))
  refine hsup.trans (hcb.trans ?_)
  calc b.K * (ulNormE (b.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) b.θ
        (generatorW (S.coeff N) t (oscTestFun b.m α))).toReal
      ≤ |b.K| * (ulNormE (b.k + 1 + 1 + ⌈(d : ℝ) / 2⌉₊) b.θ
        (generatorW (S.coeff N) t (oscTestFun b.m α))).toReal :=
          mul_le_mul_of_nonneg_right (le_abs_self _) ENNReal.toReal_nonneg
    _ ≤ |b.K| * (Cg * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2)) := mul_le_mul_of_nonneg_left hulr (abs_nonneg _)
    _ = _ := by ring

theorem s55f_summable (b : WholeBounds d) (hb : b.Valid) :
    Summable fun α : MultiIndex d => oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  have hm := hb.hm
  have h := (summable_oscEigenvalue_rpow_iff hd1 (-((((b.J : ℝ) - b.m) / 2)))).2 ?_
  · simpa using h
  · have hJ : (b.J : ℝ) = 4 * b.k + 4 * d + 40 := by unfold WholeBounds.J; push_cast; ring
    have : (0 : ℝ) ≤ b.k := Nat.cast_nonneg _
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg _
    rw [hJ] at hm
    linarith

/-! ### Measurability and the assembly -/

lemma s55f_ellVec_zero (m : ℝ) : (ellVec (d := d) m (fun _ => (0 : ℝ))) = 0 := by
  have h : Memℓp (fun _ : MultiIndex d => (0 : ℝ)) 2 := zero_memℓp
  have := s55f_ellVec_eq (m := m) h
  refine (Subtype.ext ?_ : (ellVec (d := d) m (fun _ => (0 : ℝ)) : lp (fun _ : MultiIndex d => ℝ) 2) = 0)
  rw [this]; rfl

lemma s55f_aesm_ellVec {μ : Measure ℝ} {m : ℝ} (v : MultiIndex d → ℝ → ℝ)
    (hv : ∀ α, AEStronglyMeasurable (v α) μ) (hsum : ∀ t, Summable fun α => |v α t|) :
    AEStronglyMeasurable (fun t => ellVec (d := d) m (fun α => v α t)) μ := by
  set ι : ∀ α : MultiIndex d, ℝ →L[ℝ] OscDual d m := fun α =>
    lp.singleContinuousLinearMap (𝕜 := ℝ) (E := fun _ : MultiIndex d => ℝ) 2 α with hι
  refine aestronglyMeasurable_of_tendsto_ae (atTop : Filter (Finset (MultiIndex d)))
    (f := fun (s : Finset (MultiIndex d)) (t : ℝ) => ∑ α ∈ s, ι α (v α t)) ?_ ?_
  · intro s
    exact Finset.aestronglyMeasurable_fun_sum s fun α _ => (ι α).continuous.comp_aestronglyMeasurable (hv α)
  · refine Eventually.of_forall fun t => ?_
    exact (s55f_hasSum_ellVec (m := m) (hsum t))

/-- The `t`-measurability input. -/
def S55fMeas (b : WholeBounds d) (S : WholeSetup b) : Prop :=
  ∀ (N : ℕ) (a : Fin d), ∀ r ∈ Set.Icc (0 : ℝ) b.T, ∀ (α : MultiIndex d) (x : Euc d),
    AEStronglyMeasurable (fun t => gradComp a (propagatorW (S.coeff N) r t
      (generatorW (S.coeff N) t (oscTestFun b.m α))) x) (volume.restrict (Set.Ioc r b.T))

lemma s55f_iter_zero (j : ℕ) (x : Euc d) :
    ‖iteratedFDeriv ℝ j (fun _ : Euc d => (0 : ℝ)) x‖ = 0 := by
  rcases j with _ | j
  · simp
  · rw [iteratedFDeriv_const_of_ne (by omega)]; simp

/-- **Features, conditional on `t`-measurability** (`S55fMeas`): the nonautonomous feature is `C^k` in `x` with
`‖D^j Γ‖ ≤ C`, `j ≤ k`, uniformly in `S, N, a, r`. -/
theorem s55f_features_of_meas (b : WholeBounds d) (hb : b.Valid) :
    ∃ C : ℝ, ∀ S : WholeSetup b, S55fMeas b S → ∀ (N : ℕ) (a : Fin d), ∀ r ∈ Set.Icc (0 : ℝ) b.T,
      ContDiff ℝ (b.k : WithTop ℕ∞) (fun x => gradFeature (S.coeff N) b.m b.T a r x) ∧
      ∀ j ≤ b.k, ∀ x, ‖iteratedFDeriv ℝ j (fun y => gradFeature (S.coeff N) b.m b.T a r y) x‖ ≤ C := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  have hd1' : (1 : ℝ) ≤ d := by exact_mod_cast hd1
  obtain ⟨Cb, hCb0, hCb⟩ := s55f_base_bound b hb
  obtain ⟨Co, hCo0, hCo⟩ := s55f_orbit_bound b hb
  have hsum := s55f_summable b hb
  set Cc : ℝ := max Cb Co with hCc
  set c : MultiIndex d → ℝ := fun α => Cc * oscEigenvalue d α ^ (((b.J : ℝ) - b.m) / 2) with hc
  have hc0 : ∀ α, 0 ≤ c α := fun α =>
    mul_nonneg (le_max_of_le_left hCb0) (Real.rpow_nonneg (oscEigenvalue_pos α).le _)
  have hcs : Summable c := hsum.mul_left Cc
  set Bs : ℝ := ∑' α, c α with hBs
  have hBs0 : 0 ≤ Bs := tsum_nonneg hc0
  set μ : Measure ℝ := volume.restrict (Set.Icc (0 : ℝ) b.T) with hμ
  haveI : IsFiniteMeasure μ := by rw [hμ]; infer_instance
  refine ⟨2 * Bs + (d : ℝ) ^ b.k * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)), fun S hmeas N a r hr => ?_⟩
  set CC := S.coeff N with hCC
  -- the base part
  have hbase := s55f_ell_contDiff (E := Euc d) (m := b.m) (k := b.k)
    (fun α x => gradComp a (oscTestFun b.m α) x) (fun α => (hCb a α).1) c hcs (fun α j hj x =>
      ((hCb a α).2 j hj x).trans (mul_le_mul_of_nonneg_right (le_max_left _ _)
        (Real.rpow_nonneg (oscEigenvalue_pos α).le _)))
  -- the orbit part
  set v' : MultiIndex d → ℝ → Euc d → ℝ := fun α t x =>
    if r < t ∧ t ≤ b.T then gradComp a (propagatorW CC r t (generatorW CC t (oscTestFun b.m α))) x else 0
    with hv'
  have hv'smooth : ∀ α t, ContDiff ℝ (b.k : WithTop ℕ∞) (v' α t) ∧
      ∀ j ≤ b.k, ∀ x, ‖iteratedFDeriv ℝ j (v' α t) x‖ ≤ c α := by
    intro α t
    by_cases ht : r < t ∧ t ≤ b.T
    · have e : v' α t = fun x => gradComp a
          (propagatorW CC r t (generatorW CC t (oscTestFun b.m α))) x := by
        funext x; simp [hv', ht]
      rw [e]
      obtain ⟨h1, h2⟩ := hCo S N a r t hr.1 ht.1.le ht.2 α
      exact ⟨h1, fun j hj x => (h2 j hj x).trans (mul_le_mul_of_nonneg_right (le_max_right _ _)
        (Real.rpow_nonneg (oscEigenvalue_pos α).le _))⟩
    · have e : v' α t = fun _ => (0 : ℝ) := by funext x; simp [hv', ht]
      rw [e]
      exact ⟨contDiff_const, fun j hj x => by rw [s55f_iter_zero]; exact hc0 α⟩
  set Fv : ℝ → Euc d → OscDual d b.m := fun t x => ellVec (d := d) b.m (fun α => v' α t x) with hFv
  have hFsm : ∀ t, ContDiff ℝ (b.k : WithTop ℕ∞) (Fv t) ∧
      ∀ j ≤ b.k, ∀ x, ‖iteratedFDeriv ℝ j (Fv t) x‖ ≤ Bs := fun t =>
    s55f_ell_contDiff (E := Euc d) (m := b.m) (k := b.k) (fun α x => v' α t x)
      (fun α => (hv'smooth α t).1) c hcs (fun α j hj x => (hv'smooth α t).2 j hj x)
  have hv'meas : ∀ x α, AEStronglyMeasurable (fun t => v' α t x) μ := by
    intro x α
    have e : (fun t => v' α t x) = (Set.Ioc r b.T).indicator (fun t => gradComp a
        (propagatorW CC r t (generatorW CC t (oscTestFun b.m α))) x) := by
      funext t
      by_cases ht : r < t ∧ t ≤ b.T
      · simp [hv', ht, Set.indicator_of_mem (show t ∈ Set.Ioc r b.T from ht)]
      · simp [hv', ht, Set.indicator_of_notMem (show t ∉ Set.Ioc r b.T from ht)]
    rw [e, aestronglyMeasurable_indicator_iff measurableSet_Ioc]
    have hsub : Set.Ioc r b.T ⊆ Set.Icc (0 : ℝ) b.T := fun t ht => ⟨hr.1.trans ht.1.le, ht.2⟩
    have : μ.restrict (Set.Ioc r b.T) = volume.restrict (Set.Ioc r b.T) := by
      rw [hμ, Measure.restrict_restrict measurableSet_Ioc, Set.inter_eq_left.2 hsub]
    rw [this]
    exact hmeas N a r hr α x
  have hv'bd : ∀ x α t, |v' α t x| ≤ c α := by
    intro x α t
    have := (hv'smooth α t).2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hmeasF : ∀ x, AEStronglyMeasurable (fun t => Fv t x) μ := fun x =>
    s55f_aesm_ellVec (m := b.m) (fun α t => v' α t x) (hv'meas x) (fun t =>
      Summable.of_norm_bounded hcs fun α => by simpa [Real.norm_eq_abs] using hv'bd x α t)
  have hFb0 : ∀ t x, ‖Fv t x‖ ≤ Bs := fun t x => by
    have := (hFsm t).2 0 (Nat.zero_le _) x
    rwa [norm_iteratedFDeriv_zero] at this
  have hmem : ∀ x, MemLp (fun t => Fv t x) 2 μ := fun x =>
    s55f_memLp_of_bound μ (hmeasF x) (B := Bs) (fun t => hFb0 t x)
  obtain ⟨hWc, hWb⟩ := s55f_L2_contDiff μ hd1 b.k Fv Bs (fun t => (hFsm t).1)
    (fun t j hj x => (hFsm t).2 j hj x) hmeasF hmem
  -- identification
  have hid : ∀ x, gradFeature CC b.m b.T a r x =
      s55fΦ₁ b.m b.T (ellVec (d := d) b.m (fun α => gradComp a (oscTestFun b.m α) x)) +
        s55fΦ₂ b.m b.T ((hmem x).toLp (fun t => Fv t x)) := by
    intro x
    have hfF : (fun t => if r < t then ellVec (d := d) b.m (fun α => gradComp a
        (propagatorW CC r t (generatorW CC t (oscTestFun b.m α))) x) else 0) =ᵐ[μ]
        fun t => Fv t x := by
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun t ht => ?_)
      by_cases hrt : r < t
      · have hc : r < t ∧ t ≤ b.T := ⟨hrt, ht.2⟩
        simp only [hrt, if_true, hFv, hv', hc, and_self]
      · simp only [hrt, if_false, hFv, hv', false_and, if_false]
        exact (s55f_ellVec_zero b.m).symm
    have hmf := (hmem x).ae_eq hfF.symm
    rw [← s55f_mk_eq]
    unfold gradFeature orbitFeature
    dsimp only
    congr 1
    exact (dif_pos hmf).trans (MemLp.toLp_congr hmf (hmem x) hfF)
  have hfun : (fun x => gradFeature CC b.m b.T a r x) = fun x =>
      s55fΦ₁ b.m b.T (ellVec (d := d) b.m (fun α => gradComp a (oscTestFun b.m α) x)) +
        s55fΦ₂ b.m b.T ((hmem x).toLp (fun t => Fv t x)) := funext hid
  rw [hfun]
  refine ⟨((s55fΦ₁ b.m b.T).contDiff.comp hbase.1).add ((s55fΦ₂ b.m b.T).contDiff.comp hWc), ?_⟩
  intro j hj x
  have hjk : (j : WithTop ℕ∞) ≤ (b.k : WithTop ℕ∞) := by exact_mod_cast hj
  have hadd := iteratedFDeriv_add_apply (𝕜 := ℝ) (i := j)
    (((s55fΦ₁ b.m b.T).contDiff.comp hbase.1).of_le hjk).contDiffAt
    (((s55fΦ₂ b.m b.T).contDiff.comp hWc).of_le hjk).contDiffAt (x := x)
  have e1 := (s55fΦ₁ b.m b.T).norm_iteratedFDeriv_comp_left hbase.1.contDiffAt (x := x) (n := j) hjk
  have e2 := (s55fΦ₂ b.m b.T).norm_iteratedFDeriv_comp_left hWc.contDiffAt (x := x) (n := j) hjk
  show ‖iteratedFDeriv ℝ j ((s55fΦ₁ b.m b.T ∘ _) + (s55fΦ₂ b.m b.T ∘ _)) x‖ ≤ _
  rw [hadd]
  refine (norm_add_le _ _).trans ?_
  have hb1 := hbase.2 j hj x
  have hb2 := hWb j hj x
  have hn1 := s55fΦ₁_norm (d := d) b.m b.T
  have hn2 := s55fΦ₂_norm (d := d) b.m b.T
  have hdj : (d : ℝ) ^ j ≤ (d : ℝ) ^ b.k := pow_le_pow_right₀ hd1' hj
  have hX : 0 ≤ Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ) := by positivity
  calc _ ≤ ‖s55fΦ₁ b.m b.T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) b.m
          (fun α => gradComp a (oscTestFun b.m α) x)) x‖ +
        ‖s55fΦ₂ b.m b.T‖ * ‖iteratedFDeriv ℝ j (fun x => (hmem x).toLp (fun t => Fv t x)) x‖ :=
        add_le_add e1 e2
    _ ≤ 2 * Bs + (d : ℝ) ^ b.k * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
        have h1 : ‖s55fΦ₁ b.m b.T‖ * ‖iteratedFDeriv ℝ j (fun x => ellVec (d := d) b.m
            (fun α => gradComp a (oscTestFun b.m α) x)) x‖ ≤ 2 * Bs :=
          mul_le_mul hn1 hb1 (norm_nonneg _) (by norm_num)
        have h2 : ‖s55fΦ₂ b.m b.T‖ * ‖iteratedFDeriv ℝ j (fun x => (hmem x).toLp (fun t => Fv t x)) x‖ ≤
            (d : ℝ) ^ b.k * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) :=
          calc _ ≤ 1 * ((d : ℝ) ^ j * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ))) :=
                mul_le_mul hn2 hb2 (norm_nonneg _) (by norm_num)
            _ ≤ (d : ℝ) ^ b.k * (Bs * (μ Set.univ).toReal ^ (1 / 2 : ℝ)) := by
                rw [one_mul]; exact mul_le_mul_of_nonneg_right hdj hX
        linarith

end HRS.MS.Go
