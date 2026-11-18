import HRS.MS.S111K2B02
import HRS.MS.R2GenInitAux23
import HRS.MS.CovMeasTie

/-!
# S11.1 continuation (S11K3), B03 part A: qualitative window-orbit facts, the gradient Duhamel identity and the
pairings of the shifted window feature

From `S111k2WindowOrbitInput C m c0 r b` (all `t ≥ 0`, `Σ b² < ∞`, `c0 ≥ 0`) we derive the gradient bound `|∂_a U^{v,t} φ_α| ≤ b_α`,
the gradient Duhamel identity (differentiation of the value-level fundamental theorem of calculus under the integral sign),
`OscAdjointInput C m H` for every `H`, and the pairings `⟨Γ_{v,a}(x), y1(t,α)⟩`, `⟨Γ_{v,a}(x), y2(α)⟩` (finite combinations).
-/

set_option autoImplicit false
noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.S111K3

open HRS HRS.Whole HRS.MS.Go HRS.MS.CovMeas HRS.MS.S111K2 HRS.MS.R2WinErr HRS.MS.S52 HRS.MS.R2GenInit

variable {d : ℕ} {C : WholeCoeff d} {m c0 : ℝ} {r : ℕ} {b : MultiIndex d → ℝ}

lemma k3_base_bound (hW : S111k2WindowOrbitInput C m c0 r b) (α : MultiIndex d) (a : Fin d) (x : Euc d) :
    |gradComp a (oscTestFun m α) x| ≤ b α := by
  have hex := (hW.classical α 0 le_rfl).1
  have hp : propagatorW C 0 0 (oscTestFun m α) = oscTestFun m α := by
    unfold propagatorW; rw [dif_pos hex]; exact hex.choose_spec.terminal
  have h := (s104_gradComp_bound C (hW.nonneg α) (hW.grad α 0 le_rfl).1 (r := 0) ⟨le_rfl, le_rfl⟩ a).2
    0 (Nat.zero_le _) x
  rw [hp, norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  refine h.trans ?_
  simp

lemma k3_exp_le (hc0 : 0 ≤ c0) {t r' : ℝ} (hr' : r' ∈ Icc (0 : ℝ) t) : Real.exp (-c0 * (t - r')) ≤ 1 :=
  Real.exp_le_one_iff.2 (by nlinarith [hr'.2])

lemma k3_prop_bound (hW : S111k2WindowOrbitInput C m c0 r b) (hc0 : 0 ≤ c0) (α : MultiIndex d) {t r' : ℝ}
    (ht : 0 ≤ t) (hr' : r' ∈ Icc (0 : ℝ) t) (a : Fin d) (x : Euc d) :
    |gradComp a (propagatorW C r' t (oscTestFun m α)) x| ≤ b α := by
  have h := (s104_gradComp_bound C (hW.nonneg α) (hW.grad α t ht).1 hr' a).2 0 (Nat.zero_le _) x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  refine h.trans ?_
  have := k3_exp_le hc0 hr'
  nlinarith [hW.nonneg α]

lemma k3_gen_bound (hW : S111k2WindowOrbitInput C m c0 r b) (hc0 : 0 ≤ c0) (α : MultiIndex d) {t r' : ℝ}
    (ht : 0 ≤ t) (hr' : r' ∈ Icc (0 : ℝ) t) (a : Fin d) (x : Euc d) :
    |gradComp a (propagatorW C r' t (generatorW C t (oscTestFun m α))) x| ≤ b α := by
  have h := (s104_gradComp_bound C (hW.nonneg α) (hW.grad α t ht).2 hr' a).2 0 (Nat.zero_le _) x
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  refine h.trans ?_
  have := k3_exp_le hc0 hr'
  nlinarith [hW.nonneg α]

/-- Differentiability in `x` of the generator orbit. -/
lemma k3_gen_diff (hW : S111k2WindowOrbitInput C m c0 r b) (α : MultiIndex d) {v t : ℝ} (hv : 0 ≤ v) (hvt : v ≤ t) :
    Differentiable ℝ (propagatorW C v t (generatorW C t (oscTestFun m α))) := by
  have hex := (hW.classical α t (hv.trans hvt)).2
  have hp : propagatorW C v t (generatorW C t (oscTestFun m α)) = hex.choose v := by
    unfold propagatorW; rw [dif_pos hex]
  rw [hp]
  exact (hex.choose_spec.c2 v ⟨hv, hvt⟩).differentiable (by norm_num)

lemma k3_prop_diff (hW : S111k2WindowOrbitInput C m c0 r b) (α : MultiIndex d) {v t : ℝ} (hv : 0 ≤ v) (hvt : v ≤ t) :
    Differentiable ℝ (propagatorW C v t (oscTestFun m α)) := by
  have hex := (hW.classical α t (hv.trans hvt)).1
  have hp : propagatorW C v t (oscTestFun m α) = hex.choose v := by
    unfold propagatorW; rw [dif_pos hex]
  rw [hp]
  exact (hex.choose_spec.c2 v ⟨hv, hvt⟩).differentiable (by norm_num)

lemma k3_prop_terminal (hW : S111k2WindowOrbitInput C m c0 r b) (α : MultiIndex d) {v : ℝ} (hv : 0 ≤ v) :
    propagatorW C v v (oscTestFun m α) = oscTestFun m α := by
  have hex := (hW.classical α v hv).1
  unfold propagatorW; rw [dif_pos hex]; exact hex.choose_spec.terminal

/-- Measurability in the time variable of the generator orbit (values). -/
lemma k3_gen_meas_val (hW : S111k2WindowOrbitInput C m c0 r b) (α : MultiIndex d) {v : ℝ} (hv : 0 ≤ v) (y : Euc d)
    (t : ℝ) :
    AEStronglyMeasurable (fun s => propagatorW C v s (generatorW C s (oscTestFun m α)) y)
      (volume.restrict (Icc v t)) := by
  classical
  set D : ℝ → ℝ := fun s => derivWithin (fun s' => propagatorW C v s' (oscTestFun m α) y) (Ici s) s with hD
  have hDm : Measurable D := measurable_derivWithin_Ici _
  refine hDm.aestronglyMeasurable.congr ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
  have := (hW.terminal_derivative α v s hv hs.1 y).mono (Ici_subset_Ici.2 hs.1)
  exact this.derivWithin (uniqueDiffWithinAt_Ici s)

/-- Measurability in the time variable of the gradient of the generator orbit. -/
lemma k3_gen_meas_grad (hW : S111k2WindowOrbitInput C m c0 r b) (α : MultiIndex d) {v : ℝ} (hv : 0 ≤ v) (a : Fin d)
    (y : Euc d) (t : ℝ) :
    AEStronglyMeasurable (fun s => gradComp a (propagatorW C v s (generatorW C s (oscTestFun m α))) y)
      (volume.restrict (Icc v t)) := by
  classical
  have h := s111k2_hmeasU (C := C) (oscTestFun m α) t 0 v hv a y (fun s hs => (hW.classical α s hs).2)
    (fun s hsv z => hW.terminal_derivative α v s hv hsv z)
  have h' : AEStronglyMeasurable (fun u : ℝ => if v < 0 + u then
      gradComp a (propagatorW C v (0 + u) (generatorW C (0 + u) (oscTestFun m α))) y else 0)
      (volume.restrict (Icc v t)) := by
    exact h.mono_measure (Measure.restrict_mono (Icc_subset_Icc_left hv) le_rfl)
  refine h'.congr ?_
  have hae : ∀ᵐ s ∂(volume.restrict (Icc v t)), s ≠ v := by
    have : volume ({v} : Set ℝ) = 0 := Real.volume_singleton
    exact ae_restrict_of_ae ((measure_eq_zero_iff_ae_notMem.1 this).mono fun s hs => by simpa using hs)
  filter_upwards [hae, ae_restrict_mem measurableSet_Icc] with s hsv hs
  have e : v < s := lt_of_le_of_ne hs.1 (Ne.symm hsv)
  simp only [zero_add, if_pos e]


lemma k3_G_eq_dt (hW : S111k2WindowOrbitInput C m c0 r b) (α : MultiIndex d) {v s T' : ℝ} (hv : 0 ≤ v) (hvs : v ≤ s)
    (hsT : s ≤ T') (hvT : v < T') (y : Euc d) :
    s101Dt C m T' v s α y = propagatorW C v s (generatorW C s (oscTestFun m α)) y := by
  unfold s101Dt
  have h := (hW.terminal_derivative α v s hv hvs y).mono (Icc_subset_Ici_self : Icc v T' ⊆ Ici v)
  exact h.derivWithin (uniqueDiffOn_Icc hvT s ⟨hvs, hsT⟩)

lemma k3_G_bdd (hW : S111k2WindowOrbitInput C m c0 r b) (α : MultiIndex d) (hd : 1 ≤ d) {v t : ℝ} (hv : 0 ≤ v)
    (hvt : v ≤ t) :
    ∃ c : ℝ, ∀ s ∈ Icc v t, ∀ y, |propagatorW C v s (generatorW C s (oscTestFun m α)) y| ≤ c := by
  obtain ⟨c, hD⟩ := s101_data_of_horb hd (hW.orbit (t + 1) (by linarith))
  refine ⟨c α, fun s hs y => ?_⟩
  have h := hD.bddD α v ⟨hv, by linarith [hs.2, hvt]⟩ s ⟨hs.1, by linarith [hs.2]⟩ 0 (Nat.zero_le _) y
  rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h
  rwa [k3_G_eq_dt hW α hv hs.1 (by linarith [hs.2]) (by linarith) y] at h

/-- Value-level fundamental theorem of calculus for the orbit. -/
lemma k3_ftc_val (hW : S111k2WindowOrbitInput C m c0 r b) (α : MultiIndex d) (hd : 1 ≤ d) {v t : ℝ} (hv : 0 ≤ v)
    (hvt : v ≤ t) (y : Euc d) :
    propagatorW C v t (oscTestFun m α) y - oscTestFun m α y =
      ∫ s in Icc v t, propagatorW C v s (generatorW C s (oscTestFun m α)) y := by
  set F : ℝ → ℝ := fun s => propagatorW C v s (oscTestFun m α) y with hF
  set G : ℝ → ℝ := fun s => propagatorW C v s (generatorW C s (oscTestFun m α)) y with hG
  have hcont : ContinuousOn F (Icc v t) := fun s hs =>
    ((hW.terminal_derivative α v s hv hs.1 y).continuousWithinAt).mono Icc_subset_Ici_self
  have hder : ∀ s ∈ Ioo v t, HasDerivWithinAt F (G s) (Ioi s) s := by
    intro s hs
    exact (hW.terminal_derivative α v s hv hs.1.le y).mono (fun z hz => le_of_lt (lt_trans hs.1 hz))
  obtain ⟨c, hc⟩ := k3_G_bdd hW α hd hv hvt
  have hint : IntervalIntegrable G volume v t := by
    refine (intervalIntegrable_iff_integrableOn_Ioc_of_le hvt).2 ?_
    have hIcc : IntegrableOn G (Icc v t) := by
      refine Integrable.of_bound (k3_gen_meas_val hW α hv y t) c ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
      rw [Real.norm_eq_abs]; exact hc s hs y
    exact hIcc.mono_set Ioc_subset_Icc_self
  have := intervalIntegral.integral_eq_sub_of_hasDeriv_right_of_le hvt hcont hder hint
  rw [intervalIntegral.integral_of_le hvt, ← integral_Icc_eq_integral_Ioc] at this
  have e0 : F v = oscTestFun m α y := by simp only [hF]; rw [k3_prop_terminal hW α hv]
  rw [this, e0]

lemma k3_line_deriv {g : Euc d → ℝ} (hg : Differentiable ℝ g) (a : Fin d) (x : Euc d) (h : ℝ) :
    HasDerivAt (fun h' : ℝ => g (x + h' • EuclideanSpace.single a (1 : ℝ)))
      (gradComp a g (x + h • EuclideanSpace.single a (1 : ℝ))) h := by
  have h1 : HasDerivAt (fun h' : ℝ => x + h' • EuclideanSpace.single a (1 : ℝ)) (EuclideanSpace.single a (1 : ℝ)) h := by
    simpa using ((hasDerivAt_id h).smul_const (EuclideanSpace.single a (1 : ℝ))).const_add x
  have h2 := (hg (x + h • EuclideanSpace.single a (1 : ℝ))).hasFDerivAt.comp_hasDerivAt h h1
  rw [s111k2_gradComp_eq_fderiv]
  exact h2

/-- **Gradient Duhamel identity** (the `duhamel` clause of `OscAdjointInput`). -/
theorem k3_duhamel (hW : S111k2WindowOrbitInput C m c0 r b) (hc0 : 0 ≤ c0) {v t : ℝ} (hv : 0 ≤ v) (hvt : v ≤ t)
    (α : MultiIndex d) (a : Fin d) (x : Euc d) :
    IntegrableOn (fun s => gradComp a (propagatorW C v s (generatorW C s (oscTestFun m α))) x) (Icc v t) ∧
    gradComp a (propagatorW C v t (oscTestFun m α)) x - gradComp a (oscTestFun m α) x =
      ∫ s in Icc v t, gradComp a (propagatorW C v s (generatorW C s (oscTestFun m α))) x := by
  have hd : 1 ≤ d := a.pos
  set e : Euc d := EuclideanSpace.single a (1 : ℝ) with he
  set μ : Measure ℝ := volume.restrict (Icc v t) with hμ
  obtain ⟨c, hc⟩ := k3_G_bdd hW α hd hv hvt
  have hφd : Differentiable ℝ (oscTestFun m α) := by
    have := k3_prop_diff hW α hv le_rfl
    rwa [k3_prop_terminal hW α hv] at this
  have hΦ : ∀ h : ℝ, propagatorW C v t (oscTestFun m α) (x + h • e) - oscTestFun m α (x + h • e) =
      ∫ s, propagatorW C v s (generatorW C s (oscTestFun m α)) (x + h • e) ∂μ := fun h =>
    k3_ftc_val hW α hd hv hvt (x + h • e)
  have hΦd : HasDerivAt (fun h : ℝ => propagatorW C v t (oscTestFun m α) (x + h • e) - oscTestFun m α (x + h • e))
      (gradComp a (propagatorW C v t (oscTestFun m α)) x - gradComp a (oscTestFun m α) x) 0 := by
    have h1 := k3_line_deriv (k3_prop_diff hW α hv hvt) a x 0
    have h2 := k3_line_deriv hφd a x 0
    simp only [zero_smul, add_zero] at h1 h2
    exact h1.sub h2
  have hmain := hasDerivAt_integral_of_dominated_loc_of_deriv_le (μ := μ) (x₀ := (0 : ℝ))
    (F := fun (h : ℝ) (s : ℝ) => propagatorW C v s (generatorW C s (oscTestFun m α)) (x + h • e))
    (F' := fun (h : ℝ) (s : ℝ) => gradComp a (propagatorW C v s (generatorW C s (oscTestFun m α))) (x + h • e))
    (bound := fun _ => b α) (s := Metric.ball (0 : ℝ) 1) (Metric.ball_mem_nhds 0 one_pos)
    (Eventually.of_forall fun h => k3_gen_meas_val hW α hv _ t)
    (by
      refine Integrable.of_bound (k3_gen_meas_val hW α hv _ t) c ?_
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs => ?_)
      rw [Real.norm_eq_abs]; exact hc s hs _)
    (k3_gen_meas_grad hW α hv a _ t)
    (by
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs h _ => ?_)
      rw [Real.norm_eq_abs]
      exact k3_gen_bound hW hc0 α (hv.trans hs.1) ⟨hv, hs.1⟩ a _)
    (integrable_const _)
    (by
      refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun s hs h _ => ?_)
      exact k3_line_deriv (k3_gen_diff hW α hv hs.1) a x h)
  obtain ⟨hint, hder⟩ := hmain
  simp only [zero_smul, add_zero] at hint hder
  refine ⟨hint, ?_⟩
  have hfun : (fun h : ℝ => propagatorW C v t (oscTestFun m α) (x + h • e) - oscTestFun m α (x + h • e)) =
      fun h : ℝ => ∫ s, propagatorW C v s (generatorW C s (oscTestFun m α)) (x + h • e) ∂μ := funext hΦ
  rw [hfun] at hΦd
  exact hΦd.unique hder


/-! ### The `OscAdjointInput` and the pairings of the shifted window feature -/

lemma k3_memLp_win (hW : S111k2WindowOrbitInput C m c0 r b) (hbS : Summable fun α => b α ^ 2) (hc0 : 0 ≤ c0)
    {r' s L : ℝ} (hr' : 0 ≤ r') (a : Fin d) (x : Euc d) :
    MemLp (fun w : ℝ => if r' < s + w then ellVec (d := d) m (fun α => gradComp a (propagatorW C r' (s + w)
      (generatorW C (s + w) (oscTestFun m α))) x) else 0) 2 (volume.restrict (Icc (0 : ℝ) L)) := by
  classical
  set v' : MultiIndex d → ℝ → ℝ := fun α w => if r' < s + w then gradComp a (propagatorW C r' (s + w)
      (generatorW C (s + w) (oscTestFun m α))) x else 0 with hv'
  have hb : ∀ α w, |v' α w| ≤ b α := by
    intro α w
    by_cases h : r' < s + w
    · simp only [hv', if_pos h]
      exact k3_gen_bound hW hc0 α (by linarith) ⟨hr', h.le⟩ a x
    · simp only [hv', if_neg h]; simpa using hW.nonneg α
  have hsum : ∀ w, Summable fun α => v' α w ^ 2 := fun w =>
    Summable.of_nonneg_of_le (fun α => sq_nonneg _) (fun α => by
      have := abs_le.1 (hb α w)
      exact sq_le_sq' this.1 this.2) hbS
  have hae : ∀ α, AEStronglyMeasurable (v' α) (volume.restrict (Icc (0 : ℝ) L)) := fun α =>
    s111k2_hmeasU (C := C) (oscTestFun m α) L s r' hr' a x (fun t ht => (hW.classical α t ht).2)
      (fun t htr z => hW.terminal_derivative α r' t hr' htr z)
  have hfun : (fun w : ℝ => if r' < s + w then ellVec (d := d) m (fun α => gradComp a (propagatorW C r' (s + w)
      (generatorW C (s + w) (oscTestFun m α))) x) else 0) = fun w => ellVec (d := d) m (fun α => v' α w) := by
    funext w
    by_cases h : r' < s + w
    · simp only [hv', if_pos h]
    · simp only [hv', if_neg h]; exact (s55f_ellVec_zero m).symm
  rw [hfun]
  refine MemLp.of_bound (s111k2_aesm_ellVec2 (m := m) v' hae hsum) (Real.sqrt (∑' α, b α ^ 2))
    (Eventually.of_forall fun w => ?_)
  exact s101_norm_ellVec_le hbS fun α => hb α w

lemma k3_oscAdjoint (hW : S111k2WindowOrbitInput C m c0 r b) (hbS : Summable fun α => b α ^ 2) (hc0 : 0 ≤ c0)
    (H : ℝ) : OscAdjointInput C m H where
  duhamel := fun v t hv hvt _ α a x => k3_duhamel hW hc0 hv hvt α a x
  feature := fun a v hv x => by
    refine ⟨s101_memℓp_of_bound hbS fun α => k3_base_bound hW α a x, fun t ht => ?_, ?_⟩
    · exact s101_memℓp_of_bound hbS fun α => k3_gen_bound hW hc0 α (hv.1.trans ht.1.le) ⟨hv.1, ht.1.le⟩ a x
    · simpa only [zero_add] using k3_memLp_win (C := C) (m := m) hW hbS hc0 (r' := v) (s := 0) (L := H) hv.1 a x

theorem k3_pair_y1 (hW : S111k2WindowOrbitInput C m c0 r b) (hbS : Summable fun α => b α ^ 2) (hc0 : 0 ≤ c0)
    {T u v : ℝ} (hu : 0 ≤ u) (hv0 : 0 ≤ v) (hvH : v ≤ u + T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : Fin d)
    (x : Euc d) (α : MultiIndex d) :
    inner ℝ (r2WindowFeature C m T (gradComp a) u v x) (s52y1 m T t α) =
      if v ≤ u + t then gradComp a (propagatorW C v (u + t) (oscTestFun m α)) x
      else gradComp a (oscTestFun m α) x := by
  refine s105_pair_y1 C (k3_oscAdjoint hW hbS hc0 (u + T)) hu hv0 hvH ht a x ?_ ?_ ?_ α
  · exact s101_memℓp_of_bound hbS fun α => k3_prop_bound hW hc0 α (hv0.trans (le_max_right _ _))
      ⟨hv0, le_max_right _ _⟩ a x
  · intro t' ht' hlt
    exact s101_memℓp_of_bound hbS fun α => k3_gen_bound hW hc0 α (by linarith [ht'.1]) ⟨hv0, hlt.le⟩ a x
  · exact k3_memLp_win hW hbS hc0 hv0 a x

theorem k3_pair_y2 (hW : S111k2WindowOrbitInput C m c0 r b) (hbS : Summable fun α => b α ^ 2) (hc0 : 0 ≤ c0)
    {T u v : ℝ} (hv0 : 0 ≤ v) (a : Fin d) (x : Euc d) (α : MultiIndex d) :
    inner ℝ (r2WindowFeature C m T (gradComp a) u v x) (s52y2 m T α) =
      if u ≤ v then gradComp a (oscTestFun m α) x else 0 := by
  refine s105_pair_y2 C m T u v a x ?_ ?_ (k3_memLp_win hW hbS hc0 hv0 a x) α
  · exact s101_memℓp_of_bound hbS fun α => k3_prop_bound hW hc0 α (hv0.trans (le_max_right _ _))
      ⟨hv0, le_max_right _ _⟩ a x
  · refine s101_memℓp_of_bound hbS fun α => ?_
    by_cases h : u ≤ v
    · simp only [if_pos h]; exact k3_base_bound hW α a x
    · simp only [if_neg h]; simpa using hW.nonneg α


/-! ### Finite combinations -/

/-- `Σ c_α y1(t,α)`. -/
def k3y1c (m T t : ℝ) (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) : KSpace d m T :=
  ∑ α ∈ S, c α • s52y1 m T t α

/-- `Σ c_α y2(α)`. -/
def k3y2c (m T : ℝ) (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) : KSpace d m T :=
  ∑ α ∈ S, c α • s52y2 m T α

/-- The finite combination `Σ c_α φ_α`. -/
def k3combo (m : ℝ) (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) : Euc d → ℝ :=
  fun y => ∑ α ∈ S, c α * oscTestFun m α y

lemma k3_gradComp_sum (a : Fin d) (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ)
    (f : MultiIndex d → Euc d → ℝ) (hf : ∀ α ∈ S, Differentiable ℝ (f α)) (x : Euc d) :
    gradComp a (fun y => ∑ α ∈ S, c α * f α y) x = ∑ α ∈ S, c α * gradComp a (f α) x := by
  rw [s111k2_gradComp_eq_fderiv, fderiv_fun_sum (fun α hα => ((hf α hα).differentiableAt).const_mul (c α))]
  simp only [ContinuousLinearMap.sum_apply]
  refine Finset.sum_congr rfl fun α hα => ?_
  rw [fderiv_const_mul (hf α hα).differentiableAt, s111k2_gradComp_eq_fderiv]
  simp

lemma k3_prop_combo (hW : S111k2WindowOrbitInput C m c0 r b) {v t : ℝ} (hv : 0 ≤ v) (hvt : v ≤ t)
    (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    propagatorW C v t (k3combo m S c) = fun y => ∑ α ∈ S, c α * propagatorW C v t (oscTestFun m α) y :=
  s101_prop_comb (C := C) (m := m) (T := t)
    (fun u t' hu hut _ φ ψ cc hφ hψ => hW.linear u t' hu hut φ ψ cc hφ hψ) hv hvt le_rfl S c

lemma k3_combo_diff (hW : S111k2WindowOrbitInput C m c0 r b) {v t : ℝ} (hv : 0 ≤ v) (hvt : v ≤ t)
    (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) : Differentiable ℝ (propagatorW C v t (k3combo m S c)) := by
  rw [k3_prop_combo hW hv hvt]
  exact Differentiable.fun_sum fun α hα => (k3_prop_diff hW α hv hvt).const_mul (c α)

lemma k3_combo_base_diff (hW : S111k2WindowOrbitInput C m c0 r b) (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    Differentiable ℝ (k3combo m S c) := by
  unfold k3combo
  refine Differentiable.fun_sum fun α hα => ?_
  have := k3_prop_diff hW α (le_refl (0 : ℝ)) le_rfl
  rw [k3_prop_terminal hW α le_rfl] at this
  exact this.const_mul (c α)

theorem k3_pair_y1c (hW : S111k2WindowOrbitInput C m c0 r b) (hbS : Summable fun α => b α ^ 2) (hc0 : 0 ≤ c0)
    {T u v : ℝ} (hu : 0 ≤ u) (hv0 : 0 ≤ v) (hvH : v ≤ u + T) {t : ℝ} (ht : t ∈ Icc (0 : ℝ) T) (a : Fin d)
    (x : Euc d) (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    inner ℝ (r2WindowFeature C m T (gradComp a) u v x) (k3y1c m T t S c) =
      if v ≤ u + t then gradComp a (propagatorW C v (u + t) (k3combo m S c)) x
      else gradComp a (k3combo m S c) x := by
  unfold k3y1c
  rw [inner_sum]
  have h1 : ∀ α ∈ S, inner ℝ (r2WindowFeature C m T (gradComp a) u v x) (c α • s52y1 m T t α) =
      c α * (if v ≤ u + t then gradComp a (propagatorW C v (u + t) (oscTestFun m α)) x
        else gradComp a (oscTestFun m α) x) := by
    intro α _
    rw [inner_smul_right, k3_pair_y1 hW hbS hc0 hu hv0 hvH ht a x α]
  rw [Finset.sum_congr rfl h1]
  by_cases h : v ≤ u + t
  · simp only [if_pos h]
    rw [k3_prop_combo hW hv0 h S c, k3_gradComp_sum a S c _ (fun α _ => k3_prop_diff hW α hv0 h) x]
  · simp only [if_neg h]
    have e : k3combo m S c = fun y => ∑ α ∈ S, c α * oscTestFun m α y := rfl
    rw [e, k3_gradComp_sum a S c _ (fun α _ => by
      have := k3_prop_diff hW α (le_refl (0 : ℝ)) le_rfl
      rwa [k3_prop_terminal hW α le_rfl] at this) x]

theorem k3_pair_y2c (hW : S111k2WindowOrbitInput C m c0 r b) (hbS : Summable fun α => b α ^ 2) (hc0 : 0 ≤ c0)
    {T u v : ℝ} (hv0 : 0 ≤ v) (a : Fin d) (x : Euc d) (S : Finset (MultiIndex d)) (c : MultiIndex d → ℝ) :
    inner ℝ (r2WindowFeature C m T (gradComp a) u v x) (k3y2c m T S c) =
      if u ≤ v then gradComp a (k3combo m S c) x else 0 := by
  unfold k3y2c
  rw [inner_sum]
  have h1 : ∀ α ∈ S, inner ℝ (r2WindowFeature C m T (gradComp a) u v x) (c α • s52y2 m T α) =
      c α * (if u ≤ v then gradComp a (oscTestFun m α) x else 0) := by
    intro α _
    rw [inner_smul_right, k3_pair_y2 hW hbS hc0 hv0 a x α]
  rw [Finset.sum_congr rfl h1]
  by_cases h : u ≤ v
  · simp only [if_pos h]
    have e : k3combo m S c = fun y => ∑ α ∈ S, c α * oscTestFun m α y := rfl
    rw [e, k3_gradComp_sum a S c _ (fun α _ => by
      have := k3_prop_diff hW α (le_refl (0 : ℝ)) le_rfl
      rwa [k3_prop_terminal hW α le_rfl] at this) x]
  · simp only [if_neg h]; simp

end HRS.MS.S111K3
