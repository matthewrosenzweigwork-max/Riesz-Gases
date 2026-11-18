import HRS.MS.MovAdjAux26
import HRS.MS.GradSmTie
import HRS.MS.Mov63Tie
import HRS.MS.MovOpAux5
import HRS.MS.MovLinTie
import HRS.MS.MovOscAux5
import HRS.MS.S67NlBD00
import HRS.MS.S67NlBD33

/-!
# S6.7 nonlinear breakdown, packet 34: off-diagonal membership and measurable lift

`s67bd_lift_measurable`.  Part 1: `Σ^p → Σ^q` for `T†(t)` with `0 < t ≤ T - r`, from the short-time
all-level interface `HsOK` (gain on the first step, level preservation after) and the semigroup law
`T†(t) = T†(1) T†(t - 1)`.  Part 2: the Hermite coefficients of `T†(v - r) h_v` equal
`⟨T(v - r) P h_α, h_v⟩` (`P` the orthogonal projection onto `L²_0`), hence are continuous on
`(r, T]`; the finite-truncation argument of packet 33 gives a.e. strong measurability.
-/

set_option autoImplicit false
set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.BreakdownS67

open HRS HRS.Whole HRS.MS.MovLin HRS.MS.MovOsc HRS.MS.MovAdj
open HRS.MS.Mov63 HRS.MS.MovForce HRS.MS.MovC2
open HRS.MS.PoisFlow HRS.MS.PoisSg HRS.MS.PoisKolm HRS.MS.PoisHigh

variable {d : ℕ} {s β q : ℝ} {ρ₀ : Euc d → ℝ}

def s67bd_lift (H : Mov2dTh d s β q ρ₀) (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x))
    (qlev r : ℝ) (h : ℝ → MovL2Zero ρ₀) (v : ℝ) : OscSpace d qlev :=
  if r < v then OscSpace.ofFun qlev (movFun (s67bd_Tdag H g hg (v - r) (h v))) else 0

/-- Strong measurability of `v ↦ ofFun m (k v)` from continuous Hermite coefficients and membership. -/
theorem s67bd_measurable_of_coeff {S : Set ℝ} (hS : MeasurableSet S) (m : ℝ)
    (k : ℝ → Euc d → ℝ)
    (hcoef : ∀ α : MultiIndex d, ContinuousOn (fun v => hermiteCoeff (k v) α) S)
    (hmem : ∀ v ∈ S, MemOsc m (k v)) :
    AEStronglyMeasurable (fun v => OscSpace.ofFun m (k v)) (volume.restrict S) := by
  classical
  set e : MultiIndex d → lp (fun _ : MultiIndex d => ℝ) 2 := fun α => lp.single 2 α (1 : ℝ)
    with he
  set F : ℕ → ℝ → lp (fun _ : MultiIndex d => ℝ) 2 := fun n v =>
    ∑ α ∈ mova2_S d n, (oscEigenvalue d α ^ (m / 2) * hermiteCoeff (k v) α) • e α
    with hF
  have hFm : ∀ n, AEStronglyMeasurable (F n) (volume.restrict S) := by
    intro n
    refine Finset.aestronglyMeasurable_fun_sum _ fun α _ => ?_
    exact ((continuousOn_const.mul (hcoef α)).aestronglyMeasurable hS).smul_const (e α)
  have hlim : ∀ᵐ v ∂(volume.restrict S),
      Tendsto (fun n => F n v) atTop (𝓝 (OscSpace.ofFun m (k v) :
        lp (fun _ : MultiIndex d => ℝ) 2)) := by
    refine (ae_restrict_iff' hS).2 (Eventually.of_forall fun v hv => ?_)
    have hmv := hmem v hv
    set f : lp (fun _ : MultiIndex d => ℝ) 2 := (OscSpace.ofFun m (k v) :
      lp (fun _ : MultiIndex d => ℝ) 2) with hf
    have hsum := lp.hasSum_single (E := fun _ : MultiIndex d => ℝ) (p := 2) ENNReal.ofNat_ne_top f
    have hT' := hsum.comp (tendsto_atTop_finset_of_monotone (mova2_S_mono (d := d)) mova2_S_exh)
    refine hT'.congr fun n => ?_
    simp only [Function.comp_apply, hF]
    refine Finset.sum_congr rfl fun α _ => ?_
    have hfα : f α = oscEigenvalue d α ^ (m / 2) * hermiteCoeff (k v) α :=
      OscSpace.coord_ofFun_eq hmv α
    rw [hfα, he]
    simp only
    rw [← lp.single_smul (𝕜 := ℝ), smul_eq_mul, mul_one]
  exact aestronglyMeasurable_of_tendsto_ae atTop hFm hlim

theorem s67bd_coeff_eq_inner (u : MovL2Zero ρ₀) (α : MultiIndex d) :
    hermiteCoeff (movFun u) α = inner ℝ (hermiteLpD α) (u : Lp ℝ 2 (volume : Measure (Euc d))) := by
  have hmem : MemLp (movFun u) 2 (volume : Measure (Euc d)) :=
    Lp.memLp (u : Lp ℝ 2 (volume : Measure (Euc d)))
  have := OscSpace.inner_hermiteLpD_toLp (movFun u) hmem α
  have h2 : hmem.toLp (movFun u) = (u : Lp ℝ 2 (volume : Measure (Euc d))) :=
    Lp.toLp_coeFn _ hmem
  rw [← this, h2]

/-- The Hermite coefficient of `T†(t) w` is the pairing of `T(t) P h_α` with `w`. -/
theorem s67bd_coeff_Tdag (H : Mov2dTh d s β q ρ₀) (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x)) (t : ℝ) (w : MovL2Zero ρ₀)
    (α : MultiIndex d) :
    hermiteCoeff (movFun (s67bd_Tdag H g hg t w)) α =
      inner ℝ (mov2d_T H g hg t ((MovL2Zero ρ₀).orthogonalProjectionOnto (hermiteLpD α))) w := by
  rw [s67bd_coeff_eq_inner]
  have h1 := Submodule.inner_orthogonalProjectionOnto_eq_of_mem_right
    (K := MovL2Zero ρ₀) (s67bd_Tdag H g hg t w) (hermiteLpD α)
  rw [← h1]
  unfold s67bd_Tdag
  rw [ContinuousLinearMap.adjoint_inner_right]

/-- The adjoint semigroup law `T†(t) = T†(1) T†(t - 1)` for `t ≥ 1`. -/
theorem s67bd_Tdag_law (H : Mov2dTh d s β q ρ₀) (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x))
    (hsemi : MovIsSemigroup d s β ρ₀ (mov2d_T H g hg)) (t : ℝ) (ht : 1 ≤ t)
    (v : MovL2Zero ρ₀) :
    s67bd_Tdag H g hg t v = s67bd_Tdag H g hg 1 (s67bd_Tdag H g hg (t - 1) v) := by
  have h := hsemi.add (t - 1) 1 (by linarith) zero_le_one
  rw [sub_add_cancel] at h
  have e : mov2d_T H g hg t = (mov2d_T H g hg (t - 1)).comp (mov2d_T H g hg 1) := h
  have e2 : s67bd_Tdag H g hg t =
      (s67bd_Tdag H g hg 1).comp (s67bd_Tdag H g hg (t - 1)) := by
    unfold s67bd_Tdag
    rw [e]
    exact ContinuousLinearMap.adjoint_comp _ _
  rw [e2]
  rfl

/-- Gain `Σ^p → Σ^q` for `T†(t)`, `0 < t ≤ m + 1`, from the short-time interface and the semigroup law. -/
theorem s67bd_gain_mem (H : Mov2dTh d s β q ρ₀) (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x)) (p qlev : ℝ) (hp : 0 ≤ p)
    (hpq : p ≤ qlev) :
    ∀ m : ℕ, ∀ t ∈ Ioc (0 : ℝ) ((m : ℝ) + 1), ∀ v : MovL2Zero ρ₀, MemOsc p (movFun v) →
      MemOsc qlev (movFun (s67bd_Tdag H g hg t v)) := by
  obtain ⟨hsemi, -, hOK, -⟩ := s67bd_semigroup_data H g hg
  obtain ⟨C1, -, hC1⟩ := hOK p qlev hp hpq
  obtain ⟨C2, -, hC2⟩ := hOK qlev qlev (hp.trans hpq) le_rfl
  have hshort : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ v : MovL2Zero ρ₀, MemOsc p (movFun v) →
      MemOsc qlev (movFun (s67bd_Tdag H g hg t v)) := fun t ht v hv => (hC1 t ht v hv).1
  have hpres : ∀ t ∈ Ioc (0 : ℝ) 1, ∀ v : MovL2Zero ρ₀, MemOsc qlev (movFun v) →
      MemOsc qlev (movFun (s67bd_Tdag H g hg t v)) := fun t ht v hv => (hC2 t ht v hv).1
  have hlaw : ∀ t : ℝ, 1 ≤ t → ∀ v : MovL2Zero ρ₀,
      s67bd_Tdag H g hg t v = s67bd_Tdag H g hg 1 (s67bd_Tdag H g hg (t - 1) v) :=
    fun t ht v => s67bd_Tdag_law H g hg hsemi t ht v
  intro m
  induction m with
  | zero =>
    intro t ht v hv
    exact hshort t (by simpa using ht) v hv
  | succ m ih =>
    intro t ht v hv
    by_cases h1 : t ≤ 1
    · exact hshort t ⟨ht.1, h1⟩ v hv
    · replace h1 := not_le.1 h1
      rw [hlaw t h1.le v]
      refine hpres 1 ⟨one_pos, le_rfl⟩ _ (ih (t - 1) ⟨by linarith, ?_⟩ v hv)
      have := ht.2
      push_cast at this
      linarith

theorem s67bd_lift_measurable (H : Mov2dTh d s β q ρ₀)
    (g : SchwartzMap (Euc d) ℝ)
    (hg : (⇑g : Euc d → ℝ) = fun x => Real.sqrt (ρ₀ x))
    (p qlev T : ℝ) (hp : 0 ≤ p) (hpq : p ≤ qlev) (hgain : qlev - p < 2)
    (hT : 0 ≤ T) (h : ℝ → MovL2Zero ρ₀) (hc : ContinuousOn h (Icc (0 : ℝ) T))
    (hm : ∀ v ∈ Icc (0 : ℝ) T, MemOsc p (movFun (h v)))
    (r : ℝ) (hr : r ∈ Icc (0 : ℝ) T) :
    (∀ v ∈ Ioc r T, MemOsc qlev (movFun (s67bd_Tdag H g hg (v - r) (h v)))) ∧
    AEStronglyMeasurable (s67bd_lift H g hg qlev r h) (volume.restrict (Icc r T)) := by
  have hmem : ∀ v ∈ Ioc r T, MemOsc qlev (movFun (s67bd_Tdag H g hg (v - r) (h v))) := by
    intro v hv
    refine s67bd_gain_mem H g hg p qlev hp hpq ⌈T⌉₊ (v - r) ⟨by linarith [hv.1], ?_⟩ (h v)
      (hm v ⟨hr.1.trans hv.1.le, hv.2⟩)
    have h1 : v - r ≤ T := by linarith [hv.2, hr.1]
    have h2 : T ≤ (⌈T⌉₊ : ℝ) := Nat.le_ceil T
    linarith
  refine ⟨hmem, ?_⟩
  obtain ⟨hsemi, -, -, -⟩ := s67bd_semigroup_data H g hg
  -- continuity of the Hermite coefficients on `(r, T]`
  have hcoef : ∀ α : MultiIndex d, ContinuousOn
      (fun v => hermiteCoeff (movFun (s67bd_Tdag H g hg (v - r) (h v))) α) (Ioc r T) := by
    intro α
    simp_rw [s67bd_coeff_Tdag]
    set e : MovL2Zero ρ₀ := (MovL2Zero ρ₀).orthogonalProjectionOnto (hermiteLpD α) with he
    have h1 : ContinuousOn (fun v : ℝ => mov2d_T H g hg (v - r) e) (Ioc r T) := by
      refine (hsemi.cont e).comp (continuousOn_id.sub continuousOn_const) ?_
      intro v hv
      simp only [mem_Ici, sub_nonneg]
      exact hv.1.le
    have h2 : ContinuousOn h (Ioc r T) :=
      hc.mono fun v hv => ⟨hr.1.trans hv.1.le, hv.2⟩
    exact h1.inner h2
  have hmeas := s67bd_measurable_of_coeff (S := Ioc r T) measurableSet_Ioc qlev
    (fun v => movFun (s67bd_Tdag H g hg (v - r) (h v))) hcoef hmem
  rw [← Measure.restrict_congr_set Ioc_ae_eq_Icc]
  refine hmeas.congr ?_
  refine (ae_restrict_iff' measurableSet_Ioc).2 (Eventually.of_forall fun v hv => ?_)
  unfold s67bd_lift
  simp only [hv.1, ↓reduceIte]

end HRS.MS.BreakdownS67
