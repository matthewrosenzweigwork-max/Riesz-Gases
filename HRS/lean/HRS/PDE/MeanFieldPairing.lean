import HRS.PDE.MeanFieldInputs

/-!
# Symmetrisation of the interaction pairing (packet I6)

For a Lipschitz density `ρ` (e.g. `Torus.IsCk 1 ρ`) and a `C²` test `ψ`,
`interactionPairing D ψ (ρ dx) (ρ dx) = ∫ ρ ∇ψ·M(∇g⋆ρ)` with the cancellation convention.
(For merely continuous `ρ` and `s ≥ d-1` the right side is a non-absolutely convergent
principal value and `convGradConv` is the Bochner junk value `0`; see the report in
`MeanFieldInputs.lean` / the packet notes.)

Route: Fubini on `x` and `z = x - y` together with the oddness of `∇g`; no truncation.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS.KernelGrad

namespace HRS.PDE.MFPairing

variable {d : ℕ} {s C : ℝ} {G : Torus d → Euc d}

/-- Bounded, Lipschitz (in the torus distance), continuous. -/
def LipB (h : Torus d → ℝ) : Prop :=
  Continuous h ∧ ∃ B L : ℝ, 0 ≤ B ∧ 0 ≤ L ∧ (∀ x, |h x| ≤ B) ∧ IsLipschitz L h

theorem LipB.of_isCk {h : Torus d → ℝ} (hh : Torus.IsCk 1 h) : LipB h := by
  obtain ⟨B, hB0, hB⟩ := isCk_bounded hh
  obtain ⟨L, hL0, hL⟩ := isLipschitz_of_isCk hh
  exact ⟨isCk_continuous hh, B, L, hB0, hL0, hB, hL⟩

theorem LipB.mul {a w : Torus d → ℝ} (ha : LipB a) (hw : LipB w) : LipB (fun y => a y * w y) := by
  obtain ⟨hac, A, La, hA0, hLa0, hA, hLa⟩ := ha
  obtain ⟨hwc, Bw, Lw, hBw0, hLw0, hBw, hLw⟩ := hw
  obtain ⟨h1, h2⟩ := prod_data hA hLa hA0 hBw hLw hBw0
  exact ⟨hac.mul hwc, A * Bw, A * Lw + Bw * La, by positivity, by positivity, h1, h2⟩

theorem LipB.conv_continuous (hG : GoodKernel d s C G) {h : Torus d → ℝ} (hh : LipB h) :
    Continuous (convGradConv G h) := by
  obtain ⟨hc, B, L, hB0, hL0, hB, hL⟩ := hh
  exact hG.continuous_op hc hB hL hL0 hB0

theorem inner_kern (v : Euc d) (h : Torus d → ℝ) (x z : Torus d) :
    inner ℝ v (kern G h x z) =
      (h (x - z) - (if ‖z‖ ≤ 1 / 4 then h x else 0)) * inner ℝ v (G z) := by
  unfold kern
  split_ifs <;> simp [inner_smul_right]

theorem dom_nonneg (hG : GoodKernel d s C G) {L B : ℝ} (hL : 0 ≤ L) (hB : 0 ≤ B) (z : Torus d) :
    0 ≤ dom s C L B d z := by
  have := hG.hC0
  unfold dom
  have h1 : 0 ≤ ‖z‖ ^ (-s) := Real.rpow_nonneg (norm_nonneg _) _
  have h2 : 0 ≤ (1 / 4 : ℝ) ^ (-s - 1) := Real.rpow_nonneg (by norm_num) _
  positivity

theorem kern_norm_le_all (hG : GoodKernel d s C G) {h : Torus d → ℝ} {B L : ℝ}
    (hB : ∀ x, |h x| ≤ B) (hL : IsLipschitz L h) (hL0 : 0 ≤ L) (hB0 : 0 ≤ B) (x z : Torus d) :
    ‖kern G h x z‖ ≤ dom s C L B d z := by
  by_cases hz : z = 0
  · subst hz
    simp [kern]
    exact dom_nonneg hG hL0 hB0 0
  · exact kern_norm_le hG hB hL hL0 hB0 x hz

theorem measurable_kern_prod (hG : GoodKernel d s C G) {h : Torus d → ℝ} (hh : Measurable h) :
    Measurable (fun p : Torus d × Torus d => kern G h p.1 p.2) := by
  unfold kern
  refine Measurable.ite (measurableSet_le (measurable_norm.comp measurable_snd) measurable_const) ?_ ?_
  · exact ((hh.comp (measurable_fst.sub measurable_snd)).sub (hh.comp measurable_fst)).smul
      (hG.meas.comp measurable_snd)
  · exact (hh.comp (measurable_fst.sub measurable_snd)).smul (hG.meas.comp measurable_snd)

/-- Fubini form of the pairing of a bounded continuous `f` with `⟪v, ∇g ⋆ h⟫`. -/
theorem pair_eq (hG : GoodKernel d s C G) (v : Euc d) {f h : Torus d → ℝ}
    (hf : Continuous f) (hh : LipB h) :
    ∫ x, f x * inner ℝ v (convGradConv G h x) =
      ∫ z, inner ℝ v (G z) * ((∫ x, f x * h (x - z)) -
        (if ‖z‖ ≤ 1 / 4 then (1 : ℝ) else 0) * ∫ x, f x * h x) := by
  obtain ⟨hhc, B, L, hB0, hL0, hB, hL⟩ := hh
  obtain ⟨F, hF⟩ : ∃ F : ℝ, ∀ x, |f x| ≤ F := by
    obtain ⟨F, hF⟩ := isCompact_univ.exists_bound_of_continuousOn hf.continuousOn
    exact ⟨F, fun x => by simpa using hF x (Set.mem_univ x)⟩
  have hF0 : 0 ≤ F := (abs_nonneg _).trans (hF 0)
  have step1 : ∀ x, f x * inner ℝ v (convGradConv G h x) =
      ∫ z, f x * inner ℝ v (kern G h x z) := by
    intro x
    rw [convGradConv_eq_integral_kern, ← integral_inner (integrable_kern hG hhc.measurable hB hL hL0 hB0 x) v,
      ← integral_const_mul]
  simp_rw [step1]
  have hint : Integrable (Function.uncurry fun x z => f x * inner ℝ v (kern G h x z))
      ((volume : Measure (Torus d)).prod volume) := by
    have hdom : Integrable (fun p : Torus d × Torus d => (1 : ℝ) * dom s C L B d p.2)
        ((volume : Measure (Torus d)).prod volume) :=
      (integrable_const (1 : ℝ)).mul_prod (HRS.KernelGrad.integrable_dom hG L B)
    refine (hdom.const_mul (F * ‖v‖)).mono' ?_ (Eventually.of_forall fun p => ?_)
    · have hm := measurable_kern_prod hG hhc.measurable
      exact ((hf.measurable.comp measurable_fst).mul
        ((continuous_const.inner continuous_id).measurable.comp hm)).aestronglyMeasurable
    · simp only [Function.uncurry, Real.norm_eq_abs, one_mul]
      rw [abs_mul]
      have h1 := hF p.1
      have h2 : |inner ℝ v (kern G h p.1 p.2)| ≤ ‖v‖ * ‖kern G h p.1 p.2‖ :=
        abs_real_inner_le_norm _ _
      have h3 := kern_norm_le_all hG hB hL hL0 hB0 p.1 p.2
      calc |f p.1| * |inner ℝ v (kern G h p.1 p.2)| ≤ F * (‖v‖ * dom s C L B d p.2) := by
            gcongr
            exact h2.trans (by gcongr)
        _ = F * ‖v‖ * dom s C L B d p.2 := by ring
  rw [integral_integral_swap hint]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only
  have hp : ∀ x, f x * inner ℝ v (kern G h x z) =
      inner ℝ v (G z) * (f x * h (x - z)) -
        (inner ℝ v (G z) * (if ‖z‖ ≤ 1 / 4 then (1 : ℝ) else 0)) * (f x * h x) := by
    intro x
    rw [inner_kern]
    split_ifs <;> ring
  simp_rw [hp]
  have i1 : Integrable (fun x => f x * h (x - z)) :=
    (hf.mul (hhc.comp (continuous_id.sub continuous_const))).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have i2 : Integrable (fun x => f x * h x) :=
    (hf.mul hhc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  rw [integral_sub (i1.const_mul _) (i2.const_mul _), integral_const_mul, integral_const_mul]
  ring

/-- Antisymmetry of the cancellation convolution against bounded Lipschitz functions. -/
theorem antisym (hG : GoodKernel d s C G) (v : Euc d) {f h : Torus d → ℝ}
    (hf : LipB f) (hh : LipB h) :
    ∫ x, f x * inner ℝ v (convGradConv G h x) = -∫ x, h x * inner ℝ v (convGradConv G f x) := by
  rw [pair_eq hG v hf.1 hh, pair_eq hG v hh.1 hf]
  set R : Torus d → ℝ := fun z => inner ℝ v (G z) * ((∫ x, f x * h (x - z)) -
        (if ‖z‖ ≤ 1 / 4 then (1 : ℝ) else 0) * ∫ x, f x * h x) with hR
  rw [← integral_neg, ← integral_neg_eq_self R volume]
  refine integral_congr_ae (Eventually.of_forall fun z => ?_)
  simp only [hR]
  have e1 : (∫ x, h x * f (x - z)) = ∫ x, f x * h (x - (-z)) := by
    rw [← integral_add_right_eq_self (fun x => h x * f (x - z)) z]
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only [sub_neg_eq_add, add_sub_cancel_right]
    ring
  have e2 : (∫ x, h x * f x) = ∫ x, f x * h x := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  have e3 : G (-z) = -G z := hG.odd z
  have e4 : ‖-z‖ = ‖z‖ := norm_neg z
  rw [e1, e2, e3, e4, inner_neg_right]
  ring


theorem integrable_of_continuous {f : Torus d → ℝ} (hf : Continuous f) : Integrable f :=
  hf.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-- The substitution `y = x - z` in the pairing: integrability and value of the inner integral. -/
theorem comb (hG : GoodKernel d s C G) (v : Euc d) {a w : Torus d → ℝ} (ha : LipB a) (hw : LipB w)
    (x : Torus d) :
    Integrable (fun y => w y * ((a x - a y) * inner ℝ v (G (x - y)))) ∧
    ∫ y, w y * ((a x - a y) * inner ℝ v (G (x - y))) =
      a x * inner ℝ v (convGradConv G w x) -
        inner ℝ v (convGradConv G (fun y => a y * w y) x) := by
  have haw := ha.mul hw
  obtain ⟨hwc, Bw, Lw, hBw0, hLw0, hBw, hLw⟩ := hw
  obtain ⟨hawc, Bu, Lu, hBu0, hLu0, hBu, hLu⟩ := haw
  have hk1 := integrable_kern hG hawc.measurable hBu hLu hLu0 hBu0 x
  have hk2 := integrable_kern hG hwc.measurable hBw hLw hLw0 hBw0 x
  have hF : Integrable (fun z => inner ℝ v (kern G (fun y => a y * w y) x z) -
      a x * inner ℝ v (kern G w x z)) :=
    (hk1.const_inner v).sub ((hk2.const_inner v).const_mul _)
  have hpt : ∀ z, inner ℝ v (kern G (fun y => a y * w y) x z) -
      a x * inner ℝ v (kern G w x z) =
      inner ℝ v (G z) * (w (x - z) * (a (x - z) - a x)) := by
    intro z
    rw [inner_kern, inner_kern]
    split_ifs <;> ring
  have hpt2 : ∀ y, w y * ((a x - a y) * inner ℝ v (G (x - y))) =
      -((fun z => inner ℝ v (kern G (fun y => a y * w y) x z) -
        a x * inner ℝ v (kern G w x z)) (x - y)) := by
    intro y
    simp only [hpt, sub_sub_cancel]
    ring
  simp_rw [hpt2]
  refine ⟨(hF.comp_sub_left x).neg, ?_⟩
  rw [integral_neg, integral_sub_left_eq_self (fun z => inner ℝ v (kern G (fun y => a y * w y) x z) -
        a x * inner ℝ v (kern G w x z)) volume x,
    integral_sub (hk1.const_inner v) ((hk2.const_inner v).const_mul _), integral_const_mul,
    integral_inner hk1 v, integral_inner hk2 v, ← convGradConv_eq_integral_kern,
    ← convGradConv_eq_integral_kern]
  ring

theorem scalar (hG : GoodKernel d s C G) (v : Euc d) {a w : Torus d → ℝ} (ha : LipB a) (hw : LipB w) :
    ∫ x, w x * (∫ y, w y * ((a x - a y) * inner ℝ v (G (x - y)))) =
      2 * ∫ x, w x * (a x * inner ℝ v (convGradConv G w x)) := by
  have haw := ha.mul hw
  have hc1 := hw.conv_continuous hG
  have hc2 := haw.conv_continuous hG
  simp_rw [fun x => (comb hG v ha hw x).2]
  have i1 : Integrable (fun x => w x * (a x * inner ℝ v (convGradConv G w x))) :=
    integrable_of_continuous (hw.1.mul (ha.1.mul (continuous_const.inner hc1)))
  have i2 : Integrable (fun x => w x * inner ℝ v (convGradConv G (fun y => a y * w y) x)) :=
    integrable_of_continuous (hw.1.mul (continuous_const.inner hc2))
  have e : ∀ x, w x * (a x * inner ℝ v (convGradConv G w x) -
      inner ℝ v (convGradConv G (fun y => a y * w y) x)) =
      w x * (a x * inner ℝ v (convGradConv G w x)) -
        w x * inner ℝ v (convGradConv G (fun y => a y * w y) x) := fun x => by ring
  simp_rw [e]
  rw [integral_sub i1 i2, antisym hG v hw haw]
  have : ∫ x, (fun y => a y * w y) x * inner ℝ v (convGradConv G w x) =
      ∫ x, w x * (a x * inner ℝ v (convGradConv G w x)) := by
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only; ring
  rw [this]; ring

theorem inner_matVec_decomp (M : Matrix (Fin d) (Fin d) ℝ) (p g : Euc d) :
    inner ℝ p (Torus.matVec M g) = ∑ j, inner ℝ (EuclideanSpace.single j (1 : ℝ)) g *
      inner ℝ p (Torus.matVec M (EuclideanSpace.single j (1 : ℝ))) := by
  have hg : g = ∑ j, g j • EuclideanSpace.single j (1 : ℝ) := by
    ext i
    simp [Finset.sum_apply, Pi.single_apply]
  conv_lhs => rw [hg]
  unfold Torus.matVec
  simp [map_sum, inner_sum, inner_smul_right, EuclideanSpace.inner_single_left]


/-- The abstract symmetrisation identity for a good kernel. -/
theorem core (hG : GoodKernel d s C G) (M : Matrix (Fin d) (Fin d) ℝ) (u : Torus d → Euc d)
    (hu : ∀ j, LipB (fun x => inner ℝ (u x) (Torus.matVec M (EuclideanSpace.single j (1 : ℝ)))))
    {ρ : Torus d → ℝ} (hρ : LipB ρ) :
    (1 / 2 : ℝ) * ∫ x, ρ x * ∫ y, ρ y * inner ℝ (u x - u y) (Torus.matVec M (G (x - y))) =
      ∫ x, ρ x * inner ℝ (u x) (Torus.matVec M (convGradConv G ρ x)) := by
  set a : Fin d → Torus d → ℝ :=
    fun j x => inner ℝ (u x) (Torus.matVec M (EuclideanSpace.single j (1 : ℝ))) with ha
  set e : Fin d → Euc d := fun j => EuclideanSpace.single j (1 : ℝ) with he
  have hpt : ∀ x y, ρ y * inner ℝ (u x - u y) (Torus.matVec M (G (x - y))) =
      ∑ j, ρ y * ((a j x - a j y) * inner ℝ (e j) (G (x - y))) := by
    intro x y
    rw [inner_matVec_decomp, Finset.mul_sum]
    refine Finset.sum_congr rfl fun j _ => ?_
    simp only [ha, he, inner_sub_left]
    ring
  have hinner : ∀ x, ∫ y, ρ y * inner ℝ (u x - u y) (Torus.matVec M (G (x - y))) =
      ∑ j, (a j x * inner ℝ (e j) (convGradConv G ρ x) -
        inner ℝ (e j) (convGradConv G (fun y => a j y * ρ y) x)) := by
    intro x
    simp_rw [hpt]
    rw [integral_finsetSum _ fun j _ => (comb hG (e j) (hu j) hρ x).1]
    exact Finset.sum_congr rfl fun j _ => (comb hG (e j) (hu j) hρ x).2
  have hcont : ∀ j, Continuous fun x => ρ x * (a j x * inner ℝ (e j) (convGradConv G ρ x)) :=
    fun j => hρ.1.mul ((hu j).1.mul (continuous_const.inner (hρ.conv_continuous hG)))
  have hcont2 : ∀ j, Continuous fun x => ρ x *
      (a j x * inner ℝ (e j) (convGradConv G ρ x) -
        inner ℝ (e j) (convGradConv G (fun y => a j y * ρ y) x)) := fun j =>
    hρ.1.mul (((hu j).1.mul (continuous_const.inner (hρ.conv_continuous hG))).sub
      (continuous_const.inner (((hu j).mul hρ).conv_continuous hG)))
  have hL : ∫ x, ρ x * ∫ y, ρ y * inner ℝ (u x - u y) (Torus.matVec M (G (x - y))) =
      ∑ j, ∫ x, ρ x * (∫ y, ρ y * ((a j x - a j y) * inner ℝ (e j) (G (x - y)))) := by
    have : ∀ x, ρ x * ∫ y, ρ y * inner ℝ (u x - u y) (Torus.matVec M (G (x - y))) =
        ∑ j, ρ x * (a j x * inner ℝ (e j) (convGradConv G ρ x) -
          inner ℝ (e j) (convGradConv G (fun y => a j y * ρ y) x)) := by
      intro x
      rw [hinner, Finset.mul_sum]
    simp_rw [this]
    rw [integral_finsetSum _ fun j _ => integrable_of_continuous (hcont2 j)]
    refine Finset.sum_congr rfl fun j _ => ?_
    refine integral_congr_ae (Eventually.of_forall fun x => ?_)
    simp only
    rw [(comb hG (e j) (hu j) hρ x).2]
  have hR : ∫ x, ρ x * inner ℝ (u x) (Torus.matVec M (convGradConv G ρ x)) =
      ∑ j, ∫ x, ρ x * (a j x * inner ℝ (e j) (convGradConv G ρ x)) := by
    have : ∀ x, ρ x * inner ℝ (u x) (Torus.matVec M (convGradConv G ρ x)) =
        ∑ j, ρ x * (a j x * inner ℝ (e j) (convGradConv G ρ x)) := by
      intro x
      rw [inner_matVec_decomp, Finset.mul_sum]
      refine Finset.sum_congr rfl fun j _ => ?_
      simp only [ha, he]
      ring
    simp_rw [this]
    rw [integral_finsetSum _ fun j _ => integrable_of_continuous (hcont j)]
  rw [hL, hR, Finset.mul_sum]
  refine Finset.sum_congr rfl fun j _ => ?_
  rw [scalar hG (e j) (hu j) hρ]
  ring

theorem integral_withDensityReal {ρ : Torus d → ℝ} (hρ : Measurable ρ) (hρ0 : ∀ x, 0 ≤ ρ x)
    (f : Torus d → ℝ) : ∫ x, f x ∂(withDensityReal ρ) = ∫ x, ρ x * f x := by
  unfold withDensityReal
  have : (fun x => ENNReal.ofReal (ρ x)) = fun x => ((ρ x).toNNReal : ENNReal) := rfl
  rw [this, integral_withDensity_eq_integral_smul hρ.real_toNNReal f]
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp [NNReal.smul_def, Real.coe_toNNReal _ (hρ0 x)]


theorem isCk_one_inner_grad {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) (c : Euc d) :
    Torus.IsCk 1 (fun x => inner ℝ (Torus.grad ψ x) c) := by
  have h2 : Torus.IsCk ((1 + 1 : ℕ) : WithTop ℕ∞) ψ := by exact_mod_cast hψ
  have h1 : Torus.IsCk ((1 : ℕ) : WithTop ℕ∞) (Torus.grad ψ) := isCk_grad 1 ψ h2
  have h1' : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞) (Torus.lift (Torus.grad ψ)) := h1
  have : ContDiff ℝ ((1 : ℕ) : WithTop ℕ∞)
      (Torus.lift fun x => inner ℝ (Torus.grad ψ x) c) := h1'.inner ℝ contDiff_const
  exact_mod_cast this

/-- **(I6), Lipschitz version.**  For a `C¹` (hence Lipschitz) nonnegative density `ρ` and a `C²`
test `ψ`, the symmetrised interaction pairing equals `∫ ρ ∇ψ·M(∇g⋆ρ)` (cancellation convention).
For merely continuous `ρ` and `s ≥ d-1` the right-hand side is not an absolutely convergent
integral (Bochner junk value `0`), so this is the natural form. -/
theorem interactionPairing_eq_of_isCk (hd : 1 ≤ d) (D : DynData d) (ρ : Torus d → ℝ)
    (hρ : Torus.IsCk 1 ρ) (hρ0 : ∀ x, 0 ≤ ρ x) (ψ : Torus d → ℝ) (hψ : Torus.IsCk 2 ψ) :
    interactionPairing D ψ (withDensityReal ρ) (withDensityReal ρ) =
      ∫ x, ρ x * inner ℝ (Torus.grad ψ x)
        (Torus.matVec D.M (convGradConv (periodicRieszGrad d D.s) ρ x)) := by
  obtain ⟨C, hG⟩ := KernelGradD1.goodKernel_periodicRieszGrad_of_one_le (d := d) hd D.hs0 D.hsd
  have hρL : LipB ρ := LipB.of_isCk hρ
  have hρm : Measurable ρ := hρL.1.measurable
  have hu : ∀ j, LipB (fun x => inner ℝ (Torus.grad ψ x)
      (Torus.matVec D.M (EuclideanSpace.single j (1 : ℝ)))) :=
    fun j => LipB.of_isCk (isCk_one_inner_grad hψ _)
  rw [← core hG D.M (Torus.grad ψ) hu hρL]
  unfold interactionPairing
  simp_rw [integral_withDensityReal hρm hρ0]
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun x => ?_)
  simp only
  congr 1
  refine integral_congr_ae (Eventually.of_forall fun y => ?_)
  simp only
  by_cases h : x = y
  · subst h; simp
  · simp [h]

end HRS.PDE.MFPairing
