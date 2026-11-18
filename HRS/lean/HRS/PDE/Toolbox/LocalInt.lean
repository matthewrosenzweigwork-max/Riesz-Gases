import HRS.PDE.Toolbox.Kernel
import HRS.PDE.Toolbox.Product

/-!
# Appendix C helper lemmas: local integrability of powers of the torus distance

Auxiliary results for `HRS/PDE/Toolbox.lean`.

Main results (namespace `HRS.PDE.LocInt`):

* `integrable_tdist_rpow`: for `α < d`, `z ↦ tdist z 0 ^ (-α)` is integrable on `𝕋^d`.
  Proof: for `0 < α`, `t^{-α} ≤ ∏_i |c_i|^{-α/d}` where `c = centeredRep z` and `t = |c| ≥ |c_i|`;
  the product is integrable on the product measure, each factor being a power `|c|^{-β}`, `β < 1`,
  on the circle.
* `schur_integrable`: Schur/Young bound `∬ ρ(x-y) |w(x)| |w(y)| ≤ (∫ρ) ‖w‖₂²` for integrable `ρ ≥ 0`.
* `measurable_of_smoothOffZero`, tdist symmetry, Lipschitz ⇒ continuous, Hölder seminorm bound.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS.PDE.LocInt

open Set

/-! ### The centered coordinate on the circle -/

/-- centered coordinate `(-1/2, 1/2]` on the circle -/
def cc (u : UnitAddCircle) : ℝ :=
  if (AddCircle.equivIco (1 : ℝ) 0 u : ℝ) ≤ 1 / 2 then (AddCircle.equivIco (1 : ℝ) 0 u : ℝ)
  else (AddCircle.equivIco (1 : ℝ) 0 u : ℝ) - 1

theorem centeredRep_apply {d : ℕ} (z : Torus d) (i : Fin d) : Torus.centeredRep z i = cc (z i) := rfl

theorem measurable_cc : Measurable cc := by
  have h1 : Measurable fun t : UnitAddCircle =>
      ((AddCircle.equivIco (1 : ℝ) 0 t : Set.Ico (0 : ℝ) (0 + 1)) : ℝ) :=
    measurable_subtype_coe.comp (AddCircle.measurableEquivIco 1 0).measurable
  exact Measurable.ite (measurableSet_le h1 measurable_const) h1 (h1.sub_const 1)

theorem cc_coe {t : ℝ} (h1 : -1 / 2 < t) (h2 : t ≤ 1 / 2) : cc (t : UnitAddCircle) = t := by
  unfold cc
  have hf : (AddCircle.equivIco (1 : ℝ) 0 (t : UnitAddCircle) : ℝ) = Int.fract t := by
    simp
  rw [hf]
  by_cases h0 : 0 ≤ t
  · have : Int.fract t = t := Int.fract_eq_self.2 ⟨h0, by linarith⟩
    simp [this, show t ≤ 2⁻¹ by linarith]
  · have h0' : t < 0 := not_le.1 h0
    have : Int.fract t = t + 1 := by
      rw [← Int.fract_add_one, Int.fract_eq_self.2 ⟨by linarith, by linarith⟩]
    have h3 : ¬ (t + 1 ≤ 1 / 2) := by intro h; linarith
    simp [this, show ¬ (t + 1 ≤ 2⁻¹) by intro h; linarith]

theorem cc_eq_zero_iff (u : UnitAddCircle) : cc u = 0 ↔ u = 0 := by
  have hr := (AddCircle.equivIco (1 : ℝ) 0 u).2
  simp only [zero_add] at hr
  have hu : (((AddCircle.equivIco (1 : ℝ) 0 u : ℝ)) : UnitAddCircle) = u := by
    simp
  constructor
  · intro h
    unfold cc at h
    split_ifs at h with h1
    · rw [← hu, h]; simp
    · linarith [hr.2]
  · intro h
    have : (AddCircle.equivIco (1 : ℝ) 0 u : ℝ) = 0 := by
      rw [h]
      have := AddCircle.equivIco_coe_of_mem (p := (1 : ℝ)) (a := 0) (y := (0 : ℝ)) (by simp)
      simpa using this
    unfold cc
    simp [this]

theorem integrableOn_abs_rpow_Ioc {β : ℝ} (hβ : β < 1) :
    IntegrableOn (fun t : ℝ => |t| ^ (-β)) (Set.Ioc (-1/2 : ℝ) (-1/2 + 1)) := by
  have h0 : IntegrableOn (fun t : ℝ => t ^ (-β)) (Ioc (0:ℝ) (1/2)) := by
    have := (intervalIntegral.intervalIntegrable_rpow' (a := 0) (b := 1/2) (r := -β) (by linarith))
    exact (intervalIntegrable_iff_integrableOn_Ioc_of_le (by norm_num)).1 this
  have h1 : IntegrableOn (fun t : ℝ => |t| ^ (-β)) (Ioc (0:ℝ) (1/2)) :=
    h0.congr_fun (fun t ht => by simp [abs_of_pos ht.1]) measurableSet_Ioc
  have h2 : IntegrableOn (fun t : ℝ => |t| ^ (-β)) (Ico (-(1/2) : ℝ) 0) := by
    have := h1.comp_neg
    have e : (-Ioc (0:ℝ) (1/2)) = Ico (-(1/2)) 0 := by
      ext t; simp [Set.mem_Ico]
    rw [e] at this
    simpa using this
  have h3 : IntegrableOn (fun t : ℝ => |t| ^ (-β)) (Ioc (-(1/2) : ℝ) (1/2)) := by
    have : Ioc (-(1/2) : ℝ) (1/2) ⊆ (Ico (-(1/2) : ℝ) 0 ∪ Ioc (0:ℝ) (1/2)) ∪ {0} := by
      intro t ht
      rcases lt_trichotomy t 0 with h | h | h
      · exact Or.inl (Or.inl ⟨ht.1.le, h⟩)
      · exact Or.inr h
      · exact Or.inl (Or.inr ⟨h, ht.2⟩)
    exact ((h2.union h1).union (by
      rw [IntegrableOn, Measure.restrict_eq_zero.2 Real.volume_singleton]
      exact integrable_zero_measure)).mono_set this
  have e : (-1/2 : ℝ) + 1 = 1/2 := by norm_num
  rw [e]; convert h3 using 2; norm_num

theorem integrable_cc_rpow {β : ℝ} (hβ : β < 1) :
    Integrable (fun u : UnitAddCircle => |cc u| ^ (-β)) := by
  have hm : Measurable fun u : UnitAddCircle => |cc u| ^ (-β) :=
    (measurable_cc.abs).pow_const _
  refine ⟨hm.aestronglyMeasurable, ?_⟩
  have h := UnitAddCircle.lintegral_preimage (-1 / 2) (fun u => ‖|cc u| ^ (-β)‖ₑ)
  unfold HasFiniteIntegral
  rw [← h]
  have hI := (integrableOn_abs_rpow_Ioc hβ).2
  unfold HasFiniteIntegral at hI
  refine lt_of_le_of_lt (le_of_eq ?_) hI
  refine setLIntegral_congr_fun measurableSet_Ioc (fun t ht => ?_)
  simp only
  rw [cc_coe ht.1 (by linarith [ht.2])]

/-! ### `tdist` basics -/

variable {d : ℕ}

theorem tdist_nonneg (x y : Torus d) : 0 ≤ Torus.tdist x y := norm_nonneg _

theorem tdist_zero_right (x y : Torus d) : Torus.tdist x y = Torus.tdist (x - y) 0 := by
  simp [Torus.tdist]

theorem tdist_eq_sqrt (z : Torus d) : Torus.tdist z 0 = Real.sqrt (∑ i, ‖z i‖ ^ 2) := by
  unfold Torus.tdist
  rw [sub_zero, EuclideanSpace.norm_eq]
  congr 1
  refine Finset.sum_congr rfl fun i _ => ?_
  rw [Real.norm_eq_abs, ← ProdAux.abs_centeredRep, sq_abs]

theorem tdist_self (x : Torus d) : Torus.tdist x x = 0 := by
  rw [tdist_zero_right, sub_self, tdist_eq_sqrt]; simp

theorem tdist_neg (z : Torus d) : Torus.tdist (-z) 0 = Torus.tdist z 0 := by
  rw [tdist_eq_sqrt, tdist_eq_sqrt]
  simp

theorem tdist_comm (x y : Torus d) : Torus.tdist x y = Torus.tdist y x := by
  rw [tdist_zero_right x y, tdist_zero_right y x, ← tdist_neg (x - y)]
  simp

theorem tdist_le_dim (z : Torus d) : Torus.tdist z 0 ≤ d := Kern.tdist_zero_le z

theorem norm_le_tdist (x y : Torus d) : ‖x - y‖ ≤ Torus.tdist x y := by
  rw [pi_norm_le_iff_of_nonneg (tdist_nonneg x y)]
  intro i
  rw [← ProdAux.abs_centeredRep]
  have := PiLp.norm_apply_le (Torus.centeredRep (x - y)) i
  simpa [Real.norm_eq_abs, Torus.tdist, Pi.sub_apply] using this

theorem measurable_tdist_pair : Measurable fun p : Torus d × Torus d => Torus.tdist p.1 p.2 := by
  have : (fun p : Torus d × Torus d => Torus.tdist p.1 p.2) =
      fun p => Torus.tdist (p.1 - p.2) 0 := by
    funext p; exact tdist_zero_right _ _
  rw [this]
  exact Kern.measurable_tdist_zero.comp (measurable_fst.sub measurable_snd)

theorem tdist_eq_zero_iff (x y : Torus d) : Torus.tdist x y = 0 ↔ x = y := by
  constructor
  · intro h
    have h' : Torus.tdist (x - y) 0 = 0 := by rw [← tdist_zero_right]; exact h
    rw [tdist_eq_sqrt] at h'
    have h3 : ∑ i, ‖(x - y) i‖ ^ 2 = 0 := by
      by_contra hne
      have : 0 < ∑ i, ‖(x - y) i‖ ^ 2 :=
        lt_of_le_of_ne (Finset.sum_nonneg fun _ _ => by positivity) (Ne.symm hne)
      have := Real.sqrt_pos.2 this
      linarith
    refine sub_eq_zero.1 (funext fun i => ?_)
    have := (Finset.sum_eq_zero_iff_of_nonneg (fun _ _ => by positivity)).1 h3 i (Finset.mem_univ i)
    simpa using this
  · rintro rfl; exact tdist_self x


/-! ### Integrability of `tdist ^ (-α)` -/

theorem circle_singleton (x : UnitAddCircle) : (volume : Measure UnitAddCircle) {x} = 0 := by
  refine le_antisymm ?_ (zero_le)
  refine ENNReal.le_of_forall_pos_le_add fun ε hε _ => ?_
  rw [zero_add]
  have h1 : ({x} : Set UnitAddCircle) ⊆ Metric.closedBall x ((ε : ℝ) / 2) := by
    intro y hy; rw [Set.mem_singleton_iff.1 hy]; simp only [Metric.mem_closedBall, dist_self]; positivity
  refine (measure_mono h1).trans ?_
  rw [AddCircle.volume_closedBall]
  have : ENNReal.ofReal (min 1 (2 * ((ε : ℝ) / 2))) ≤ ENNReal.ofReal ε := by
    apply ENNReal.ofReal_le_ofReal
    have := min_le_right (1 : ℝ) (2 * ((ε : ℝ) / 2))
    linarith
  simpa using this

theorem ae_coords_ne_zero : ∀ᵐ z : Torus d ∂volume, ∀ i, z i ≠ 0 := by
  rw [ae_all_iff]
  intro i
  have : NullSingletonClass (volume : Measure UnitAddCircle) := ⟨circle_singleton⟩
  have h : (volume : Measure (Torus d)) {f | f i = 0} = 0 :=
    Measure.pi_hyperplane (fun _ : Fin d => (volume : Measure UnitAddCircle)) i 0
  exact measure_eq_zero_iff_ae_notMem.1 h

theorem integrable_tdist_rpow {α : ℝ} (hα : α < d) :
    Integrable (fun z : Torus d => Torus.tdist z 0 ^ (-α)) := by
  have hm : Measurable fun z : Torus d => Torus.tdist z 0 ^ (-α) :=
    Kern.measurable_tdist_zero.pow_const _
  by_cases hα0 : α ≤ 0
  · refine Integrable.of_bound hm.aestronglyMeasurable ((d : ℝ) ^ (-α)) (Eventually.of_forall fun z => ?_)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg (tdist_nonneg _ _) _)]
    exact Real.rpow_le_rpow (tdist_nonneg _ _) (tdist_le_dim z) (by linarith)
  · push Not at hα0
    have hd : (0 : ℝ) < d := by linarith
    have hd' : 0 < d := by exact_mod_cast hd
    have : Nonempty (Fin d) := ⟨⟨0, hd'⟩⟩
    set β : ℝ := α / d with hβdef
    have hβ0 : 0 ≤ β := div_nonneg hα0.le hd.le
    have hβ : β < 1 := by rw [hβdef, div_lt_one hd]; exact hα
    have hG : Integrable (fun z : Torus d => ∏ i, |cc (z i)| ^ (-β)) := by
      have := Integrable.fintype_prod (ι := Fin d) (𝕜 := ℝ) (E := UnitAddCircle)
        (f := fun _ u => |cc u| ^ (-β)) (μ := fun _ => (volume : Measure UnitAddCircle))
        (fun _ => integrable_cc_rpow hβ)
      exact this
    refine hG.mono' hm.aestronglyMeasurable ?_
    filter_upwards [ae_coords_ne_zero] with z hz
    have hc : ∀ i, 0 < |cc (z i)| := fun i =>
      abs_pos.2 (fun h => hz i ((cc_eq_zero_iff _).1 h))
    have hle : ∀ i, |cc (z i)| ≤ Torus.tdist z 0 := by
      intro i
      have := PiLp.norm_apply_le (Torus.centeredRep z) i
      simpa [Torus.tdist, centeredRep_apply, Real.norm_eq_abs] using this
    have ht : 0 < Torus.tdist z 0 := lt_of_lt_of_le (hc ⟨0, hd'⟩) (hle _)
    rw [Real.norm_of_nonneg (Real.rpow_nonneg ht.le _)]
    have h1 : Torus.tdist z 0 ^ (-α) = ∏ _i : Fin d, Torus.tdist z 0 ^ (-β) := by
      rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin, ← Real.rpow_natCast,
        ← Real.rpow_mul ht.le]
      congr 1
      rw [hβdef]; field_simp
    rw [h1]
    refine Finset.prod_le_prod₀ (fun i _ => Real.rpow_nonneg ht.le _) (fun i _ => ?_)
    exact Real.rpow_le_rpow_of_nonpos (hc i) (hle i) (by linarith)

theorem exists_circle_ne_zero : ∃ u : UnitAddCircle, u ≠ 0 :=
  ⟨((1 / 2 : ℝ) : UnitAddCircle), fun h => by
    have := (cc_eq_zero_iff _).2 h
    rw [cc_coe (by norm_num) (by norm_num)] at this
    norm_num at this⟩

theorem exists_torus_ne_zero (hd : 1 ≤ d) : ∃ z : Torus d, z ≠ 0 := by
  obtain ⟨u, hu⟩ := exists_circle_ne_zero
  refine ⟨Function.update 0 ⟨0, hd⟩ u, fun h => hu ?_⟩
  have := congrFun h ⟨0, hd⟩
  simpa using this

/-! ### Measurability -/

theorem measurable_centeredRep : Measurable (Torus.centeredRep : Torus d → Euc d) := by
  have h : Measurable fun z : Torus d => (fun i => cc (z i) : Fin d → ℝ) :=
    measurable_pi_iff.2 fun i => measurable_cc.comp (measurable_pi_apply i)
  exact (PiLp.continuous_toLp 2 (fun _ : Fin d => ℝ)).measurable.comp h

theorem measurable_of_smoothOffZero {κ : Torus d → ℝ} (h : Torus.IsSmoothOffZero κ) :
    Measurable κ := by
  have hU : IsOpen {x : Euc d | Torus.mk x ≠ 0} :=
    (isClosed_singleton.isOpen_compl).preimage Torus.continuous_mk
  have h1 : ContinuousOn (Torus.lift κ) {x : Euc d | Torus.mk x ≠ 0} := h.continuousOn
  have hm : Measurable (Torus.lift κ) := by
    have : Torus.lift κ = {x : Euc d | Torus.mk x ≠ 0}.piecewise (Torus.lift κ) (fun _ => κ 0) := by
      funext x
      by_cases hx : Torus.mk x = 0
      · simp [Set.piecewise, hx, Torus.lift]
      · simp [Set.piecewise, hx]
    rw [this]
    exact ContinuousOn.measurable_piecewise h1 continuousOn_const hU.measurableSet
  have : κ = Torus.lift κ ∘ Torus.centeredRep := by
    funext z; simp [Torus.lift, Kern.centeredRep_mk]
  rw [this]; exact hm.comp measurable_centeredRep

/-! ### Lipschitz functions -/

theorem continuous_of_isLipschitz {L : ℝ} {a : Torus d → ℝ} (h : Torus.IsLipschitz L a) :
    Continuous a := (ProdAux.prodHyp_of_lipschitz h).cont

theorem abs_le_supNorm_of_isLipschitz {L : ℝ} {a : Torus d → ℝ} (h : Torus.IsLipschitz L a)
    (x : Torus d) : |a x| ≤ Torus.supNorm a := by
  simpa using norm_le_supNorm (continuous_of_isLipschitz h) x

theorem holderSeminorm_nonneg (a : Torus d → ℝ) : 0 ≤ Torus.holderSeminorm 1 a := by
  unfold Torus.holderSeminorm
  exact Real.iSup_nonneg fun p => by positivity

theorem abs_sub_le_holder {L : ℝ} {a : Torus d → ℝ} (h : Torus.IsLipschitz L a) (x y : Torus d) :
    |a x - a y| ≤ Torus.holderSeminorm 1 a * Torus.tdist x y := by
  by_cases hxy : x = y
  · subst hxy
    simp [tdist_self]
  have hdist : ∀ x y : Torus d, |a x - a y| ≤ |L| * Real.sqrt d * ‖x - y‖ := by
    intro x y
    calc |a x - a y| ≤ L * Torus.tdist x y := h x y
      _ ≤ |L| * Torus.tdist x y := by
          apply mul_le_mul_of_nonneg_right (le_abs_self _)
          exact norm_nonneg _
      _ ≤ |L| * (Real.sqrt d * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (ProdAux.tdist_le x y) (abs_nonneg _)
      _ = _ := by ring
  have hbdd : BddAbove (Set.range fun p : {p : Torus d × Torus d // p.1 ≠ p.2} =>
      |a p.1.1 - a p.1.2| / ‖p.1.1 - p.1.2‖ ^ (1 : ℝ)) := by
    refine ⟨|L| * Real.sqrt d, ?_⟩
    rintro _ ⟨p, rfl⟩
    have hp : 0 < ‖p.1.1 - p.1.2‖ := norm_pos_iff.2 (sub_ne_zero.2 p.2)
    show |a p.1.1 - a p.1.2| / ‖p.1.1 - p.1.2‖ ^ (1 : ℝ) ≤ _
    rw [Real.rpow_one, div_le_iff₀ hp]
    exact hdist _ _
  have h1 : |a x - a y| / ‖x - y‖ ^ (1 : ℝ) ≤ Torus.holderSeminorm 1 a :=
    le_ciSup hbdd (⟨(x, y), hxy⟩ : {p : Torus d × Torus d // p.1 ≠ p.2})
  have hp : 0 < ‖x - y‖ := norm_pos_iff.2 (sub_ne_zero.2 hxy)
  rw [Real.rpow_one, div_le_iff₀ hp] at h1
  exact h1.trans (mul_le_mul_of_nonneg_left (norm_le_tdist x y) (holderSeminorm_nonneg a))

theorem isLipschitz_holder {L : ℝ} {a : Torus d → ℝ} (h : Torus.IsLipschitz L a) :
    Torus.IsLipschitz (Torus.holderSeminorm 1 a) a := abs_sub_le_holder h

theorem holderSeminorm_le_c01Norm (a : Torus d → ℝ) :
    Torus.holderSeminorm 1 a ≤ Torus.c01Norm a := by
  unfold Torus.c01Norm; linarith [supNorm_nonneg a]

theorem supNorm_le_c01Norm (a : Torus d → ℝ) :
    Torus.supNorm a ≤ Torus.c01Norm a := by
  unfold Torus.c01Norm; linarith [holderSeminorm_nonneg a]

theorem isLipschitz_mul {L L' : ℝ} {u v : Torus d → ℝ} (hu : Torus.IsLipschitz L u)
    (hv : Torus.IsLipschitz L' v) :
    Torus.IsLipschitz (Torus.supNorm u * L' + Torus.supNorm v * L) (fun x => u x * v x) := by
  intro x y
  have hA := abs_le_supNorm_of_isLipschitz hu x
  have hB := abs_le_supNorm_of_isLipschitz hv y
  have h1 := hu x y
  have h2 := hv x y
  have e : u x * v x - u y * v y = u x * (v x - v y) + v y * (u x - u y) := by ring
  rw [e]
  refine (abs_add_le _ _).trans ?_
  rw [abs_mul, abs_mul]
  have t0 := tdist_nonneg x y
  have := mul_le_mul hA h2 (abs_nonneg _) ((abs_nonneg _).trans hA)
  have := mul_le_mul hB h1 (abs_nonneg _) ((abs_nonneg _).trans hB)
  nlinarith

theorem memLp_two_of_isLipschitz {L : ℝ} {w : Torus d → ℝ} (h : Torus.IsLipschitz L w) :
    MemLp w 2 volume :=
  (continuous_of_isLipschitz h).memLp_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)

/-! ### Schur / Young bound -/

section Schur

variable {ρ g : Torus d → ℝ}

theorem integrable_sub_mul_snd (hρ : Integrable ρ) (hg : Integrable g) :
    Integrable (fun p : Torus d × Torus d => ρ (p.1 - p.2) * g p.2) ∧
    ∫ p : Torus d × Torus d, ρ (p.1 - p.2) * g p.2 = (∫ z, ρ z) * ∫ y, g y := by
  have hmeas : AEStronglyMeasurable (fun p : Torus d × Torus d => ρ (p.1 - p.2) * g p.2)
      (volume.prod volume) :=
    (hρ.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure (Torus d)) volume)).mul
      (hg.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_snd)
  have hint : Integrable (fun p : Torus d × Torus d => ρ (p.1 - p.2) * g p.2)
      (volume.prod volume) := by
    rw [integrable_prod_iff' hmeas]
    refine ⟨Eventually.of_forall fun y => (hρ.comp_sub_right y).mul_const (g y), ?_⟩
    refine (hg.norm.const_mul (∫ z, ‖ρ z‖)).congr (Eventually.of_forall fun y => ?_)
    simp only
    have : ∀ x : Torus d, ‖ρ (x - y) * g y‖ = ‖ρ (x - y)‖ * ‖g y‖ := fun x => norm_mul _ _
    simp_rw [this]
    rw [integral_mul_const, integral_sub_right_eq_self (fun x => ‖ρ x‖) y, mul_comm]
  refine ⟨hint, ?_⟩
  rw [show (volume : Measure (Torus d × Torus d)) = volume.prod volume from rfl,
    integral_prod_symm _ hint]
  have : ∀ y : Torus d, ∫ x : Torus d, ρ (x - y) * g y = (∫ z, ρ z) * g y := fun y => by
    rw [integral_mul_const, integral_sub_right_eq_self ρ y]
  simp_rw [this]
  rw [integral_const_mul]

theorem integrable_sub_mul_fst (hρ : Integrable ρ) (hg : Integrable g) :
    Integrable (fun p : Torus d × Torus d => ρ (p.1 - p.2) * g p.1) ∧
    ∫ p : Torus d × Torus d, ρ (p.1 - p.2) * g p.1 = (∫ z, ρ z) * ∫ y, g y := by
  have hmeas : AEStronglyMeasurable (fun p : Torus d × Torus d => ρ (p.1 - p.2) * g p.1)
      (volume.prod volume) :=
    (hρ.aestronglyMeasurable.comp_quasiMeasurePreserving
      (quasiMeasurePreserving_sub_of_right_invariant (volume : Measure (Torus d)) volume)).mul
      (hg.aestronglyMeasurable.comp_quasiMeasurePreserving Measure.quasiMeasurePreserving_fst)
  have hint : Integrable (fun p : Torus d × Torus d => ρ (p.1 - p.2) * g p.1)
      (volume.prod volume) := by
    rw [integrable_prod_iff hmeas]
    refine ⟨Eventually.of_forall fun x => (hρ.comp_sub_left x).mul_const (g x), ?_⟩
    refine (hg.norm.const_mul (∫ z, ‖ρ z‖)).congr (Eventually.of_forall fun x => ?_)
    simp only
    have : ∀ y : Torus d, ‖ρ (x - y) * g x‖ = ‖ρ (x - y)‖ * ‖g x‖ := fun y => norm_mul _ _
    simp_rw [this]
    rw [integral_mul_const, integral_sub_left_eq_self (fun x => ‖ρ x‖) volume x, mul_comm]
  refine ⟨hint, ?_⟩
  rw [show (volume : Measure (Torus d × Torus d)) = volume.prod volume from rfl,
    integral_prod _ hint]
  have : ∀ x : Torus d, ∫ y : Torus d, ρ (x - y) * g x = (∫ z, ρ z) * g x := fun x => by
    rw [integral_mul_const, integral_sub_left_eq_self ρ volume x]
  simp_rw [this]
  rw [integral_const_mul]

/-- **Schur/Young bound**: for an integrable `ρ ≥ 0`, `w ∈ L²`, and `G` measurable with
`|G(x,y)| ≤ ρ(x-y)|w(x)||w(y)|`, `G` is integrable and `|∬ G| ≤ (∫ρ) ‖w‖²₂`. -/
theorem schur_bound (hρ : Integrable ρ) (hρ0 : ∀ z, 0 ≤ ρ z) {w : Torus d → ℝ}
    (hw : MemLp w 2 volume) {G : Torus d × Torus d → ℝ}
    (hG : AEStronglyMeasurable G (volume : Measure (Torus d × Torus d)))
    (hbd : ∀ p : Torus d × Torus d, |G p| ≤ ρ (p.1 - p.2) * (|w p.1| * |w p.2|)) :
    Integrable G ∧ |∫ p, G p| ≤ (∫ z, ρ z) * ∫ x, w x ^ 2 := by
  have hw2 : Integrable (fun x => w x ^ 2) := hw.integrable_sq
  obtain ⟨hB, hBv⟩ := integrable_sub_mul_snd hρ hw2
  obtain ⟨hA, hAv⟩ := integrable_sub_mul_fst hρ hw2
  have hdom : Integrable (fun p : Torus d × Torus d =>
      (1 / 2 : ℝ) * (ρ (p.1 - p.2) * w p.1 ^ 2 + ρ (p.1 - p.2) * w p.2 ^ 2)) :=
    (hA.add hB).const_mul _
  have hpt : ∀ p : Torus d × Torus d, |G p| ≤
      (1 / 2 : ℝ) * (ρ (p.1 - p.2) * w p.1 ^ 2 + ρ (p.1 - p.2) * w p.2 ^ 2) := by
    intro p
    refine (hbd p).trans ?_
    have h2 : |w p.1| * |w p.2| ≤ (1 / 2) * (w p.1 ^ 2 + w p.2 ^ 2) := by
      nlinarith [sq_nonneg (|w p.1| - |w p.2|), sq_abs (w p.1), sq_abs (w p.2)]
    calc ρ (p.1 - p.2) * (|w p.1| * |w p.2|)
        ≤ ρ (p.1 - p.2) * ((1 / 2) * (w p.1 ^ 2 + w p.2 ^ 2)) :=
          mul_le_mul_of_nonneg_left h2 (hρ0 _)
      _ = _ := by ring
  have hint : Integrable G := by
    refine hdom.mono' hG (Eventually.of_forall fun p => ?_)
    rw [Real.norm_eq_abs]; exact hpt p
  refine ⟨hint, ?_⟩
  have hnorm : ‖∫ p, G p‖ ≤ ∫ p : Torus d × Torus d, (1 / 2 : ℝ) * (ρ (p.1 - p.2) * w p.1 ^ 2 + ρ (p.1 - p.2) * w p.2 ^ 2) :=
    norm_integral_le_of_norm_le hdom (Eventually.of_forall fun p => by
      rw [Real.norm_eq_abs]; exact hpt p)
  rw [Real.norm_eq_abs] at hnorm
  refine hnorm.trans (le_of_eq ?_)
  rw [integral_const_mul, integral_add hA hB, hAv, hBv]
  ring

end Schur

end HRS.PDE.LocInt
