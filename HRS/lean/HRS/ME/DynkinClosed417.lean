import HRS.ME.Dynkin417
import HRS.MD.DOMSpec

/-!
# Packet M2 (row 4.17): Dynkin's formula on the closed generator domain

Proof of `dynkin_closedGenerator` of `HRS/ME/Spec417.lean` (statement copied verbatim as
`dynkin_closedGenerator_proof`; `HRS/ME/Spec417.lean` is not imported).  Helpers carry the prefix `dcl417_`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.ME

variable {d : ℕ}

open HRS HRS.LZ

/-! ### Part 1: the covering map, the collision-free set, and continuity of the gradient energy -/

theorem dcl417_continuous_q {N : ℕ} :
    Continuous (fun Y : Fin N → Euc d => fun i => (Torus.mk (Y i) : Torus d)) :=
  continuous_pi fun i => Q84a.q84a_continuous_mk.comp (continuous_apply i)

theorem dcl417_isOpen_coverFree {N : ℕ} : IsOpen (coverFree d N) :=
  (isClosed_collisionSet d N).isOpen_compl.preimage dcl417_continuous_q

/-- The configuration gradient of `Φ` at a covering point of differentiability of `configLift Φ`. -/
theorem dcl417_gradY_eq {N : ℕ} (Φ : Config d N → ℝ) (Y : Fin N → Euc d) (i : Fin N)
    (hD : DifferentiableAt ℝ (configLift (fun _ => Φ) 0) Y) :
    configGrad Φ (fun j => Torus.mk (Y j)) i
      = (InnerProductSpace.toDual ℝ (Euc d)).symm
          ((fderiv ℝ (configLift (fun _ => Φ) 0) Y).comp
            (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i)) := by
  unfold configGrad
  rw [dyn417_gradient_fun Φ Y i]
  unfold gradient
  congr 1
  have hA : HasFDerivAt (fun u : Euc d => Y + (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) u)
      (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) 0 :=
    (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i).hasFDerivAt.const_add Y
  have hg : HasFDerivAt (configLift (fun _ => Φ) 0)
      (fderiv ℝ (configLift (fun _ => Φ) 0) (Y + (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) 0))
      (Y + (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) 0) := by
    simpa using hD.hasFDerivAt
  have hc := hg.comp (0 : Euc d) hA
  have hc' : HasFDerivAt (fun u : Euc d => configLift (fun _ => Φ) 0 (Y + Pi.single i u))
      ((fderiv ℝ (configLift (fun _ => Φ) 0) (Y + (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i) 0)).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i)) 0 := hc
  rw [hc'.fderiv]
  simp

theorem dcl417_continuous_comp_single {N : ℕ} (i : Fin N) :
    Continuous (fun A : (Fin N → Euc d) →L[ℝ] ℝ =>
      A.comp (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i)) := by
  have h := ((ContinuousLinearMap.compL ℝ (Euc d) (Fin N → Euc d) ℝ).flip
    (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i)).continuous
  refine h.congr fun A => ?_
  ext v
  simp

/-- The configuration gradient of a `C¹`-on-the-cover function is continuous on the cover off collisions. -/
theorem dcl417_gradY_cont {N : ℕ} (Φ : Config d N → ℝ) (i : Fin N)
    (hΦ : ContDiffOn ℝ 1 (configLift (fun _ => Φ) 0) (coverFree d N)) :
    ContinuousOn (fun Y : Fin N → Euc d => configGrad Φ (fun j => Torus.mk (Y j)) i)
      (coverFree d N) := by
  have hfd : ContinuousOn (fun Y => fderiv ℝ (configLift (fun _ => Φ) 0) Y) (coverFree d N) :=
    hΦ.continuousOn_fderiv_of_isOpen dcl417_isOpen_coverFree le_rfl
  have h1 : ContinuousOn (fun Y : Fin N → Euc d => (InnerProductSpace.toDual ℝ (Euc d)).symm
      ((fderiv ℝ (configLift (fun _ => Φ) 0) Y).comp
        (ContinuousLinearMap.single ℝ (fun _ : Fin N => Euc d) i))) (coverFree d N) :=
    (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.comp_continuousOn
      ((dcl417_continuous_comp_single i).comp_continuousOn hfd)
  refine h1.congr fun Y hY => ?_
  exact dcl417_gradY_eq Φ Y i
    ((hΦ.differentiableOn (by norm_num) Y hY).differentiableAt
      (dcl417_isOpen_coverFree.mem_nhds hY))

theorem dcl417_energy_cont {N : ℕ} (Φ : Config d N → ℝ)
    (hΦ : ContDiffOn ℝ 1 (configLift (fun _ => Φ) 0) (coverFree d N)) :
    ContinuousOn (fun Y : Fin N → Euc d =>
      ∑ i, ‖configGrad Φ (fun j => Torus.mk (Y j)) i‖ₑ ^ 2) (coverFree d N) :=
  continuousOn_finset_sum _ fun i _ =>
    ((ENNReal.continuous_pow 2).comp_continuousOn (continuous_enorm.comp_continuousOn (dcl417_gradY_cont Φ i hΦ)))

open Classical in
/-- Measurability of the energy integrand on the configuration space: it is the composition of a
Borel function on the cover (zero off the cover's collision-free set) with the lift `repC`. -/
theorem dcl417_energy_meas {N : ℕ} (Φ : Config d N → ℝ)
    (hΦ : ContDiffOn ℝ 1 (configLift (fun _ => Φ) 0) (coverFree d N)) :
    Measurable (fun X : Config d N => (coverFree d N).piecewise
      (fun Y : Fin N → Euc d => ∑ i, ‖configGrad Φ (fun j => Torus.mk (Y j)) i‖ₑ ^ 2)
      (fun _ => (0 : ℝ≥0∞)) (repC X)) := by
  have hpw : Measurable ((coverFree d N).piecewise
      (fun Y : Fin N → Euc d => ∑ i, ‖configGrad Φ (fun j => Torus.mk (Y j)) i‖ₑ ^ 2)
      (fun _ => (0 : ℝ≥0∞))) :=
    ContinuousOn.measurable_piecewise (dcl417_energy_cont Φ hΦ) continuousOn_const
      dcl417_isOpen_coverFree.measurableSet
  exact hpw.comp measurable_repC

/-! ### Part 2: continuity along paths, via the open quotient map `Y ↦ (mk (Y i))_i` -/

theorem dcl417_isOpenQuotientMap_mk :
    IsOpenQuotientMap (Torus.mk : Euc d → Torus d) := by
  have h1 : IsOpenQuotientMap
      (Pi.map (fun _ : Fin d => ((↑) : ℝ → UnitAddCircle))) :=
    IsOpenQuotientMap.piMap fun _ => QuotientAddGroup.isOpenQuotientMap_mk
  have h2 := h1.comp (PiLp.homeomorph 2 (fun _ : Fin d => ℝ)).isOpenQuotientMap
  exact h2

theorem dcl417_isOpenQuotientMap {N : ℕ} :
    IsOpenQuotientMap (fun Y : Fin N → Euc d => fun i => (Torus.mk (Y i) : Torus d)) :=
  IsOpenQuotientMap.piMap fun _ => dcl417_isOpenQuotientMap_mk

theorem dcl417_continuousOn_compl {N : ℕ} (F : Config d N → ℝ)
    (hF : ContinuousOn (fun Y : Fin N → Euc d => F (fun i => Torus.mk (Y i))) (coverFree d N)) :
    ContinuousOn F (collisionSet d N)ᶜ := by
  have hU : IsOpen (collisionSet d N)ᶜ := (isClosed_collisionSet d N).isOpen_compl
  have hq := (dcl417_isOpenQuotientMap (d := d) (N := N)).isQuotientMap
  rw [continuousOn_iff_continuous_domRestrict]
  rw [(hq.restrictPreimage_isOpen hU).continuous_iff]
  exact hF.domRestrict


/-! ### Part 3: measure-theoretic tools along the path -/

theorem dcl417_lint_stat {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    {X : ℝ≥0 → Ω → Config d N} {H : ℝ} {μ : Measure (Config d N)}
    (hXm : ∀ t : ℝ≥0, Measurable (X t))
    (hstat : ∀ t : ℝ≥0, (t : ℝ) ≤ H → P.map (X t) = μ)
    {g : Config d N → ℝ≥0∞} (hg : Measurable g) {r : ℝ} (hr0 : 0 ≤ r) (hrH : r ≤ H) :
    ∫⁻ ω, g (X r.toNNReal ω) ∂P = ∫⁻ x, g x ∂μ := by
  have hle : ((r.toNNReal : ℝ≥0) : ℝ) ≤ H := by rw [Real.coe_toNNReal _ hr0]; exact hrH
  rw [← hstat _ hle]
  exact (lintegral_map hg (hXm _)).symm

theorem dcl417_time_lint {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P] {N : ℕ}
    {X : ℝ≥0 → Ω → Config d N} {H : ℝ} {μ : Measure (Config d N)}
    (hXm : ∀ t : ℝ≥0, Measurable (X t))
    (hXj : Measurable (fun p : ℝ × Ω => ofNNRealTime X p.1 p.2))
    (hstat : ∀ t : ℝ≥0, (t : ℝ) ≤ H → P.map (X t) = μ)
    {g : Config d N → ℝ≥0∞} (hg : Measurable g) {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v)
    (hvH : v ≤ H) :
    ∫⁻ ω, (∫⁻ r in Set.Ioc u v, g (X r.toNNReal ω) ∂volume) ∂P
      = ENNReal.ofReal (v - u) * ∫⁻ x, g x ∂μ := by
  have hm : Measurable (fun p : Ω × ℝ => g (X p.2.toNNReal p.1)) :=
    hg.comp (hXj.comp measurable_swap)
  have h1 : ∀ r ∈ Set.Ioc u v, ∫⁻ ω, g (X r.toNNReal ω) ∂P = ∫⁻ x, g x ∂μ := fun r hr =>
    dcl417_lint_stat hXm hstat hg (by linarith [hr.1]) (by linarith [hr.2])
  have hsw := lintegral_lintegral_swap (μ := P) (ν := volume.restrict (Set.Ioc u v))
    (f := fun ω r => g (X r.toNNReal ω)) hm.aemeasurable
  rw [hsw, setLIntegral_congr_fun measurableSet_Ioc (fun r hr => h1 r hr), setLIntegral_const,
    Real.volume_Ioc, mul_comm]

theorem dcl417_enorm_interval (f : ℝ → ℝ) {u v : ℝ} (huv : u ≤ v) :
    ‖∫ r in u..v, f r‖ₑ ≤ ∫⁻ r in Set.Ioc u v, ‖f r‖ₑ := by
  rw [intervalIntegral.integral_of_le huv]
  exact enorm_integral_le_lintegral_enorm f

theorem dcl417_meas_time_int {Ω : Type*} [MeasurableSpace Ω] {N : ℕ}
    {X : ℝ≥0 → Ω → Config d N}
    (hXj : Measurable (fun p : ℝ × Ω => ofNNRealTime X p.1 p.2))
    {g : Config d N → ℝ} (hg : Measurable g) {u v : ℝ} (huv : u ≤ v) :
    Measurable (fun ω : Ω => ∫ r in u..v, g (X r.toNNReal ω)) := by
  have hm : Measurable (fun p : Ω × ℝ => g (X p.2.toNNReal p.1)) :=
    hg.comp (hXj.comp measurable_swap)
  have hsm := (hm.stronglyMeasurable).integral_prod_right' (ν := volume.restrict (Set.Ioc u v))
  have e : (fun ω : Ω => ∫ r in u..v, g (X r.toNNReal ω))
      = fun ω => ∫ r, g (X r.toNNReal ω) ∂(volume.restrict (Set.Ioc u v)) := by
    funext ω
    rw [intervalIntegral.integral_of_le huv]
  rw [e]
  exact hsm.measurable

theorem dcl417_aemeas_finset_sup {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (f : ℝ → Ω → ℝ≥0∞) (hf : ∀ v, AEMeasurable (f v) P) (T : Finset ℝ) :
    AEMeasurable (fun ω => T.sup (fun v => f v ω)) P := by
  induction T using Finset.induction_on with
  | empty => simp
  | insert a T ha ih =>
    have e : (fun ω => (insert a T).sup (fun v => f v ω))
        = fun ω => f a ω ⊔ T.sup (fun v => f v ω) := by
      funext ω
      rw [Finset.sup_insert]
    rw [e]
    exact (hf a).sup ih

theorem dcl417_aemeas_sup {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} (T : Finset ℝ)
    (f : ℝ → Ω → ℝ≥0∞) (hf : ∀ v, AEMeasurable (f v) P) :
    AEMeasurable (fun ω => ⨆ v ∈ T, f v ω) P := by
  have e : (fun ω => ⨆ v ∈ T, f v ω) = fun ω => T.sup (fun v => f v ω) := by
    funext ω
    rw [Finset.sup_eq_iSup]
  rw [e]
  exact dcl417_aemeas_finset_sup f hf T

theorem dcl417_subseq {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {Q : ℕ → Ω → ℝ≥0∞}
    (hQ : ∀ n, AEMeasurable (Q n) P)
    (hlim : Tendsto (fun n => ∫⁻ ω, Q n ω ∂P) atTop (𝓝 0)) :
    ∃ φ : ℕ → ℕ, StrictMono φ ∧ ∀ᵐ ω ∂P, Tendsto (fun k => Q (φ k) ω) atTop (𝓝 0) := by
  have hpos : ∀ m : ℕ, (0 : ℝ≥0∞) < (2⁻¹ : ℝ≥0∞) ^ m := fun m =>
    ENNReal.pow_pos (ENNReal.inv_pos.2 (by norm_num)) m
  have hev : ∀ m : ℕ, ∀ᶠ n in atTop, ∫⁻ ω, Q n ω ∂P < (2⁻¹ : ℝ≥0∞) ^ m := fun m =>
    hlim.eventually (Iio_mem_nhds (hpos m))
  obtain ⟨φ, hφ, hφb⟩ := Filter.extraction_forall_of_eventually hev
  refine ⟨φ, hφ, ?_⟩
  have hsum : ∑' m, (2⁻¹ : ℝ≥0∞) ^ m ≠ ⊤ := by
    rw [ENNReal.tsum_geometric, ENNReal.one_sub_inv_two, inv_inv]
    norm_num
  have hT : ∫⁻ ω, ∑' m, Q (φ m) ω ∂P ≠ ⊤ := by
    rw [lintegral_tsum fun m => (hQ (φ m))]
    refine ne_top_of_le_ne_top hsum ?_
    exact ENNReal.tsum_le_tsum fun m => (hφb m).le
  have hae : ∀ᵐ ω ∂P, ∑' m, Q (φ m) ω ≠ ⊤ :=
    (ae_lt_top' (AEMeasurable.tsum fun m => hQ (φ m)) hT).mono fun ω hω => hω.ne
  filter_upwards [hae] with ω hω
  exact ENNReal.tendsto_atTop_zero_of_tsum_ne_top hω

theorem dcl417_pt (x : ℕ → ℝ) (y : ℝ) (q : ℕ → ℝ≥0∞) (hq : Tendsto q atTop (𝓝 0))
    (hxq : ∀ k, ‖x k - y‖ₑ ≤ q k) :
    Tendsto (fun k => ENNReal.ofReal (x k ^ 2)) atTop (𝓝 (ENNReal.ofReal (y ^ 2))) := by
  have h1 : Tendsto (fun k => ‖x k - y‖ₑ) atTop (𝓝 0) :=
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hq
      (by intro k; exact zero_le) hxq
  have h3 : Tendsto (fun k => ‖x k - y‖) atTop (𝓝 0) := by
    have := (ENNReal.tendsto_toReal ENNReal.zero_ne_top).comp h1
    simp only [ENNReal.toReal_zero] at this
    refine this.congr fun k => ?_
    simp [← ofReal_norm_eq_enorm]
  have h2 : Tendsto x atTop (𝓝 y) := tendsto_iff_norm_sub_tendsto_zero.2 h3
  exact (ENNReal.continuous_ofReal.tendsto _).comp (h2.pow 2)

/-- Abstract Fatou step: the maximal inequality for a finite set of times passes to the limit along an
almost surely convergent subsequence (`lintegral_liminf_le'`). -/
theorem dcl417_fatou_core {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω}
    (R : ℕ → ℝ → Ω → ℝ) (R0 : ℝ → Ω → ℝ) (T : Finset ℝ)
    (hR : ∀ n v, AEMeasurable (R n v) P) (hR0 : ∀ v, AEMeasurable (R0 v) P)
    (hL1 : ∀ v ∈ T, Tendsto (fun n => ∫⁻ ω, ‖R n v ω - R0 v ω‖ₑ ∂P) atTop (𝓝 0))
    (B : ℕ → ℝ≥0∞) (L : ℝ≥0∞)
    (hB : ∀ n, ∫⁻ ω, ⨆ v ∈ T, ENNReal.ofReal (R n v ω ^ 2) ∂P ≤ B n)
    (hBL : Tendsto B atTop (𝓝 L)) :
    ∫⁻ ω, ⨆ v ∈ T, ENNReal.ofReal (R0 v ω ^ 2) ∂P ≤ L := by
  set Q : ℕ → Ω → ℝ≥0∞ := fun n ω => ∑ v ∈ T, ‖R n v ω - R0 v ω‖ₑ with hQdef
  have hQm : ∀ n, AEMeasurable (Q n) P := fun n =>
    Finset.aemeasurable_fun_sum _ fun v _ => ((hR n v).sub (hR0 v)).enorm
  have hQlim : Tendsto (fun n => ∫⁻ ω, Q n ω ∂P) atTop (𝓝 0) := by
    have e : ∀ n, ∫⁻ ω, Q n ω ∂P = ∑ v ∈ T, ∫⁻ ω, ‖R n v ω - R0 v ω‖ₑ ∂P := fun n =>
      lintegral_finsetSum' _ fun v _ => ((hR n v).sub (hR0 v)).enorm
    simp_rw [e]
    have := tendsto_finset_sum T (fun v hv => hL1 v hv)
    simpa using this
  obtain ⟨φ, hφ, hae⟩ := dcl417_subseq hQm hQlim
  have hpt : ∀ᵐ ω ∂P, ∀ v ∈ T, Tendsto (fun k => ENNReal.ofReal (R (φ k) v ω ^ 2)) atTop
      (𝓝 (ENNReal.ofReal (R0 v ω ^ 2))) := by
    refine (Filter.eventually_all_finset T).2 fun v hv => ?_
    filter_upwards [hae] with ω hω
    refine dcl417_pt (fun k => R (φ k) v ω) (R0 v ω) (fun k => Q (φ k) ω) hω fun k => ?_
    exact Finset.single_le_sum (f := fun w => ‖R (φ k) w ω - R0 w ω‖ₑ) (fun _ _ => zero_le) hv
  have hΨ : ∀ᵐ ω ∂P, ⨆ v ∈ T, ENNReal.ofReal (R0 v ω ^ 2)
      ≤ liminf (fun k => ⨆ v ∈ T, ENNReal.ofReal (R (φ k) v ω ^ 2)) atTop := by
    filter_upwards [hpt] with ω hω
    refine iSup₂_le fun v hv => ?_
    rw [← (hω v hv).liminf_eq]
    exact Filter.liminf_le_liminf (Eventually.of_forall fun k =>
      le_iSup₂ (f := fun w (_ : w ∈ T) => ENNReal.ofReal (R (φ k) w ω ^ 2)) v hv)
  calc ∫⁻ ω, ⨆ v ∈ T, ENNReal.ofReal (R0 v ω ^ 2) ∂P
      ≤ ∫⁻ ω, liminf (fun k => ⨆ v ∈ T, ENNReal.ofReal (R (φ k) v ω ^ 2)) atTop ∂P :=
        lintegral_mono_ae hΨ
    _ ≤ liminf (fun k => ∫⁻ ω, ⨆ v ∈ T, ENNReal.ofReal (R (φ k) v ω ^ 2) ∂P) atTop :=
        lintegral_liminf_le' fun k => dcl417_aemeas_sup T _ fun v =>
          ((hR (φ k) v).pow_const 2).ennreal_ofReal
    _ ≤ liminf (fun k => B (φ k)) atTop :=
        Filter.liminf_le_liminf (Eventually.of_forall fun k => hB (φ k))
    _ = L := (hBL.comp hφ.tendsto_atTop).liminf_eq


/-! ### Part 4: approximants, the `L¹` estimate, and the energy (Minkowski) step -/

theorem dcl417_meas_of_cdiff {N : ℕ} (Φ : Config d N → ℝ)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => Φ) 0)) : Measurable Φ := by
  have e : Φ = fun X : Config d N => configLift (fun _ => Φ) 0 (repC X) := by
    funext X
    exact congrArg Φ (mk_repC X).symm
  rw [e]
  exact (hΦ.continuous.measurable).comp measurable_repC

theorem dcl417_meas_particleGen {N : ℕ} {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β)
    (Φ : Config d N → ℝ)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => Φ) 0)) :
    Measurable (particleGen d s V β Φ) := by
  set D := PDE.mfData d s hs0 hsd V β hβ with hD
  have hV2 : Torus.IsCk 2 D.V := dyn417_isCk2 hV
  have hΦc := dyn417_isC12 Φ 0 hΦ
  have hm := measurable_fkeIto_clamp_config (T := 0) (le_refl (0 : ℝ)) D hV2 (fun _ => Φ) hΦc
  have hcomp : Measurable (fun X : Config d N => fkeIto D 0 (fun _ => Φ) (clampTI 0 0) (repC X)) :=
    hm.comp (measurable_const.prodMk measurable_id)
  have e : particleGen d s V β Φ
      = fun X : Config d N => fkeIto D 0 (fun _ => Φ) (clampTI 0 0) (repC X) := by
    funext X
    have h := dyn417_fkeIto_eq V β hβ D rfl rfl rfl rfl Φ hΦ 0 (clampTI 0 0) (repC X)
    rw [mk_repC] at h
    exact h.symm
  rw [e]
  exact hcomp

theorem dcl417_bound_particle {N : ℕ} {s : ℝ} (V : Torus d → ℝ) (hV : Torus.IsSmooth V)
    (β : ℝ) (hβ : 0 < β) (hs0 : 0 ≤ s) (hsd : s < d) (hN : 0 < N)
    (Φ : Config d N → ℝ)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => Φ) 0))
    {K : Set (Config d N)} (hK : IsCompact K) (hdisj : Disjoint K (collisionSet d N))
    (hsupp : ∀ Y, Y ∉ K → Φ Y = 0) :
    ∃ C : ℝ, ∀ Z : Config d N, ‖particleGen d s V β Φ Z‖ ≤ C := by
  set D := PDE.mfData d s hs0 hsd V β hβ with hD
  have hV2 : Torus.IsCk 2 D.V := dyn417_isCk2 hV
  have hΦc := dyn417_isC12 Φ 0 hΦ
  obtain ⟨C, hC⟩ := fkeIto_bound (le_refl (0 : ℝ)) D hN hV2 (fun _ => Φ) hΦc hK hdisj
    (fun r Y hY => hsupp Y hY)
  refine ⟨C, fun Z => ?_⟩
  have h := hC 0 ⟨le_refl _, le_refl _⟩ (repC Z)
  rw [dyn417_fkeIto_eq V β hβ D rfl rfl rfl rfl Φ hΦ 0 0 (repC Z), mk_repC] at h
  exact h

theorem dcl417_L1_of_L2 {N : ℕ} {μ : Measure (Config d N)} [IsProbabilityMeasure μ]
    {f : ℕ → Config d N → ℝ} (hfm : ∀ n, Measurable (f n))
    (hf : Tendsto (fun n => eLpNorm (f n) 2 μ) atTop (𝓝 0)) :
    Tendsto (fun n => ∫⁻ x, ‖f n x‖ₑ ∂μ) atTop (𝓝 0) := by
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hf
    (fun n => zero_le) fun n => ?_
  have h := eLpNorm_le_eLpNorm_of_exponent_le (μ := μ) (f := f n) (p := 1) (q := 2) (by norm_num)
  rwa [eLpNorm_one_eq_lintegral_enorm (hfm n).aestronglyMeasurable] at h

/-- The `L¹(μ)`-estimate of the remainder difference, along the path (stationarity, Tonelli). -/
theorem dcl417_L1_diff {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} {X : ℝ≥0 → Ω → Config d N} {H : ℝ} {μ : Measure (Config d N)}
    (hXm : ∀ t : ℝ≥0, Measurable (X t))
    (hXj : Measurable (fun p : ℝ × Ω => ofNNRealTime X p.1 p.2))
    (hstat : ∀ t : ℝ≥0, (t : ℝ) ≤ H → P.map (X t) = μ)
    {F Fn G Gn : Config d N → ℝ} (hF : Measurable F) (hFn : Measurable Fn)
    (hG : Measurable G) (hGn : Measurable Gn)
    {u v : ℝ} (hu : 0 ≤ u) (huv : u ≤ v) (hvH : v ≤ H)
    (hint : ∀ᵐ ω ∂P, IntervalIntegrable (fun r : ℝ => G (X r.toNNReal ω)) volume 0 H)
    (hintn : ∀ᵐ ω ∂P, IntervalIntegrable (fun r : ℝ => Gn (X r.toNNReal ω)) volume 0 H) :
    ∫⁻ ω, ‖(Fn (X v.toNNReal ω) - Fn (X u.toNNReal ω) - ∫ r in u..v, Gn (X r.toNNReal ω))
        - (F (X v.toNNReal ω) - F (X u.toNNReal ω) - ∫ r in u..v, G (X r.toNNReal ω))‖ₑ ∂P
      ≤ 2 * ∫⁻ x, ‖Fn x - F x‖ₑ ∂μ + ENNReal.ofReal (v - u) * ∫⁻ x, ‖Gn x - G x‖ₑ ∂μ := by
  have hH0 : 0 ≤ H := hu.trans (huv.trans hvH)
  have hsub : Set.uIcc u v ⊆ Set.uIcc 0 H := by
    rw [Set.uIcc_of_le hH0]
    exact Set.uIcc_subset_Icc ⟨hu, huv.trans hvH⟩ ⟨hu.trans huv, hvH⟩
  have hpt : ∀ᵐ ω ∂P, ‖(Fn (X v.toNNReal ω) - Fn (X u.toNNReal ω) - ∫ r in u..v, Gn (X r.toNNReal ω))
        - (F (X v.toNNReal ω) - F (X u.toNNReal ω) - ∫ r in u..v, G (X r.toNNReal ω))‖ₑ
      ≤ ‖Fn (X v.toNNReal ω) - F (X v.toNNReal ω)‖ₑ + ‖Fn (X u.toNNReal ω) - F (X u.toNNReal ω)‖ₑ
        + ∫⁻ r in Set.Ioc u v, ‖Gn (X r.toNNReal ω) - G (X r.toNNReal ω)‖ₑ := by
    filter_upwards [hint, hintn] with ω h1 h2
    have hi1 : IntervalIntegrable (fun r : ℝ => Gn (X r.toNNReal ω)) volume u v :=
      h2.mono_set hsub
    have hi2 : IntervalIntegrable (fun r : ℝ => G (X r.toNNReal ω)) volume u v :=
      h1.mono_set hsub
    have hsplit : ∫ r in u..v, (Gn (X r.toNNReal ω) - G (X r.toNNReal ω))
        = (∫ r in u..v, Gn (X r.toNNReal ω)) - ∫ r in u..v, G (X r.toNNReal ω) :=
      intervalIntegral.integral_sub hi1 hi2
    have e : (Fn (X v.toNNReal ω) - Fn (X u.toNNReal ω) - ∫ r in u..v, Gn (X r.toNNReal ω))
        - (F (X v.toNNReal ω) - F (X u.toNNReal ω) - ∫ r in u..v, G (X r.toNNReal ω))
        = (Fn (X v.toNNReal ω) - F (X v.toNNReal ω)) - (Fn (X u.toNNReal ω) - F (X u.toNNReal ω))
          - ∫ r in u..v, (Gn (X r.toNNReal ω) - G (X r.toNNReal ω)) := by
      rw [hsplit]
      ring
    rw [e]
    exact le_trans enorm_sub_le (add_le_add enorm_sub_le (dcl417_enorm_interval _ huv))
  have hf1 : Measurable (fun ω => ‖Fn (X v.toNNReal ω) - F (X v.toNNReal ω)‖ₑ) :=
    ((hFn.sub hF).enorm).comp (hXm _)
  have hf2 : Measurable (fun ω => ‖Fn (X u.toNNReal ω) - F (X u.toNNReal ω)‖ₑ) :=
    ((hFn.sub hF).enorm).comp (hXm _)
  have hf3 : Measurable (fun ω => ∫⁻ r in Set.Ioc u v, ‖Gn (X r.toNNReal ω) - G (X r.toNNReal ω)‖ₑ) := by
    have hm : Measurable (fun p : Ω × ℝ => ‖Gn (X p.2.toNNReal p.1) - G (X p.2.toNNReal p.1)‖ₑ) :=
      (((hGn.sub hG).enorm).comp (hXj.comp measurable_swap))
    exact hm.lintegral_prod_right'
  have hs1 : ∫⁻ ω, ‖Fn (X v.toNNReal ω) - F (X v.toNNReal ω)‖ₑ ∂P = ∫⁻ x, ‖Fn x - F x‖ₑ ∂μ :=
    dcl417_lint_stat (g := fun x => ‖Fn x - F x‖ₑ) hXm hstat ((hFn.sub hF).enorm) (by linarith) hvH
  have hs2 : ∫⁻ ω, ‖Fn (X u.toNNReal ω) - F (X u.toNNReal ω)‖ₑ ∂P = ∫⁻ x, ‖Fn x - F x‖ₑ ∂μ :=
    dcl417_lint_stat (g := fun x => ‖Fn x - F x‖ₑ) hXm hstat ((hFn.sub hF).enorm) hu
      (by linarith)
  have hs3 := dcl417_time_lint (μ := μ) hXm hXj hstat (g := fun x => ‖Gn x - G x‖ₑ)
    ((hGn.sub hG).enorm) hu huv hvH
  calc ∫⁻ ω, ‖(Fn (X v.toNNReal ω) - Fn (X u.toNNReal ω) - ∫ r in u..v, Gn (X r.toNNReal ω))
        - (F (X v.toNNReal ω) - F (X u.toNNReal ω) - ∫ r in u..v, G (X r.toNNReal ω))‖ₑ ∂P
      ≤ ∫⁻ ω, (‖Fn (X v.toNNReal ω) - F (X v.toNNReal ω)‖ₑ + ‖Fn (X u.toNNReal ω) - F (X u.toNNReal ω)‖ₑ
        + ∫⁻ r in Set.Ioc u v, ‖Gn (X r.toNNReal ω) - G (X r.toNNReal ω)‖ₑ) ∂P :=
        lintegral_mono_ae hpt
    _ = ∫⁻ ω, ‖Fn (X v.toNNReal ω) - F (X v.toNNReal ω)‖ₑ ∂P
        + ∫⁻ ω, ‖Fn (X u.toNNReal ω) - F (X u.toNNReal ω)‖ₑ ∂P
        + ∫⁻ ω, (∫⁻ r in Set.Ioc u v, ‖Gn (X r.toNNReal ω) - G (X r.toNNReal ω)‖ₑ) ∂P := by
        rw [lintegral_add_right _ hf3, lintegral_add_left hf1]
    _ = 2 * ∫⁻ x, ‖Fn x - F x‖ₑ ∂μ + ENNReal.ofReal (v - u) * ∫⁻ x, ‖Gn x - G x‖ₑ ∂μ := by
        rw [hs1, hs2, hs3, two_mul]

/-! ### Part 5: energies as functions of the configuration, and the Minkowski step -/

theorem dcl417_cg_repC {N : ℕ} (Φ : Config d N → ℝ) (X : Config d N) (i : Fin N) :
    configGrad Φ X i = configGrad Φ (fun j => Torus.mk (repC X j)) i := by
  rw [mk_repC]

theorem dcl417_c1_of_cdiff {N : ℕ} (Φ : Config d N → ℝ)
    (hΦ : ContDiff ℝ ((⊤ : ℕ∞) : WithTop ℕ∞) (configLift (fun _ => Φ) 0)) :
    ContDiffOn ℝ 1 (configLift (fun _ => Φ) 0) (coverFree d N) :=
  (hΦ.contDiffOn).of_le (by norm_num)

open Classical in
theorem dcl417_aemeas_repC {N : ℕ} {μ : Measure (Config d N)}
    (g : (Fin N → Euc d) → ℝ≥0∞) (hg : ContinuousOn g (coverFree d N))
    (hμ : ∀ᵐ X ∂μ, X ∉ collisionSet d N) (G : Config d N → ℝ≥0∞)
    (hG : ∀ X, G X = g (repC X)) : AEMeasurable G μ := by
  have hpw : Measurable ((coverFree d N).piecewise g (fun _ => (0 : ℝ≥0∞))) :=
    ContinuousOn.measurable_piecewise hg continuousOn_const dcl417_isOpen_coverFree.measurableSet
  have hm : Measurable (fun X : Config d N => (coverFree d N).piecewise g (fun _ => (0 : ℝ≥0∞)) (repC X)) :=
    hpw.comp measurable_repC
  refine hm.aemeasurable.congr ?_
  filter_upwards [hμ] with X hX
  have hc : repC X ∈ coverFree d N := by
    show (fun i => (Torus.mk (repC X i) : Torus d)) ∉ collisionSet d N
    rw [mk_repC]
    exact hX
  rw [hG X, Set.piecewise_eq_of_mem _ _ _ hc]

theorem dcl417_aemeas_energy {N : ℕ} {μ : Measure (Config d N)} (Φ : Config d N → ℝ)
    (hΦ : ContDiffOn ℝ 1 (configLift (fun _ => Φ) 0) (coverFree d N))
    (hμ : ∀ᵐ X ∂μ, X ∉ collisionSet d N) :
    AEMeasurable (fun X : Config d N => ∑ i, ‖configGrad Φ X i‖ₑ ^ 2) μ :=
  dcl417_aemeas_repC _ (dcl417_energy_cont Φ hΦ) hμ _ fun X => by
    show ∑ i, ‖configGrad Φ X i‖ₑ ^ 2 = ∑ i, ‖configGrad Φ (fun j => Torus.mk (repC X j)) i‖ₑ ^ 2
    rw [mk_repC]

theorem dcl417_diff_cont {N : ℕ} (Φ Ψ : Config d N → ℝ)
    (hΦ : ContDiffOn ℝ 1 (configLift (fun _ => Φ) 0) (coverFree d N))
    (hΨ : ContDiffOn ℝ 1 (configLift (fun _ => Ψ) 0) (coverFree d N)) :
    ContinuousOn (fun Y : Fin N → Euc d => ∑ i,
        ‖configGrad Φ (fun j => Torus.mk (Y j)) i - configGrad Ψ (fun j => Torus.mk (Y j)) i‖ₑ ^ 2)
      (coverFree d N) :=
  continuousOn_finset_sum _ fun i _ =>
    ((ENNReal.continuous_pow 2).comp_continuousOn
      (continuous_enorm.comp_continuousOn ((dcl417_gradY_cont Φ i hΦ).sub (dcl417_gradY_cont Ψ i hΨ))))

theorem dcl417_aemeas_diff {N : ℕ} {μ : Measure (Config d N)} (Φ Ψ : Config d N → ℝ)
    (hΦ : ContDiffOn ℝ 1 (configLift (fun _ => Φ) 0) (coverFree d N))
    (hΨ : ContDiffOn ℝ 1 (configLift (fun _ => Ψ) 0) (coverFree d N))
    (hμ : ∀ᵐ X ∂μ, X ∉ collisionSet d N) :
    AEMeasurable (fun X : Config d N => ∑ i, ‖configGrad Φ X i - configGrad Ψ X i‖ₑ ^ 2) μ :=
  dcl417_aemeas_repC _ (dcl417_diff_cont Φ Ψ hΦ hΨ) hμ _ fun X => by
    show ∑ i, ‖configGrad Φ X i - configGrad Ψ X i‖ₑ ^ 2
      = ∑ i, ‖configGrad Φ (fun j => Torus.mk (repC X j)) i
          - configGrad Ψ (fun j => Torus.mk (repC X j)) i‖ₑ ^ 2
    rw [mk_repC]

theorem dcl417_sq_half (x : ℝ≥0∞) : (x ^ (1 / 2 : ℝ)) ^ (2 : ℝ) = x := by
  rw [← ENNReal.rpow_mul]
  norm_num

theorem dcl417_top_sum {ι : Type*} [Fintype ι] (c : ι → ℝ≥0∞) (i : ι) (hi : c i = ⊤) :
    (∑ j, c j ^ (2 : ℝ)) ^ (1 / 2 : ℝ) = ⊤ := by
  have h1 : c i ^ (2 : ℝ) = ⊤ := by
    rw [hi]
    exact ENNReal.top_rpow_of_pos (by norm_num)
  have h2 : ∑ j, c j ^ (2 : ℝ) = ⊤ := by
    apply top_le_iff.1
    rw [← h1]
    exact Finset.single_le_sum (f := fun j => c j ^ (2 : ℝ)) (fun j _ => zero_le) (Finset.mem_univ i)
  rw [h2]
  exact ENNReal.top_rpow_of_pos (by norm_num)

/-- Finite Minkowski inequality for `ℓ²`-norms of `ℝ≥0∞`-valued finite families. -/
theorem dcl417_fin_mink {ι : Type*} [Fintype ι] (z a b : ι → ℝ≥0∞) (hz : ∀ i, z i ≤ a i + b i) :
    (∑ i, z i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) ≤ (∑ i, a i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
      + (∑ i, b i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) := by
  by_cases hfin : ∀ i, a i ≠ ⊤ ∧ b i ≠ ⊤
  · have ha : ∀ i, a i = (((a i).toNNReal : ℝ≥0) : ℝ≥0∞) := fun i =>
      (ENNReal.coe_toNNReal (hfin i).1).symm
    have hb : ∀ i, b i = (((b i).toNNReal : ℝ≥0) : ℝ≥0∞) := fun i =>
      (ENNReal.coe_toNNReal (hfin i).2).symm
    have hz' : ∀ i, z i ≤ ((((a i).toNNReal + (b i).toNNReal : ℝ≥0)) : ℝ≥0∞) := fun i => by
      rw [ENNReal.coe_add, ← ha i, ← hb i]
      exact hz i
    have hS : ∑ i, z i ^ (2 : ℝ)
        ≤ ((∑ i, ((a i).toNNReal + (b i).toNNReal) ^ (2 : ℝ) : ℝ≥0) : ℝ≥0∞) := by
      rw [ENNReal.coe_finset_sum]
      refine Finset.sum_le_sum fun i _ => ?_
      rw [ENNReal.coe_rpow_of_nonneg _ (by norm_num)]
      exact ENNReal.rpow_le_rpow (hz' i) (by norm_num)
    have h1 := ENNReal.rpow_le_rpow hS (show (0 : ℝ) ≤ 1 / 2 by norm_num)
    rw [← ENNReal.coe_rpow_of_nonneg _ (by norm_num)] at h1
    have h2 := NNReal.Lp_add_le Finset.univ (fun i => (a i).toNNReal) (fun i => (b i).toNNReal)
      (p := 2) (by norm_num)
    have ea : (∑ i, a i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        = ((∑ i, (a i).toNNReal ^ (2 : ℝ)) ^ (1 / 2 : ℝ) : ℝ≥0) := by
      rw [ENNReal.coe_rpow_of_nonneg _ (by norm_num), ENNReal.coe_finset_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.coe_rpow_of_nonneg _ (by norm_num), ← ha i]
    have eb : (∑ i, b i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)
        = ((∑ i, (b i).toNNReal ^ (2 : ℝ)) ^ (1 / 2 : ℝ) : ℝ≥0) := by
      rw [ENNReal.coe_rpow_of_nonneg _ (by norm_num), ENNReal.coe_finset_sum]
      congr 1
      refine Finset.sum_congr rfl fun i _ => ?_
      rw [ENNReal.coe_rpow_of_nonneg _ (by norm_num), ← hb i]
    rw [ea, eb, ← ENNReal.coe_add]
    exact h1.trans (by exact_mod_cast h2)
  · obtain ⟨i, hi⟩ := not_forall.1 hfin
    by_cases hai : a i = ⊤
    · rw [dcl417_top_sum a i hai, top_add]
      exact le_top
    · have hbi : b i = ⊤ := by
        by_contra h
        exact hi ⟨hai, h⟩
      rw [dcl417_top_sum b i hbi, add_top]
      exact le_top

/-- Minkowski inequality for the energies: the `L²(μ; ℓ²)`-triangle inequality for the squared
`ℓ²`-norms of a pointwise triangle inequality. -/
theorem dcl417_energy_mink {Ω ι : Type*} [MeasurableSpace Ω] [Fintype ι] {μ : Measure Ω}
    (z a b : Ω → ι → ℝ≥0∞) (hz : ∀ ω i, z ω i ≤ a ω i + b ω i)
    (ha : AEMeasurable (fun ω => ∑ i, a ω i ^ (2 : ℝ)) μ)
    (hb : AEMeasurable (fun ω => ∑ i, b ω i ^ (2 : ℝ)) μ) :
    ∫⁻ ω, ∑ i, z ω i ^ (2 : ℝ) ∂μ
      ≤ ((∫⁻ ω, ∑ i, a ω i ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)
          + (∫⁻ ω, ∑ i, b ω i ^ (2 : ℝ) ∂μ) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
  have hp : AEMeasurable (fun ω => (∑ i, a ω i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) μ := ha.pow_const _
  have hq : AEMeasurable (fun ω => (∑ i, b ω i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) μ := hb.pow_const _
  have hpt : ∀ ω, ∑ i, z ω i ^ (2 : ℝ)
      ≤ ((∑ i, a ω i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) + (∑ i, b ω i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := by
    intro ω
    rw [← dcl417_sq_half (∑ i, z ω i ^ (2 : ℝ))]
    exact ENNReal.rpow_le_rpow (dcl417_fin_mink (z ω) (a ω) (b ω) (hz ω)) (by norm_num)
  have hM := ENNReal.lintegral_Lp_add_le hp hq (p := 2) (by norm_num)
  have hpsq : ∫⁻ ω, ((∑ i, a ω i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μ
      = ∫⁻ ω, ∑ i, a ω i ^ (2 : ℝ) ∂μ :=
    lintegral_congr fun ω => dcl417_sq_half _
  have hqsq : ∫⁻ ω, ((∑ i, b ω i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μ
      = ∫⁻ ω, ∑ i, b ω i ^ (2 : ℝ) ∂μ :=
    lintegral_congr fun ω => dcl417_sq_half _
  rw [hpsq, hqsq] at hM
  calc ∫⁻ ω, ∑ i, z ω i ^ (2 : ℝ) ∂μ
      ≤ ∫⁻ ω, ((∑ i, a ω i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) + (∑ i, b ω i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μ :=
        lintegral_mono fun ω => hpt ω
    _ = ((∫⁻ ω, ((∑ i, a ω i ^ (2 : ℝ)) ^ (1 / 2 : ℝ) + (∑ i, b ω i ^ (2 : ℝ)) ^ (1 / 2 : ℝ)) ^ (2 : ℝ) ∂μ)
          ^ (1 / 2 : ℝ)) ^ (2 : ℝ) := (dcl417_sq_half _).symm
    _ ≤ _ := ENNReal.rpow_le_rpow (by simpa using hM) (by norm_num)

/-- Squares of the `ℝ≥0∞`-valued Minkowski bound: the square of `A + T` is controlled by the energy. -/
theorem dcl417_tendsto_sq (A : ℝ≥0∞) (T : ℕ → ℝ≥0∞) (hT : Tendsto T atTop (𝓝 0)) :
    Tendsto (fun n => (A + T n) ^ (2 : ℕ)) atTop (𝓝 (A ^ (2 : ℕ))) := by
  by_cases hA : A = ⊤
  · simp [hA]
  · have h1 : Tendsto (fun n => A + T n) atTop (𝓝 (A + 0)) :=
      tendsto_const_nhds.add hT
    rw [add_zero] at h1
    exact ((ENNReal.continuous_pow 2).tendsto A).comp h1 |>.congr' (Eventually.of_forall fun n => rfl)

/-! ### Part 6: a good event with continuous paths, joint measurability, conjuncts 1 and 2 -/

theorem dcl417_good {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}
    {X : ℝ≥0 → Ω → Config d N} {H : ℝ}
    (hcont : ∀ᵐ ω ∂P, ∀ i, Continuous fun t : ℝ≥0 => X t ω i)
    (hnc : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ H → X t ω ∉ collisionSet d N) :
    ∃ S : Set Ω, MeasurableSet S ∧ (∀ᵐ ω ∂P, ω ∈ S) ∧ ∀ ω ∈ S,
      (∀ i, Continuous fun t : ℝ≥0 => X t ω i) ∧ ∀ t : ℝ≥0, (t : ℝ) ≤ H → X t ω ∉ collisionSet d N := by
  have hp := hcont.and hnc
  have h0 : P {ω | ¬ ((∀ i, Continuous fun t : ℝ≥0 => X t ω i) ∧
      ∀ t : ℝ≥0, (t : ℝ) ≤ H → X t ω ∉ collisionSet d N)} = 0 := ae_iff.1 hp
  obtain ⟨S', hS't, hS'm, hS'0⟩ := exists_measurable_superset_of_null h0
  refine ⟨S'ᶜ, hS'm.compl, ?_, ?_⟩
  · rw [ae_iff]
    simpa using hS'0
  · intro ω hω
    by_contra hbad
    exact hω (hS't hbad)

theorem dcl417_joint {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (Y : ℝ≥0 → Ω → Config d N)
    (hYm : ∀ t, Measurable (Y t)) (hYc : ∀ ω i, Continuous fun t : ℝ≥0 => Y t ω i) :
    Measurable (fun p : ℝ × Ω => Y p.1.toNNReal p.2) := by
  refine measurable_pi_iff.2 fun i => ?_
  exact measurable_uncurry_of_continuous_of_measurable
    (u := fun (r : ℝ) (ω : Ω) => Y r.toNNReal ω i)
    (fun ω => (hYc ω i).comp continuous_real_toNNReal)
    (fun r => (measurable_pi_apply i).comp (hYm _))

theorem dcl417_path_meas {Ω : Type*} {N : ℕ} (Y : ℝ≥0 → Ω → Config d N)
    (hYc : ∀ ω i, Continuous fun t : ℝ≥0 => Y t ω i) (ω : Ω) :
    Measurable (fun r : ℝ => Y r.toNNReal ω) :=
  measurable_pi_iff.2 fun i => ((hYc ω i).comp continuous_real_toNNReal).measurable

theorem dcl417_meas_time_lint {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (Y : ℝ≥0 → Ω → Config d N)
    (hYj : Measurable (fun p : ℝ × Ω => Y p.1.toNNReal p.2))
    {g : Config d N → ℝ≥0∞} (hg : Measurable g) (u v : ℝ) :
    Measurable (fun ω : Ω => ∫⁻ r in Set.Ioc u v, g (Y r.toNNReal ω)) := by
  have hm : Measurable (fun p : Ω × ℝ => g (Y p.2.toNNReal p.1)) :=
    hg.comp (hYj.comp measurable_swap)
  exact hm.lintegral_prod_right'

theorem dcl417_meas_time_int' {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} (X : ℝ≥0 → Ω → Config d N)
    (hXj : Measurable (fun p : ℝ × Ω => X p.1.toNNReal p.2))
    {g : Config d N → ℝ} (hg : Measurable g) (u v : ℝ) :
    Measurable (fun ω : Ω => ∫ r in u..v, g (X r.toNNReal ω)) := by
  rcases le_total u v with huv | huv
  · exact dcl417_meas_time_int hXj hg huv
  · have e : (fun ω : Ω => ∫ r in u..v, g (X r.toNNReal ω))
        = fun ω => -∫ r in v..u, g (X r.toNNReal ω) := by
      funext ω
      rw [intervalIntegral.integral_symm]
    rw [e]
    exact (dcl417_meas_time_int hXj hg huv).neg

/-- Conjuncts 1 and 2 of the closed-generator Dynkin formula, for a process with continuous paths,
off-collision paths up to time `H`, and an integrable generator value. -/
theorem dcl417_conj12 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} {Y : ℝ≥0 → Ω → Config d N} {H : ℝ} {μ : Measure (Config d N)} (hH0 : 0 ≤ H)
    (hYm : ∀ t, Measurable (Y t))
    (hYc : ∀ ω i, Continuous fun t : ℝ≥0 => Y t ω i)
    (hYnc : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ H → Y t ω ∉ collisionSet d N)
    (hstat : ∀ t : ℝ≥0, (t : ℝ) ≤ H → P.map (Y t) = μ)
    {F G : Config d N → ℝ} (hF : ContinuousOn F (collisionSet d N)ᶜ) (hG : Measurable G)
    (hGint : ∫⁻ x, ‖G x‖ₑ ∂μ ≠ ⊤) :
    (∀ᵐ ω ∂P, IntervalIntegrable (fun r : ℝ => G (Y r.toNNReal ω)) volume 0 H) ∧
    (∀ᵐ ω ∂P, ContinuousOn (fun t : ℝ => F (Y t.toNNReal ω) - F (Y 0 ω) -
        ∫ r in (0 : ℝ)..t, G (Y r.toNNReal ω)) (Set.Icc 0 H)) := by
  have hYj := dcl417_joint Y hYm hYc
  have hint := dcl417_time_lint (μ := μ) hYm hYj hstat (g := fun x => ‖G x‖ₑ) hG.enorm
    (le_refl (0 : ℝ)) hH0 le_rfl
  have hmeasT := dcl417_meas_time_lint Y hYj (hG.enorm) 0 H
  have hfin : ∀ᵐ ω ∂P, ∫⁻ r in Set.Ioc 0 H, ‖G (Y r.toNNReal ω)‖ₑ < ⊤ := by
    refine ae_lt_top' hmeasT.aemeasurable ?_
    rw [hint]
    exact ENNReal.mul_ne_top ENNReal.ofReal_ne_top hGint
  have hI1 : ∀ᵐ ω ∂P, IntervalIntegrable (fun r : ℝ => G (Y r.toNNReal ω)) volume 0 H := by
    filter_upwards [hfin] with ω hω
    rw [intervalIntegrable_iff_integrableOn_Ioc_of_le hH0]
    have hmr : Measurable (fun r : ℝ => G (Y r.toNNReal ω)) := hG.comp (dcl417_path_meas Y hYc ω)
    exact ⟨hmr.aestronglyMeasurable, hω⟩
  refine ⟨hI1, ?_⟩
  filter_upwards [hI1, hYnc] with ω hω1 hω2
  have hpath : ContinuousOn (fun t : ℝ => Y t.toNNReal ω) (Set.Icc 0 H) :=
    (continuous_pi fun i => (hYc ω i).comp continuous_real_toNNReal).continuousOn
  have hFY : ContinuousOn (fun t : ℝ => F (Y t.toNNReal ω)) (Set.Icc 0 H) := by
    refine ContinuousOn.comp hF hpath ?_
    intro t ht
    show Y t.toNNReal ω ∈ (collisionSet d N)ᶜ
    exact hω2 _ (by rw [Real.coe_toNNReal _ ht.1]; exact ht.2)
  have hI : ContinuousOn (fun t : ℝ => ∫ r in (0 : ℝ)..t, G (Y r.toNNReal ω)) (Set.Icc 0 H) := by
    have hI1' : IntegrableOn (fun r : ℝ => G (Y r.toNNReal ω)) (Set.uIcc 0 H) := by
      rw [Set.uIcc_of_le hH0]
      exact (intervalIntegrable_iff_integrableOn_Icc_of_le hH0).1 hω1
    have := intervalIntegral.continuousOn_primitive_interval (a := (0 : ℝ)) (b := H) hI1'
    rwa [Set.uIcc_of_le hH0] at this
  exact (hFY.sub continuousOn_const).sub hI

/-! ### Part 7: the maximal inequality (conjunct 3) by Fatou and a directed supremum -/

open Classical in
theorem dcl417_conj3 {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsProbabilityMeasure P]
    {N : ℕ} {X : ℝ≥0 → Ω → Config d N} {H β : ℝ} {μ : Measure (Config d N)} (hH0 : 0 ≤ H)
    (hXm : ∀ t, Measurable (X t)) (hXj : Measurable (fun p : ℝ × Ω => X p.1.toNNReal p.2))
    (hstat : ∀ t : ℝ≥0, (t : ℝ) ≤ H → P.map (X t) = μ)
    {F G : Config d N → ℝ} (hF : Measurable F) (hG : Measurable G)
    (Fn Gn : ℕ → Config d N → ℝ) (hFn : ∀ n, Measurable (Fn n)) (hGn : ∀ n, Measurable (Gn n))
    (hintF : ∀ᵐ ω ∂P, IntervalIntegrable (fun r : ℝ => G (X r.toNNReal ω)) volume 0 H)
    (hintn : ∀ n, ∀ᵐ ω ∂P, IntervalIntegrable (fun r : ℝ => Gn n (X r.toNNReal ω)) volume 0 H)
    (hdom : ∀ n, ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ H →
      ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal
          ((Fn n (X v.toNNReal ω) - Fn n (X u.toNNReal ω) - ∫ r in u..v, Gn n (X r.toNNReal ω)) ^ 2) ∂P ≤
        ENNReal.ofReal (8 * β⁻¹ * (t - u)) * ∫⁻ Y, ∑ i, ‖configGrad (Fn n) Y i‖ₑ ^ 2 ∂μ)
    (hconv1 : Tendsto (fun n => ∫⁻ x, ‖Fn n x - F x‖ₑ ∂μ) atTop (𝓝 0))
    (hconv2 : Tendsto (fun n => ∫⁻ x, ‖Gn n x - G x‖ₑ ∂μ) atTop (𝓝 0))
    (hEF : AEMeasurable (fun Y : Config d N => ∑ i, ‖configGrad F Y i‖ₑ ^ 2) μ)
    (hED : ∀ n, AEMeasurable (fun Y : Config d N => ∑ i, ‖configGrad (Fn n) Y i - configGrad F Y i‖ₑ ^ 2) μ)
    (hE : Tendsto (fun n => ∫⁻ Y, ∑ i, ‖configGrad (Fn n) Y i - configGrad F Y i‖ₑ ^ 2 ∂μ) atTop (𝓝 0))
    (u t : ℝ) (hu : 0 ≤ u) (hut : u ≤ t) (htH : t ≤ H) :
    ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal
        ((F (X v.toNNReal ω) - F (X u.toNNReal ω) - ∫ r in u..v, G (X r.toNNReal ω)) ^ 2) ∂P ≤
      ENNReal.ofReal (8 * β⁻¹ * (t - u)) * ∫⁻ Y, ∑ i, ‖configGrad F Y i‖ₑ ^ 2 ∂μ := by
  set S := ratTimes u (t - u) with hS
  have hSsub : ∀ v ∈ S, u ≤ v ∧ v ≤ H := by
    intro v hv
    obtain ⟨⟨h1, h2⟩, _⟩ := hv
    exact ⟨h1, by linarith⟩
  set c := ENNReal.ofReal (8 * β⁻¹ * (t - u)) with hc
  set E := ∫⁻ Y, ∑ i, ‖configGrad F Y i‖ₑ ^ 2 ∂μ with hEdef
  set A := E ^ (1 / 2 : ℝ) with hAdef
  set T : ℕ → ℝ≥0∞ := fun n => (∫⁻ Y, ∑ i, ‖configGrad (Fn n) Y i - configGrad F Y i‖ₑ ^ 2 ∂μ) ^ (1 / 2 : ℝ)
    with hTdef
  -- the energy bound: the `L²` triangle inequality for the gradients
  have hMink : ∀ n, ∫⁻ Y, ∑ i, ‖configGrad (Fn n) Y i‖ₑ ^ 2 ∂μ ≤ (A + T n) ^ 2 := by
    intro n
    have htri : ∀ (Y : Config d N) (i : Fin N),
        ‖configGrad (Fn n) Y i‖ₑ ≤ ‖configGrad F Y i‖ₑ + ‖configGrad (Fn n) Y i - configGrad F Y i‖ₑ := by
      intro Y i
      calc ‖configGrad (Fn n) Y i‖ₑ
          = ‖configGrad F Y i + (configGrad (Fn n) Y i - configGrad F Y i)‖ₑ := by
            rw [add_sub_cancel]
        _ ≤ _ := enorm_add_le _ _
    have hm := dcl417_energy_mink (μ := μ)
      (fun Y i => ‖configGrad (Fn n) Y i‖ₑ) (fun Y i => ‖configGrad F Y i‖ₑ)
      (fun Y i => ‖configGrad (Fn n) Y i - configGrad F Y i‖ₑ) htri
      (by simp only [ENNReal.rpow_two]; exact hEF) (by simp only [ENNReal.rpow_two]; exact hED n)
    simp only [ENNReal.rpow_two] at hm
    exact hm
  have hT : Tendsto T atTop (𝓝 0) := by
    have h := ((ENNReal.continuous_rpow_const (y := 1 / 2)).tendsto (0 : ℝ≥0∞)).comp hE
    rw [ENNReal.zero_rpow_of_pos (by norm_num)] at h
    exact h
  have hA2 : A ^ (2 : ℕ) = E := by
    rw [← ENNReal.rpow_natCast]
    exact_mod_cast dcl417_sq_half E
  have hBL : Tendsto (fun n => c * (A + T n) ^ (2 : ℕ)) atTop (𝓝 (c * E)) := by
    have h1 := ENNReal.Tendsto.const_mul (a := c) (dcl417_tendsto_sq A T hT)
      (Or.inr (ENNReal.ofReal_ne_top (r := 8 * β⁻¹ * (t - u))))
    rw [hA2] at h1
    exact h1
  -- the Fatou step for a finite set of times
  let R : ℕ → ℝ → Ω → ℝ := fun n v ω =>
    Fn n (X v.toNNReal ω) - Fn n (X u.toNNReal ω) - ∫ r in u..v, Gn n (X r.toNNReal ω)
  let R0 : ℝ → Ω → ℝ := fun v ω =>
    F (X v.toNNReal ω) - F (X u.toNNReal ω) - ∫ r in u..v, G (X r.toNNReal ω)
  have hR : ∀ n v, AEMeasurable (R n v) P := fun n v =>
    ((((hFn n).comp (hXm _)).sub ((hFn n).comp (hXm _))).sub
      (dcl417_meas_time_int' X hXj (hGn n) u v)).aemeasurable
  have hR0 : ∀ v, AEMeasurable (R0 v) P := fun v =>
    ((((hF.comp (hXm _)).sub (hF.comp (hXm _))).sub
      (dcl417_meas_time_int' X hXj hG u v))).aemeasurable
  have hfin : ∀ Tr : Finset ℝ, (↑Tr ⊆ S) →
      ∫⁻ ω, ⨆ v ∈ Tr, ENNReal.ofReal (R0 v ω ^ 2) ∂P ≤ c * E := by
    intro Tr hTr
    have hB : ∀ n, ∫⁻ ω, ⨆ v ∈ Tr, ENNReal.ofReal (R n v ω ^ 2) ∂P ≤ c * (A + T n) ^ (2 : ℕ) := by
      intro n
      calc ∫⁻ ω, ⨆ v ∈ Tr, ENNReal.ofReal (R n v ω ^ 2) ∂P
          ≤ ∫⁻ ω, ⨆ v ∈ S, ENNReal.ofReal
              ((Fn n (X v.toNNReal ω) - Fn n (X u.toNNReal ω) - ∫ r in u..v, Gn n (X r.toNNReal ω)) ^ 2) ∂P :=
            lintegral_mono fun ω => iSup₂_le fun v hv => le_iSup₂_of_le v (hTr hv) le_rfl
        _ ≤ c * ∫⁻ Y, ∑ i, ‖configGrad (Fn n) Y i‖ₑ ^ 2 ∂μ := hdom n u t hu hut htH
        _ ≤ c * (A + T n) ^ (2 : ℕ) := mul_le_mul_of_nonneg_left (hMink n) zero_le
    have hL1 : ∀ v ∈ Tr, Tendsto (fun n => ∫⁻ ω, ‖R n v ω - R0 v ω‖ₑ ∂P) atTop (𝓝 0) := by
      intro v hv
      obtain ⟨hu', hvH⟩ := hSsub v (hTr (Finset.mem_coe.2 hv))
      have hb : ∀ n, ∫⁻ ω, ‖R n v ω - R0 v ω‖ₑ ∂P
          ≤ 2 * ∫⁻ x, ‖Fn n x - F x‖ₑ ∂μ + ENNReal.ofReal (v - u) * ∫⁻ x, ‖Gn n x - G x‖ₑ ∂μ :=
        fun n => dcl417_L1_diff hXm hXj hstat hF (hFn n) hG (hGn n) hu hu' hvH hintF (hintn n)
      have hsum := (ENNReal.Tendsto.const_mul hconv1 (Or.inr (show (2 : ℝ≥0∞) ≠ ⊤ by norm_num))).add
        (ENNReal.Tendsto.const_mul hconv2 (Or.inr (ENNReal.ofReal_ne_top (r := v - u))))
      simp only [mul_zero, add_zero] at hsum
      exact tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds hsum
        (fun n => zero_le) hb
    have hR0m : ∀ v, AEMeasurable (fun ω => ENNReal.ofReal (R0 v ω ^ 2)) P :=
      fun v => ((hR0 v).pow_const 2).ennreal_ofReal
    exact dcl417_fatou_core R R0 Tr hR hR0 hL1 (fun n => c * (A + T n) ^ (2 : ℕ)) (c * E) hB hBL
  -- the directed family of finite sets of rational times
  let Tr : Finset ℚ → Finset ℝ := fun Tq =>
    (Tq.filter (fun q : ℚ => (q : ℝ) ∈ S)).image (fun q : ℚ => (q : ℝ))
  let Gq : Finset ℚ → Ω → ℝ≥0∞ := fun Tq ω => ⨆ v ∈ Tr Tq, ENNReal.ofReal (R0 v ω ^ 2)
  have hGm : ∀ Tq, AEMeasurable (Gq Tq) P := fun Tq =>
    dcl417_aemeas_sup (Tr Tq) (fun v ω => ENNReal.ofReal (R0 v ω ^ 2))
      (fun v => ((hR0 v).pow_const 2).ennreal_ofReal)
  have hsubTr : ∀ Tq Tq' : Finset ℚ, Tq ⊆ Tq' → ∀ v ∈ Tr Tq, v ∈ Tr Tq' := by
    intro Tq Tq' h v hv
    obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 hv
    exact Finset.mem_image.2 ⟨q, Finset.mem_filter.2 ⟨h (Finset.mem_filter.1 hq).1,
      (Finset.mem_filter.1 hq).2⟩, rfl⟩
  have hdir : Directed (· ≤ ·) Gq := fun Tq1 Tq2 =>
    ⟨Tq1 ∪ Tq2, fun ω => iSup₂_le fun v hv => le_iSup₂_of_le v (hsubTr _ _ Finset.subset_union_left v hv) le_rfl,
      fun ω => iSup₂_le fun v hv => le_iSup₂_of_le v (hsubTr _ _ Finset.subset_union_right v hv) le_rfl⟩
  have hpt : ∀ ω, ⨆ v ∈ S, ENNReal.ofReal (R0 v ω ^ 2) ≤ ⨆ Tq, Gq Tq ω := by
    intro ω
    refine iSup₂_le fun v hv => ?_
    obtain ⟨_, q, hq⟩ := id hv
    refine le_iSup_of_le ({q} : Finset ℚ) ?_
    refine le_iSup₂_of_le v ?_ le_rfl
    exact Finset.mem_image.2 ⟨q, Finset.mem_filter.2 ⟨Finset.mem_singleton_self q, by rw [hq]; exact hv⟩, hq⟩
  calc ∫⁻ ω, ⨆ v ∈ S, ENNReal.ofReal (R0 v ω ^ 2) ∂P
      ≤ ∫⁻ ω, ⨆ Tq, Gq Tq ω ∂P := lintegral_mono fun ω => hpt ω
    _ = ⨆ Tq, ∫⁻ ω, Gq Tq ω ∂P := lintegral_iSup_directed hGm hdir
    _ ≤ c * E := by
        refine iSup_le fun Tq => hfin (Tr Tq) ?_
        intro v hv
        obtain ⟨q, hq, rfl⟩ := Finset.mem_image.1 (Finset.mem_coe.1 hv)
        exact (Finset.mem_filter.1 hq).2

/-! ### Part 8: the closed-generator Dynkin formula (statement copied from `HRS/ME/Spec417.lean`) -/

theorem dynkin_closedGenerator_proof (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (β : ℝ) (hβ : 0 < β) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type*} [MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → Config d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → Config d N) (H : ℝ)
    (hflow : IsStationaryGibbsFlow P s hs0 hsd V β hβ H X₀ W X)
    (F G : Config d N → ℝ) (hFm : Measurable F) (hGm : Measurable G)
    (hFc : ContDiffOn ℝ 1 (configLift (fun _ => F) 0) (coverFree d N))
    (hFG : MD.DOM.IsInClosedGenerator d s V β (canonicalGibbs (periodicRiesz d s) V N β) F G) :
    (∀ᵐ ω ∂P, IntervalIntegrable (fun r : ℝ => G (X r.toNNReal ω)) volume 0 H) ∧
    (∀ᵐ ω ∂P, ContinuousOn (fun t : ℝ => F (X t.toNNReal ω) - F (X 0 ω) -
        ∫ r in (0 : ℝ)..t, G (X r.toNNReal ω)) (Set.Icc 0 H)) ∧
    (∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ H →
      ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal
          ((F (X v.toNNReal ω) - F (X u.toNNReal ω) -
            ∫ r in u..v, G (X r.toNNReal ω)) ^ 2) ∂P ≤
        ENNReal.ofReal (8 * β⁻¹ * (t - u)) *
          ∫⁻ Y, ∑ i, ‖configGrad F Y i‖ₑ ^ 2 ∂(canonicalGibbs (periodicRiesz d s) V N β)) := by
  rcases lt_or_ge H 0 with hH | hH0
  · -- H < 0: the integrand is constant on `Ioc H 0`, `Icc 0 H` is empty, and `u ≤ t ≤ H < 0 ≤ u` is impossible.
    refine ⟨?_, ?_, ?_⟩
    · refine Filter.Eventually.of_forall fun ω => ?_
      refine (intervalIntegrable_congr (μ := volume) (f := fun r : ℝ => G (X r.toNNReal ω))
        (g := fun _ : ℝ => G (X 0 ω)) ?_).2 intervalIntegrable_const
      intro r hr
      rw [Set.uIoc_of_ge hH.le] at hr
      show G (X r.toNNReal ω) = G (X 0 ω)
      rw [Real.toNNReal_of_nonpos hr.2]
    · rw [Set.Icc_eq_empty (not_le.2 hH)]
      exact Filter.Eventually.of_forall fun ω => continuousOn_empty _
    · intro u t hu hut htH
      exfalso
      linarith
  -- `H ≥ 0`
  have hstrong : IsStrongSolution P (PDE.mfData d s hs0 hsd V β hβ) H X₀ W X := by
    rcases hflow.flow.flow with h | h
    · exact h.1
    · exact absurd h.1 (by omega)
  have hstat0 := HRS.MD.Stat.md_stat_gibbs_flow_stationary_proof hd hs0 hsd V hV β hβ H hN P X₀ W X hflow
  set μ := canonicalGibbs (periodicRiesz d s) V N β with hμdef
  have hμprob : IsProbabilityMeasure μ := by
    rw [← hstat0 0 (by simpa using hH0)]
    infer_instance
  haveI := hμprob
  have hμnc : ∀ᵐ Y ∂μ, Y ∉ collisionSet d N :=
    HRS.Q84d.q84d_gibbs_ac.ae_le (HRS.Q84d.q84d_ae_not_collision (N := N) (d := d) (by omega))
  -- the good event and the modification `Xt` of `X` (equal to `X` on the good event)
  obtain ⟨S, hSm, hSae, hSprop⟩ := dcl417_good hstrong.cont hstrong.no_collision
  let Xt : ℝ≥0 → Ω → Config d N := fun t => S.indicator (X t)
  have hXt_eq : ∀ ω ∈ S, ∀ t : ℝ≥0, Xt t ω = X t ω := fun ω hω t => Set.indicator_of_mem hω _
  have hXtm : ∀ t, Measurable (Xt t) := fun t => (hstrong.adapted t).indicator hSm
  have hXtc : ∀ ω i, Continuous fun t : ℝ≥0 => Xt t ω i := by
    intro ω i
    by_cases hω : ω ∈ S
    · have e : (fun t : ℝ≥0 => Xt t ω i) = fun t => X t ω i :=
        funext fun t => by rw [hXt_eq ω hω t]
      rw [e]
      exact (hSprop ω hω).1 i
    · have e : (fun t : ℝ≥0 => Xt t ω i) = fun _ => (0 : Torus d) :=
        funext fun t => by simp [Xt, hω]
      rw [e]
      exact continuous_const
  have hXtj : Measurable (fun p : ℝ × Ω => Xt p.1.toNNReal p.2) := dcl417_joint Xt hXtm hXtc
  have hXtnc : ∀ᵐ ω ∂P, ∀ t : ℝ≥0, (t : ℝ) ≤ H → Xt t ω ∉ collisionSet d N := by
    filter_upwards [hSae] with ω hω
    intro t ht
    rw [hXt_eq ω hω t]
    exact (hSprop ω hω).2 t ht
  have hstatT : ∀ t : ℝ≥0, (t : ℝ) ≤ H → P.map (Xt t) = μ := by
    intro t ht
    rw [← hstat0 t ht]
    apply Measure.map_congr
    filter_upwards [hSae] with ω hω
    exact hXt_eq ω hω t
  have hFcont : ContinuousOn F (collisionSet d N)ᶜ :=
    dcl417_continuousOn_compl F
      (hFc.continuousOn : ContinuousOn (fun Y : Fin N → Euc d => F (fun i => Torus.mk (Y i))) (coverFree d N))
  -- approximants
  obtain ⟨Fn, hFnC, hFn1, hFn2, hFn3⟩ := hFG
  have hFnm : ∀ n, Measurable (Fn n) := fun n => dcl417_meas_of_cdiff (Fn n) (hFnC n).1
  have hGnm : ∀ n, Measurable (fun Y : Config d N => particleGen d s V β (Fn n) Y) := fun n =>
    dcl417_meas_particleGen hs0 hsd V hV β hβ (Fn n) (hFnC n).1
  have hsm := fun n => dynkin_smooth_proof hd hs0 hsd V hV β hβ hN P X₀ W X H hflow (Fn n) (hFnm n)
    (hFnC n).1 (hFnC n).2
  have hsm1 : ∀ n, ∀ᵐ ω ∂P, IntervalIntegrable
      (fun r : ℝ => particleGen d s V β (Fn n) (Xt r.toNNReal ω)) volume 0 H := fun n => by
    filter_upwards [(hsm n).1, hSae] with ω h1 hω
    have e : (fun r : ℝ => particleGen d s V β (Fn n) (Xt r.toNNReal ω))
        = fun r => particleGen d s V β (Fn n) (X r.toNNReal ω) := by
      funext r
      rw [hXt_eq ω hω]
    rw [e]
    exact h1
  have hdomT : ∀ n, ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ H →
      ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal
          ((Fn n (Xt v.toNNReal ω) - Fn n (Xt u.toNNReal ω) -
            ∫ r in u..v, particleGen d s V β (Fn n) (Xt r.toNNReal ω)) ^ 2) ∂P ≤
        ENNReal.ofReal (8 * β⁻¹ * (t - u)) * ∫⁻ Y, ∑ i, ‖configGrad (Fn n) Y i‖ₑ ^ 2 ∂μ := by
    intro n u t hu hut htH
    have h := (hsm n).2.2 u t hu hut htH
    refine (lintegral_congr_ae ?_).trans_le h
    filter_upwards [hSae] with ω hω
    simp only [hXt_eq ω hω]
  have hconv1 : Tendsto (fun n => ∫⁻ x, ‖Fn n x - F x‖ₑ ∂μ) atTop (𝓝 0) :=
    dcl417_L1_of_L2 (f := fun n x => Fn n x - F x) (fun n => (hFnm n).sub hFm) hFn1
  have hconv2 : Tendsto (fun n => ∫⁻ x, ‖particleGen d s V β (Fn n) x - G x‖ₑ ∂μ) atTop (𝓝 0) :=
    dcl417_L1_of_L2 (f := fun n x => particleGen d s V β (Fn n) x - G x)
      (fun n => (hGnm n).sub hGm) hFn2
  have hEF : AEMeasurable (fun Y : Config d N => ∑ i, ‖configGrad F Y i‖ₑ ^ 2) μ :=
    dcl417_aemeas_energy F hFc hμnc
  have hED : ∀ n, AEMeasurable (fun Y : Config d N => ∑ i, ‖configGrad (Fn n) Y i - configGrad F Y i‖ₑ ^ 2) μ :=
    fun n => dcl417_aemeas_diff (Fn n) F (dcl417_c1_of_cdiff _ (hFnC n).1) hFc hμnc
  -- `G ∈ L¹(μ)`: an `L¹`-limit of uniformly bounded functions
  have hGint : ∫⁻ x, ‖G x‖ₑ ∂μ ≠ ⊤ := by
    obtain ⟨n, hn⟩ := (hconv2.eventually (Iio_mem_nhds (show (0 : ℝ≥0∞) < 1 by norm_num))).exists
    obtain ⟨K, hKc, hKd, hKs⟩ := (hFnC n).2
    obtain ⟨C, hC⟩ := dcl417_bound_particle V hV β hβ hs0 hsd (by omega) (Fn n) (hFnC n).1 hKc hKd hKs
    have hbd : ∫⁻ x, ‖particleGen d s V β (Fn n) x‖ₑ ∂μ ≤ ENNReal.ofReal C := by
      calc ∫⁻ x, ‖particleGen d s V β (Fn n) x‖ₑ ∂μ ≤ ∫⁻ _x, ENNReal.ofReal C ∂μ := by
            refine lintegral_mono fun x => ?_
            rw [Real.enorm_eq_ofReal_abs]
            exact ENNReal.ofReal_le_ofReal ((le_abs_self _).trans (by simpa [Real.norm_eq_abs] using hC x))
        _ = ENNReal.ofReal C := by simp
    have hsplit : ∫⁻ x, ‖G x‖ₑ ∂μ
        ≤ ∫⁻ x, ‖particleGen d s V β (Fn n) x‖ₑ ∂μ + ∫⁻ x, ‖particleGen d s V β (Fn n) x - G x‖ₑ ∂μ := by
      rw [← lintegral_add_left (hGnm n).enorm]
      refine lintegral_mono fun x => ?_
      calc ‖G x‖ₑ = ‖particleGen d s V β (Fn n) x - (particleGen d s V β (Fn n) x - G x)‖ₑ := by
            rw [sub_sub_cancel]
        _ ≤ _ := enorm_sub_le
    refine ne_top_of_le_ne_top ?_ hsplit
    exact ENNReal.add_ne_top.2 ⟨ne_top_of_le_ne_top ENNReal.ofReal_ne_top hbd, ne_top_of_lt hn⟩
  -- conjuncts 1 and 2 for `F` along `Xt`, and conjunct 3 along `Xt`
  obtain ⟨hcF1, hcF2⟩ := dcl417_conj12 hH0 hXtm hXtc hXtnc hstatT hFcont hGm hGint
  have hc3 : ∀ u t : ℝ, 0 ≤ u → u ≤ t → t ≤ H →
      ∫⁻ ω, ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal
          ((F (Xt v.toNNReal ω) - F (Xt u.toNNReal ω) - ∫ r in u..v, G (Xt r.toNNReal ω)) ^ 2) ∂P ≤
        ENNReal.ofReal (8 * β⁻¹ * (t - u)) * ∫⁻ Y, ∑ i, ‖configGrad F Y i‖ₑ ^ 2 ∂μ :=
    fun u t hu hut htH =>
      dcl417_conj3 hH0 hXtm hXtj hstatT hFm hGm Fn (fun n Y => particleGen d s V β (Fn n) Y) hFnm hGnm
        hcF1 hsm1 hdomT hconv1 hconv2 hEF hED hFn3 u t hu hut htH
  refine ⟨?_, ?_, ?_⟩
  · filter_upwards [hcF1, hSae] with ω h1 hω
    have e : (fun r : ℝ => G (Xt r.toNNReal ω)) = fun r => G (X r.toNNReal ω) := by
      funext r
      rw [hXt_eq ω hω]
    rw [e] at h1
    exact h1
  · filter_upwards [hcF2, hSae] with ω h2 hω
    have e : (fun t : ℝ => F (Xt t.toNNReal ω) - F (Xt 0 ω) - ∫ r in (0 : ℝ)..t, G (Xt r.toNNReal ω))
        = fun t : ℝ => F (X t.toNNReal ω) - F (X 0 ω) - ∫ r in (0 : ℝ)..t, G (X r.toNNReal ω) := by
      funext t
      simp only [hXt_eq ω hω]
    rw [e] at h2
    exact h2
  · intro u t hu hut htH
    have hae : ∀ᵐ ω ∂P, (⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal
          ((F (X v.toNNReal ω) - F (X u.toNNReal ω) - ∫ r in u..v, G (X r.toNNReal ω)) ^ 2))
        = ⨆ v ∈ ratTimes u (t - u), ENNReal.ofReal
          ((F (Xt v.toNNReal ω) - F (Xt u.toNNReal ω) - ∫ r in u..v, G (Xt r.toNNReal ω)) ^ 2) := by
      filter_upwards [hSae] with ω hω
      simp only [hXt_eq ω hω]
    exact (lintegral_congr_ae hae).trans_le (hc3 u t hu hut htH)

end HRS.ME

end
