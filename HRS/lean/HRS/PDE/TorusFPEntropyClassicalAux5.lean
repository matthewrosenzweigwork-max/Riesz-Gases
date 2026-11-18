import HRS.PDE.TorusFPEntropyClassicalAux4

/-!
# D3-a (classical layer), helper 5: the exact free-energy identity for classical positive data

Route.  With `P = d1_gibbsMeasure κ U`, `μ_r = P.withDensity w_r`:

* `relEntropy (μ_r) P` has `toReal` equal to `∫ w_r log w_r dP` (probability densities,
  `InformationTheory.toReal_klDiv_of_measure_eq`);
* `∫ w_t log w_t dP - ∫ w_0 log w_0 dP = -κ ∫_0^t ∫ ‖∇ log w_r‖² dμ_r dr` (integrated product rule `d3a_ftc` with
  `F = w log w`, `∂_r F = L w (log w + 1)`, and the weighted Green identity with `∫ L w dP = 0`);
* the tilt part comes from the weak formulation (`d3a_isWeak`) applied to `ψ`;
* the pointwise-in-time algebra is `d3a_balance` (Green identity for `ψ`, `∇w = w ∇ log w`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS

variable {n : ℕ}

theorem d3a_mass_eq {P : Measure (Torus n)} [IsFiniteMeasure P] {w : Torus n → ℝ}
    (hc : Continuous w) (h0 : ∀ x, 0 ≤ w x) :
    (P.withDensity fun x => ENNReal.ofReal (w x)) Set.univ = ENNReal.ofReal (∫ x, w x ∂P) := by
  rw [withDensity_apply _ MeasurableSet.univ, Measure.restrict_univ]
  exact (ofReal_integral_eq_lintegral_ofReal (d3a_hint P hc) (ae_of_all _ h0)).symm

theorem d3a_relEntropy_toReal {P : Measure (Torus n)} [IsProbabilityMeasure P] {w : Torus n → ℝ}
    (hc : Continuous w) (hpos : ∀ x, 0 < w x) (hmass : ∫ x, w x ∂P = 1) :
    (relEntropy (P.withDensity fun x => ENNReal.ofReal (w x)) P).toReal =
      ∫ x, w x * Real.log (w x) ∂P := by
  haveI : IsFiniteMeasure (P.withDensity fun x => ENNReal.ofReal (w x)) :=
    isFiniteMeasure_withDensity_ofReal (d3a_hint P hc).hasFiniteIntegral
  have hac : (P.withDensity fun x => ENNReal.ofReal (w x)) ≪ P := withDensity_absolutelyContinuous P _
  have hmeas : Measurable fun x => ENNReal.ofReal (w x) := hc.measurable.ennreal_ofReal
  have hmu : (P.withDensity fun x => ENNReal.ofReal (w x)) Set.univ = P Set.univ := by
    rw [d3a_mass_eq hc (fun x => (hpos x).le), hmass]
    simp
  unfold relEntropy
  rw [InformationTheory.toReal_klDiv_of_measure_eq hac hmu]
  have hllr : llr (P.withDensity fun x => ENNReal.ofReal (w x)) P =ᵐ[P] fun x => Real.log (w x) := by
    filter_upwards [Measure.rnDeriv_withDensity P hmeas] with x hx
    simp only [llr, hx, ENNReal.toReal_ofReal (hpos x).le]
  rw [integral_congr_ae (hac.ae_eq hllr),
    d3a_integral_withDensity hc.measurable (fun x => (hpos x).le) (fun x => Real.log (w x))]

/-- Pointwise-in-time algebra of the free-energy identity (Green identity for `ψ`). -/
theorem d3a_balance {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    {w ψ ψt : Torus n → ℝ} (hw : Torus.IsCk 2 w) (hpos : ∀ x, 0 < w x) (hψ : Torus.IsCk 2 ψ)
    (hψt : Continuous ψt) :
    ∫ x, w x * (d1_gen κ (d1_gradDrift U) ψ x + κ * ‖Torus.grad ψ x‖ ^ 2 - ψt x)
        ∂(d1_gibbsMeasure κ U) =
      -κ * ∫ x, w x * ‖Torus.grad (fun y => Real.log (w y)) x‖ ^ 2 ∂(d1_gibbsMeasure κ U)
        - ∫ x, w x * (ψt x + d1_gen κ (d1_gradDrift U) ψ x) ∂(d1_gibbsMeasure κ U)
        + κ * ∫ x, w x * ‖Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x‖ ^ 2
          ∂(d1_gibbsMeasure κ U) := by
  haveI hP := d3a_gibbs_isProb (κ := κ) hU
  have hw1 := d3a_ck2_ck1 hw
  have hψ1 := d3a_ck2_ck1 hψ
  have hlog1 : Torus.IsCk 1 (fun y => Real.log (w y)) := d3a_isCk_log hw1 hpos
  have cw := d3a_continuous_of_ck1 hw1
  have cL : Continuous (d1_gen κ (d1_gradDrift U) ψ) :=
    d1_gen_continuous (d1_gradDrift_continuous hU) hψ
  have cgψ := d3a_continuous_grad_ck1 hψ1
  have cgl := d3a_continuous_grad_ck1 hlog1
  have cnψ : Continuous fun x => ‖Torus.grad ψ x‖ ^ 2 := cgψ.norm.pow 2
  have cnl : Continuous fun x => ‖Torus.grad (fun y => Real.log (w y)) x‖ ^ 2 := cgl.norm.pow 2
  have cin : Continuous fun x => inner ℝ (Torus.grad (fun y => Real.log (w y)) x) (Torus.grad ψ x) :=
    cgl.inner cgψ
  have cdf : Continuous fun x =>
      ‖Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x‖ ^ 2 := (cgl.sub cgψ).norm.pow 2
  -- Green identity for ψ against w
  have hG : ∫ x, w x * d1_gen κ (d1_gradDrift U) ψ x ∂(d1_gibbsMeasure κ U) =
      -κ * ∫ x, w x * inner ℝ (Torus.grad (fun y => Real.log (w y)) x) (Torus.grad ψ x)
        ∂(d1_gibbsMeasure κ U) := by
    have h := d3a_green_P hκ hU (f := w) (w := ψ) hw hψ
    have e1 : ∫ x, w x * d1_gen κ (d1_gradDrift U) ψ x ∂(d1_gibbsMeasure κ U) =
        ∫ x, d1_gen κ (d1_gradDrift U) ψ x * w x ∂(d1_gibbsMeasure κ U) :=
      integral_congr_ae (ae_of_all _ fun x => mul_comm _ _)
    have e2 : ∫ x, inner ℝ (Torus.grad w x) (Torus.grad ψ x) ∂(d1_gibbsMeasure κ U) =
        ∫ x, w x * inner ℝ (Torus.grad (fun y => Real.log (w y)) x) (Torus.grad ψ x)
          ∂(d1_gibbsMeasure κ U) :=
      integral_congr_ae (ae_of_all _ fun x => by
        beta_reduce
        rw [d3a_grad_eq_smul_log hw1 hpos x, real_inner_smul_left])
    rw [e1, h, e2]
  have hL1 : ∫ x, w x * (d1_gen κ (d1_gradDrift U) ψ x + κ * ‖Torus.grad ψ x‖ ^ 2 - ψt x)
        ∂(d1_gibbsMeasure κ U) =
      (∫ x, w x * d1_gen κ (d1_gradDrift U) ψ x ∂(d1_gibbsMeasure κ U)) +
        κ * (∫ x, w x * ‖Torus.grad ψ x‖ ^ 2 ∂(d1_gibbsMeasure κ U)) -
        ∫ x, w x * ψt x ∂(d1_gibbsMeasure κ U) := by
    have i1 : Integrable (fun x => w x * d1_gen κ (d1_gradDrift U) ψ x) (d1_gibbsMeasure κ U) :=
      d3a_hint _ (cw.mul cL)
    have i2 : Integrable (fun x => κ * (w x * ‖Torus.grad ψ x‖ ^ 2)) (d1_gibbsMeasure κ U) :=
      d3a_hint _ (continuous_const.mul (cw.mul cnψ))
    have i3 : Integrable (fun x => w x * ψt x) (d1_gibbsMeasure κ U) := d3a_hint _ (cw.mul hψt)
    calc ∫ x, w x * (d1_gen κ (d1_gradDrift U) ψ x + κ * ‖Torus.grad ψ x‖ ^ 2 - ψt x)
          ∂(d1_gibbsMeasure κ U)
        = ∫ x, (w x * d1_gen κ (d1_gradDrift U) ψ x + κ * (w x * ‖Torus.grad ψ x‖ ^ 2) -
            w x * ψt x) ∂(d1_gibbsMeasure κ U) := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          ring
      _ = (∫ x, w x * d1_gen κ (d1_gradDrift U) ψ x ∂(d1_gibbsMeasure κ U)) +
          (∫ x, κ * (w x * ‖Torus.grad ψ x‖ ^ 2) ∂(d1_gibbsMeasure κ U)) -
          ∫ x, w x * ψt x ∂(d1_gibbsMeasure κ U) := by
          have i12 : Integrable (fun x => w x * d1_gen κ (d1_gradDrift U) ψ x +
              κ * (w x * ‖Torus.grad ψ x‖ ^ 2)) (d1_gibbsMeasure κ U) := i1.add i2
          rw [integral_sub i12 i3, integral_add i1 i2]
      _ = _ := by rw [integral_const_mul]
  have hB : ∫ x, w x * (ψt x + d1_gen κ (d1_gradDrift U) ψ x) ∂(d1_gibbsMeasure κ U) =
      (∫ x, w x * ψt x ∂(d1_gibbsMeasure κ U)) +
        ∫ x, w x * d1_gen κ (d1_gradDrift U) ψ x ∂(d1_gibbsMeasure κ U) := by
    have i1 : Integrable (fun x => w x * ψt x) (d1_gibbsMeasure κ U) := d3a_hint _ (cw.mul hψt)
    have i2 : Integrable (fun x => w x * d1_gen κ (d1_gradDrift U) ψ x) (d1_gibbsMeasure κ U) :=
      d3a_hint _ (cw.mul cL)
    rw [← integral_add i1 i2]
    exact integral_congr_ae (ae_of_all _ fun x => by ring)
  have hC : ∫ x, w x * ‖Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x‖ ^ 2
        ∂(d1_gibbsMeasure κ U) =
      (∫ x, w x * ‖Torus.grad (fun y => Real.log (w y)) x‖ ^ 2 ∂(d1_gibbsMeasure κ U)) -
        2 * (∫ x, w x * inner ℝ (Torus.grad (fun y => Real.log (w y)) x) (Torus.grad ψ x)
          ∂(d1_gibbsMeasure κ U)) +
        ∫ x, w x * ‖Torus.grad ψ x‖ ^ 2 ∂(d1_gibbsMeasure κ U) := by
    have i1 : Integrable (fun x => w x * ‖Torus.grad (fun y => Real.log (w y)) x‖ ^ 2)
        (d1_gibbsMeasure κ U) := d3a_hint _ (cw.mul cnl)
    have i2 : Integrable (fun x => 2 * (w x * inner ℝ (Torus.grad (fun y => Real.log (w y)) x)
        (Torus.grad ψ x))) (d1_gibbsMeasure κ U) :=
      d3a_hint _ (continuous_const.mul (cw.mul cin))
    have i3 : Integrable (fun x => w x * ‖Torus.grad ψ x‖ ^ 2) (d1_gibbsMeasure κ U) :=
      d3a_hint _ (cw.mul cnψ)
    calc ∫ x, w x * ‖Torus.grad (fun y => Real.log (w y)) x - Torus.grad ψ x‖ ^ 2
          ∂(d1_gibbsMeasure κ U)
        = ∫ x, (w x * ‖Torus.grad (fun y => Real.log (w y)) x‖ ^ 2 -
            2 * (w x * inner ℝ (Torus.grad (fun y => Real.log (w y)) x) (Torus.grad ψ x)) +
            w x * ‖Torus.grad ψ x‖ ^ 2) ∂(d1_gibbsMeasure κ U) := by
          refine integral_congr_ae (ae_of_all _ fun x => ?_)
          beta_reduce
          rw [norm_sub_sq_real]
          ring
      _ = (∫ x, w x * ‖Torus.grad (fun y => Real.log (w y)) x‖ ^ 2 ∂(d1_gibbsMeasure κ U)) -
          (∫ x, 2 * (w x * inner ℝ (Torus.grad (fun y => Real.log (w y)) x) (Torus.grad ψ x))
            ∂(d1_gibbsMeasure κ U)) +
          ∫ x, w x * ‖Torus.grad ψ x‖ ^ 2 ∂(d1_gibbsMeasure κ U) := by
          have i12 : Integrable (fun x => w x * ‖Torus.grad (fun y => Real.log (w y)) x‖ ^ 2 -
              2 * (w x * inner ℝ (Torus.grad (fun y => Real.log (w y)) x) (Torus.grad ψ x)))
              (d1_gibbsMeasure κ U) := i1.sub i2
          rw [integral_add i12 i3, integral_sub i1 i2]
      _ = _ := by rw [integral_const_mul]
  rw [hL1, hB, hC]
  linarith [hG]

theorem d3a_lin3 {a b c : ℝ → ℝ} {s : Set ℝ} (ha : IntegrableOn a s) (hb : IntegrableOn b s)
    (hc : IntegrableOn c s) (κ : ℝ) :
    ∫ r in s, (-κ * a r - b r + κ * c r) =
      -κ * (∫ r in s, a r) - (∫ r in s, b r) + κ * ∫ r in s, c r := by
  have iA : Integrable (fun r => -κ * a r) (volume.restrict s) := ha.const_mul _
  have iC : Integrable (fun r => κ * c r) (volume.restrict s) := hc.const_mul _
  have iAB : Integrable (fun r => -κ * a r - b r) (volume.restrict s) := iA.sub hb
  calc ∫ r in s, (-κ * a r - b r + κ * c r)
      = (∫ r in s, (-κ * a r - b r)) + ∫ r in s, κ * c r := integral_add iAB iC
    _ = _ := by rw [integral_sub iA hb, integral_const_mul, integral_const_mul]

/-- **Exact free-energy identity, classical positive data** (`d3_tilted_identity_classical`). -/
theorem d3a_identity (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ}
    (hU : Torus.IsSmooth U) {T : ℝ} (hT : 0 < T) {w : ℝ → Torus n → ℝ} (hw : D3Classical κ U T w)
    (hmass : ∫ x, w 0 x ∂(d1_gibbsMeasure κ U) = 1) {ψ ψt : ℝ → Torus n → ℝ}
    (hψ : IsC12Test T ψ ψt) :
    ∀ t ∈ Set.Icc 0 T,
      (relEntropy ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w t x))
          (d1_gibbsMeasure κ U)).toReal
        - ∫ x, ψ t x ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w t x))
        + κ * ∫ r in Set.Icc 0 t, ∫ x, ‖Torus.grad (fun y => Real.log (w r y)) x - Torus.grad (ψ r) x‖ ^ 2
            ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w r x))
      = (relEntropy ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w 0 x))
          (d1_gibbsMeasure κ U)).toReal
        - ∫ x, ψ 0 x ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w 0 x))
        + ∫ r in Set.Icc 0 t, ∫ x, d3_source κ U ψ ψt r x
            ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w r x)) := by
  intro t ht
  haveI hP := d3a_gibbs_isProb (κ := κ) hU
  have hweak := d3a_isWeak hn hκ hU hw
  have hb := d1_gradDrift_continuous hU
  have hwc : Continuous fun p : Set.Icc (0 : ℝ) T × Torus n => w p.1 p.2 := hw.c12.continuous_f
  have hpos := hw.pos
  have hw2 : ∀ r ∈ Set.Icc (0 : ℝ) T, Torus.IsCk 2 (w r) := hw.c12.c2
  have hconv : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ g : Torus n → ℝ,
      ∫ x, g x ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w r x)) =
        ∫ x, w r x * g x ∂(d1_gibbsMeasure κ U) := fun r hr g =>
    d3a_integral_withDensity (d3a_contOn_space hwc hr).measurable (fun x => (hpos r hr x).le) g
  have htI : t ∈ Set.Icc (0 : ℝ) T := ht
  have h0T : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, ht.1.trans ht.2⟩
  have hmassr : ∀ r ∈ Set.Icc (0 : ℝ) T, ∫ x, w r x ∂(d1_gibbsMeasure κ U) = 1 := by
    intro r hr
    have h : ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w r x)) Set.univ =
        ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w 0 x)) Set.univ :=
      d1_mass_conserved hweak hr
    rw [d3a_mass_eq (d3a_contOn_space hwc hr) (fun x => (hpos r hr x).le),
      d3a_mass_eq (d3a_contOn_space hwc h0T) (fun x => (hpos 0 h0T x).le), hmass] at h
    exact (ENNReal.ofReal_eq_ofReal_iff (integral_nonneg fun x => (hpos r hr x).le)
      zero_le_one).1 h
  rcases ht.1.eq_or_lt with rfl | htpos
  · simp
  have hmemT : ∀ r ∈ Set.Icc (0 : ℝ) t, r ∈ Set.Icc (0 : ℝ) T := fun r hr => ⟨hr.1, hr.2.trans ht.2⟩
  have hwt : IsC12Test t w (fun r x => d1_gen κ (d1_gradDrift U) (w r) x) :=
    d3a_C12_restrict hw.c12 ht
  have hψt' : IsC12Test t ψ ψt := d3a_C12_restrict hψ ht
  have hwct : Continuous fun p : Set.Icc (0 : ℝ) t × Torus n => w p.1 p.2 := hwt.continuous_f
  have hposT : ∀ p : Set.Icc (0 : ℝ) t × Torus n, 0 < w p.1 p.2 := fun p =>
    hpos p.1 (hmemT p.1 p.1.2) p.2
  -- the entropy part
  have hlogc : Continuous fun p : Set.Icc (0 : ℝ) t × Torus n => Real.log (w p.1 p.2) :=
    hwct.log fun p => (hposT p).ne'
  have hLw : Continuous fun p : Set.Icc (0 : ℝ) t × Torus n =>
      d1_gen κ (d1_gradDrift U) (w p.1) p.2 := hwt.cont_time_deriv
  have hF : Continuous fun p : Set.Icc (0 : ℝ) t × Torus n => w p.1 p.2 * Real.log (w p.1 p.2) :=
    hwct.mul hlogc
  have hD : Continuous fun p : Set.Icc (0 : ℝ) t × Torus n =>
      d1_gen κ (d1_gradDrift U) (w p.1) p.2 * Real.log (w p.1 p.2) +
        w p.1 p.2 * (d1_gen κ (d1_gradDrift U) (w p.1) p.2 / w p.1 p.2) :=
    (hLw.mul hlogc).add (hwct.mul (hLw.div hwct fun p => (hposT p).ne'))
  have hder : ∀ x : Torus n, ∀ r ∈ Set.Ioo (0 : ℝ) t,
      HasDerivAt (fun s => w s x * Real.log (w s x))
        (d1_gen κ (d1_gradDrift U) (w r) x * Real.log (w r x) +
          w r x * (d1_gen κ (d1_gradDrift U) (w r) x / w r x)) r := by
    intro x r hr
    have h1 := hwt.time_deriv x r hr
    have hne : w r x ≠ 0 := (hpos r (hmemT r (Set.Ioo_subset_Icc_self hr)) x).ne'
    exact h1.mul (h1.log hne)
  have hE : (∫ x, w t x * Real.log (w t x) ∂(d1_gibbsMeasure κ U)) -
      ∫ x, w 0 x * Real.log (w 0 x) ∂(d1_gibbsMeasure κ U) =
      ∫ r in Set.Icc (0 : ℝ) t, ∫ x, (d1_gen κ (d1_gradDrift U) (w r) x * Real.log (w r x) +
        w r x * (d1_gen κ (d1_gradDrift U) (w r) x / w r x)) ∂(d1_gibbsMeasure κ U) :=
    d3a_ftc (ν := d1_gibbsMeasure κ U) htpos
      (F := fun r x => w r x * Real.log (w r x))
      (D := fun r x => d1_gen κ (d1_gradDrift U) (w r) x * Real.log (w r x) +
        w r x * (d1_gen κ (d1_gradDrift U) (w r) x / w r x)) hF hD hder
  have hinnerE : ∀ r ∈ Set.Icc (0 : ℝ) t,
      ∫ x, (d1_gen κ (d1_gradDrift U) (w r) x * Real.log (w r x) +
        w r x * (d1_gen κ (d1_gradDrift U) (w r) x / w r x)) ∂(d1_gibbsMeasure κ U) =
      -κ * ∫ x, w r x * ‖Torus.grad (fun y => Real.log (w r y)) x‖ ^ 2 ∂(d1_gibbsMeasure κ U) := by
    intro r hr
    have hrT := hmemT r hr
    have hw1 := d3a_ck2_ck1 (hw2 r hrT)
    have hlog2 : Torus.IsCk 2 (fun y => Real.log (w r y)) := d3a_isCk_log (hw2 r hrT) (hpos r hrT)
    have cL : Continuous (d1_gen κ (d1_gradDrift U) (w r)) := d1_gen_continuous hb (hw2 r hrT)
    have clog : Continuous fun x => Real.log (w r x) := d3a_continuous_of_ck1 (d3a_ck2_ck1 hlog2)
    have h1 : ∀ x, d1_gen κ (d1_gradDrift U) (w r) x * Real.log (w r x) +
        w r x * (d1_gen κ (d1_gradDrift U) (w r) x / w r x) =
        d1_gen κ (d1_gradDrift U) (w r) x * Real.log (w r x) +
          d1_gen κ (d1_gradDrift U) (w r) x := fun x => by
      have hne : w r x ≠ 0 := (hpos r hrT x).ne'
      field_simp
    simp_rw [h1]
    have iL1 : Integrable (fun x => d1_gen κ (d1_gradDrift U) (w r) x * Real.log (w r x))
        (d1_gibbsMeasure κ U) := d3a_hint _ (cL.mul clog)
    rw [integral_add iL1 (d3a_hint _ cL),
      d3a_int_gen_zero hκ hU (hw2 r hrT), add_zero,
      d3a_green_P hκ hU hlog2 (hw2 r hrT)]
    congr 1
    refine integral_congr_ae (ae_of_all _ fun x => ?_)
    beta_reduce
    rw [d3a_grad_eq_smul_log hw1 (hpos r hrT) x, real_inner_smul_right, real_inner_self_eq_norm_sq]
  have hEnt : (∫ x, w t x * Real.log (w t x) ∂(d1_gibbsMeasure κ U)) -
      ∫ x, w 0 x * Real.log (w 0 x) ∂(d1_gibbsMeasure κ U) =
      -κ * ∫ r in Set.Icc (0 : ℝ) t, ∫ x, w r x * ‖Torus.grad (fun y => Real.log (w r y)) x‖ ^ 2
        ∂(d1_gibbsMeasure κ U) := by
    rw [hE, ← integral_const_mul]
    exact setIntegral_congr_fun measurableSet_Icc fun r hr => hinnerE r hr
  have hHt : (relEntropy ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w t x))
      (d1_gibbsMeasure κ U)).toReal = ∫ x, w t x * Real.log (w t x) ∂(d1_gibbsMeasure κ U) :=
    d3a_relEntropy_toReal (d3a_contOn_space hwc htI) (hpos t htI) (hmassr t htI)
  have hH0 : (relEntropy ((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w 0 x))
      (d1_gibbsMeasure κ U)).toReal = ∫ x, w 0 x * Real.log (w 0 x) ∂(d1_gibbsMeasure κ U) :=
    d3a_relEntropy_toReal (d3a_contOn_space hwc h0T) (hpos 0 h0T) (hmassr 0 h0T)
  -- the tilt part, from the weak formulation
  have hψeq : ∫ x, ψ t x ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w t x)) =
      ∫ x, ψ 0 x ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w 0 x)) +
        ∫ s in Set.Icc (0 : ℝ) t, ∫ x, (ψt s x + d1_gen κ (d1_gradDrift U) (ψ s) x)
          ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w s x)) :=
    hweak.eqT t htI ψ ψt hψt'
  -- joint continuity of the integrands
  have hgl : Continuous fun p : Set.Icc (0 : ℝ) t × Torus n =>
      Torus.grad (fun y => Real.log (w p.1 y)) p.2 := by
    have e : (fun p : Set.Icc (0 : ℝ) t × Torus n => Torus.grad (fun y => Real.log (w p.1 y)) p.2) =
        fun p => (w p.1 p.2)⁻¹ • Torus.grad (w p.1) p.2 := funext fun p =>
      d3a_grad_log (d3a_ck2_ck1 (hw2 p.1 (hmemT p.1 p.1.2))) (hpos p.1 (hmemT p.1 p.1.2)) p.2
    rw [e]
    exact (hwct.inv₀ fun p => (hposT p).ne').smul (d3a_continuous_grad hwt)
  have hgψ : Continuous fun p : Set.Icc (0 : ℝ) t × Torus n => Torus.grad (ψ p.1) p.2 :=
    d3a_continuous_grad hψt'
  have hLψ : Continuous fun p : Set.Icc (0 : ℝ) t × Torus n =>
      d1_gen κ (d1_gradDrift U) (ψ p.1) p.2 := hψt'.continuous_gen hb
  have hψtc : Continuous fun p : Set.Icc (0 : ℝ) t × Torus n => ψt p.1 p.2 :=
    hψt'.cont_time_deriv
  have hAc : Continuous fun p : Set.Icc (0 : ℝ) t × Torus n =>
      w p.1 p.2 * ‖Torus.grad (fun y => Real.log (w p.1 y)) p.2‖ ^ 2 := hwct.mul (hgl.norm.pow 2)
  have hBc : Continuous fun p : Set.Icc (0 : ℝ) t × Torus n =>
      w p.1 p.2 * (ψt p.1 p.2 + d1_gen κ (d1_gradDrift U) (ψ p.1) p.2) :=
    hwct.mul (hψtc.add hLψ)
  have hCc : Continuous fun p : Set.Icc (0 : ℝ) t × Torus n =>
      w p.1 p.2 * ‖Torus.grad (fun y => Real.log (w p.1 y)) p.2 - Torus.grad (ψ p.1) p.2‖ ^ 2 :=
    hwct.mul ((hgl.sub hgψ).norm.pow 2)
  have hAi := (d3a_continuousOn_integral (ν := d1_gibbsMeasure κ U)
    (H := fun r x => w r x * ‖Torus.grad (fun y => Real.log (w r y)) x‖ ^ 2) hAc).integrableOn_Icc (μ := volume)
  have hBi := (d3a_continuousOn_integral (ν := d1_gibbsMeasure κ U)
    (H := fun r x => w r x * (ψt r x + d1_gen κ (d1_gradDrift U) (ψ r) x)) hBc).integrableOn_Icc (μ := volume)
  have hCi := (d3a_continuousOn_integral (ν := d1_gibbsMeasure κ U)
    (H := fun r x => w r x * ‖Torus.grad (fun y => Real.log (w r y)) x - Torus.grad (ψ r) x‖ ^ 2)
    hCc).integrableOn_Icc (μ := volume)
  -- time integrals of the three pieces
  have hBset : ∫ s in Set.Icc (0 : ℝ) t, ∫ x, (ψt s x + d1_gen κ (d1_gradDrift U) (ψ s) x)
        ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w s x)) =
      ∫ s in Set.Icc (0 : ℝ) t, ∫ x, w s x * (ψt s x + d1_gen κ (d1_gradDrift U) (ψ s) x)
        ∂(d1_gibbsMeasure κ U) :=
    setIntegral_congr_fun measurableSet_Icc fun r hr => hconv r (hmemT r hr) _
  have hCset : ∫ r in Set.Icc (0 : ℝ) t, ∫ x, ‖Torus.grad (fun y => Real.log (w r y)) x -
        Torus.grad (ψ r) x‖ ^ 2 ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w r x)) =
      ∫ r in Set.Icc (0 : ℝ) t, ∫ x, w r x * ‖Torus.grad (fun y => Real.log (w r y)) x -
        Torus.grad (ψ r) x‖ ^ 2 ∂(d1_gibbsMeasure κ U) :=
    setIntegral_congr_fun measurableSet_Icc fun r hr => hconv r (hmemT r hr) _
  have hSset : ∫ r in Set.Icc (0 : ℝ) t, ∫ x, d3_source κ U ψ ψt r x
        ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w r x)) =
      ∫ r in Set.Icc (0 : ℝ) t,
        (-κ * ∫ x, w r x * ‖Torus.grad (fun y => Real.log (w r y)) x‖ ^ 2 ∂(d1_gibbsMeasure κ U)
          - ∫ x, w r x * (ψt r x + d1_gen κ (d1_gradDrift U) (ψ r) x) ∂(d1_gibbsMeasure κ U)
          + κ * ∫ x, w r x * ‖Torus.grad (fun y => Real.log (w r y)) x - Torus.grad (ψ r) x‖ ^ 2
            ∂(d1_gibbsMeasure κ U)) := by
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hrT := hmemT r hr
    have hψtr : Continuous (ψt r) := d3a_contOn_space (F := ψt) hψtc hr
    show ∫ x, d3_source κ U ψ ψt r x
        ∂((d1_gibbsMeasure κ U).withDensity fun x => ENNReal.ofReal (w r x)) = _
    rw [hconv r hrT]
    exact d3a_balance hκ hU (hw2 r hrT) (hpos r hrT) (hψ.c2 r hrT) hψtr
  rw [hCset, hSset, d3a_lin3 hAi hBi hCi κ, hHt, hH0]
  have hψeq' := hψeq
  rw [hBset] at hψeq'
  linarith [hEnt, hψeq']

end HRS
