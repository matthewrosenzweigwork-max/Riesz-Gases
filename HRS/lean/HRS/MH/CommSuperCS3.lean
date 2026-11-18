import HRS.MH.CommSuperDefs
import HRS.Equilibrium.LocalDivAux
import HRS.Kernel.GradBasic

/-!
# CS3: concentrated data on the torus (packet `conc_measure` of `CommSuperSpec.lean`)

Reuses `LocalDivAux.mk_measurePreserving` and `LocalDivAux.ball_subset_cube`
(`HRS/Equilibrium/LocalDivAux.lean`), and `KernelGrad.mk_centeredRep`, `KernelGrad.tdist_mk`,
`KernelGrad.abs_centeredRep_le`, `KernelGrad.mk_sub` (`HRS/Kernel/GradBasic.lean`).
The push-forward identity is the key lemma `cs3_key`: the torus integral of `F · ρ_t` is
the Euclidean integral of `F ∘ mk(t ·) · ρ`, via the cube fundamental domain and the scaling of Lebesgue
measure (`Measure.map_addHaar_smul`).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MH.CommSuper

variable {d N : ℕ} {s : ℝ}

/-- The representative `Torus.rep` is measurable. -/
theorem cs3_measurable_rep : Measurable (Torus.rep : Torus d → Euc d) := by
  have h : Measurable (fun (x : Torus d) (i : Fin d) =>
      ((AddCircle.equivIco (1 : ℝ) 0 (x i) : Set.Ico (0 : ℝ) (0 + 1)) : ℝ)) :=
    measurable_pi_iff.2 fun i => measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply i))
  exact (WithLp.measurable_toLp 2 _).comp h

/-- The centered representative is measurable. -/
theorem cs3_measurable_cR : Measurable (KernelGrad.centeredRep : Torus d → Euc d) := by
  have hi : ∀ i : Fin d, Measurable (fun z : Torus d => Torus.rep z i) := fun i =>
    measurable_subtype_coe.comp
      ((AddCircle.measurableEquivIco (1 : ℝ) 0).measurable.comp (measurable_pi_apply i))
  have h : Measurable (fun (z : Torus d) (i : Fin d) =>
      if Torus.rep z i ≤ 1 / 2 then Torus.rep z i else Torus.rep z i - 1) :=
    measurable_pi_iff.2 fun i => Measurable.ite (measurableSet_le (hi i) measurable_const) (hi i)
      ((hi i).sub_const 1)
  exact (WithLp.measurable_toLp 2 _).comp h

theorem cs3_measurable_concDens {t : ℝ} {ρ : Euc d → ℝ} (hρ : Measurable ρ) :
    Measurable (concDens t ρ) := by
  unfold concDens
  exact measurable_const.mul (hρ.comp ((measurable_const_smul _).comp cs3_measurable_cR))

/-- Integer shift of coordinates under `mk`. -/
theorem cs3_exists_int_of_mk_eq {a b : Euc d} (h : Torus.mk a = Torus.mk b) (i : Fin d) :
    ∃ n : ℤ, a i = b i + n := by
  have h1 := congr_fun h i
  simp only [Torus.mk] at h1
  have h2 := (QuotientAddGroup.eq).mp h1
  rw [AddSubgroup.mem_zmultiples_iff] at h2
  obtain ⟨k, hk⟩ := h2
  refine ⟨-k, ?_⟩
  have hk' : (k : ℝ) = -a i + b i := by
    have : ((k • (1 : ℝ) : ℝ)) = (k : ℝ) := by simp
    rw [← this, hk]
  push_cast
  linarith

/-- On the small ball the centered representative is the identity. -/
theorem cs3_cR_of_small (z : Euc d) (hz : ∀ i, |z i| < 1 / 2) :
    KernelGrad.centeredRep (Torus.mk z) = z := by
  ext i
  obtain ⟨n, hn⟩ := cs3_exists_int_of_mk_eq (KernelGrad.mk_centeredRep (Torus.mk z)) i
  have h1 := KernelGrad.abs_centeredRep_le (Torus.mk z) i
  have h2 : |(n : ℝ)| < 1 := by
    have e : (n : ℝ) = KernelGrad.centeredRep (Torus.mk z) i - z i := by linarith
    rw [e]
    calc |KernelGrad.centeredRep (Torus.mk z) i - z i|
        ≤ |KernelGrad.centeredRep (Torus.mk z) i| + |z i| := abs_sub _ _
      _ < 1 := by linarith [hz i]
  have h3 : n = 0 := by
    have h4 : |n| < 1 := by exact_mod_cast h2
    rw [abs_lt] at h4
    omega
  rw [hn, h3]; simp

/-- Scaling of the Lebesgue integral under `x ↦ t x`, `t > 0`. -/
theorem cs3_lintegral_smul {t : ℝ} (ht : 0 < t) (Ψ : Euc d → ℝ≥0∞) (hΨ : Measurable Ψ) :
    ∫⁻ x, Ψ (t • x) = ENNReal.ofReal ((t ^ d)⁻¹) * ∫⁻ y, Ψ y := by
  have hfr : Module.finrank ℝ (Euc d) = d := by simp [Euc]
  have hmap := Measure.map_addHaar_smul (μ := (volume : Measure (Euc d))) (ne_of_gt ht)
  rw [hfr] at hmap
  have h1 : ∫⁻ x, Ψ (t • x) = ∫⁻ y, Ψ y ∂(Measure.map (t • ·) volume) := by
    rw [lintegral_map hΨ (measurable_const_smul t)]
  rw [h1, hmap, lintegral_smul_measure, abs_of_pos (inv_pos.2 (pow_pos ht d)), smul_eq_mul]

/-- `ρ` vanishes on the points `t⁻¹ c` with `‖c‖ ≥ 1/8`. -/
theorem cs3_rho_zero {t R0 : ℝ} (ht : 0 < t) (hR : t * R0 ≤ 1 / 16) {ρ : Euc d → ℝ}
    (hsupp : ∀ x, R0 < ‖x‖ → ρ x = 0) (c : Euc d) (hc : 1 / 8 ≤ ‖c‖) :
    ρ (t⁻¹ • c) = 0 := by
  apply hsupp
  rw [norm_smul, Real.norm_of_nonneg (inv_nonneg.2 ht.le)]
  have h1 : R0 = t⁻¹ * (t * R0) := by field_simp
  have h2 : t⁻¹ * (t * R0) < t⁻¹ * (1 / 8) :=
    mul_lt_mul_of_pos_left (by linarith) (inv_pos.2 ht)
  have h3 : t⁻¹ * (1 / 8) ≤ t⁻¹ * ‖c‖ := mul_le_mul_of_nonneg_left hc (inv_nonneg.2 ht.le)
  linarith

/-- Key identity: the torus integral of `F · ρ_t` equals the Euclidean integral of `F ∘ mk(t ·) · ρ`. -/
theorem cs3_key {t R0 : ℝ} (ht : 0 < t) (hR : t * R0 ≤ 1 / 16) {ρ : Euc d → ℝ}
    (hρ : Whole.IsProbDensity ρ) (hsupp : ∀ x, R0 < ‖x‖ → ρ x = 0)
    (F : Torus d → ℝ≥0∞) (hF : Measurable F) :
    ∫⁻ z, F z * ENNReal.ofReal (concDens t ρ z) =
      ∫⁻ x, F (Torus.mk (t • x)) * ENNReal.ofReal (ρ x) := by
  have hmp := LocalDivAux.mk_measurePreserving (d := d)
  have hmk : Measurable (Torus.mk : Euc d → Torus d) := hmp.measurable
  have hcdm : Measurable (concDens t ρ) := cs3_measurable_concDens hρ.measurable
  set B : Set (Euc d) := Metric.ball (0 : Euc d) (1 / 8) with hBdef
  have hBm : MeasurableSet B := measurableSet_ball
  have hBcube : B ⊆ LocalDivAux.cube d := LocalDivAux.ball_subset_cube (by norm_num)
  set H : Torus d → ℝ≥0∞ := fun z => F z * ENNReal.ofReal (concDens t ρ z) with hHdef
  have hHm : Measurable H := hF.mul hcdm.ennreal_ofReal
  set Ψ : Euc d → ℝ≥0∞ := fun y => F (Torus.mk y) * ENNReal.ofReal (ρ (t⁻¹ • y)) with hΨdef
  have hΨm : Measurable Ψ :=
    (hF.comp hmk).mul ((hρ.measurable.comp (measurable_const_smul _)).ennreal_ofReal)
  -- off the ball, `ρ (t⁻¹ • y) = 0`
  have hΨ0 : ∀ y : Euc d, y ∉ B → Ψ y = 0 := by
    intro y hy
    have hn : 1 / 8 ≤ ‖y‖ := by
      simp only [hBdef, Metric.mem_ball, dist_zero_right, not_lt] at hy
      exact hy
    simp only [hΨdef]
    rw [cs3_rho_zero ht hR hsupp y hn, ENNReal.ofReal_zero, mul_zero]
  -- on the ball, the centered representative is the identity
  have hcR_small : ∀ w : Euc d, w ∈ B → H (Torus.mk w) = ENNReal.ofReal ((t ^ d)⁻¹) * Ψ w := by
    intro w hw
    have hw' : ‖w‖ < 1 / 8 := by simpa [hBdef] using hw
    have hwi : ∀ i, |w i| < 1 / 2 := by
      intro i
      have h1 : |w i| ≤ ‖w‖ := by
        have := PiLp.norm_apply_le w i
        simpa [Real.norm_eq_abs] using this
      linarith
    have e1 : concDens t ρ (Torus.mk w) = (t ^ d)⁻¹ * ρ (t⁻¹ • w) := by
      unfold concDens
      rw [cs3_cR_of_small w hwi]
    show F (Torus.mk w) * ENNReal.ofReal (concDens t ρ (Torus.mk w)) = _
    rw [e1, ENNReal.ofReal_mul (inv_nonneg.2 (pow_nonneg ht.le d))]
    show _ = ENNReal.ofReal ((t ^ d)⁻¹) * (F (Torus.mk w) * ENNReal.ofReal (ρ (t⁻¹ • w)))
    ring
  -- off the ball, `H` vanishes on the cube
  have hH0 : ∀ w ∈ LocalDivAux.cube d, w ∉ B → H (Torus.mk w) = 0 := by
    intro w hwc hwB
    have hn : 1 / 8 ≤ ‖w‖ := by
      simpa [hBdef, Metric.mem_ball, dist_zero_right, not_lt] using hwB
    have hwi : ∀ i, |w i| ≤ 1 / 2 := by
      intro i
      obtain ⟨h1, h2⟩ := hwc i
      exact abs_le.2 ⟨by linarith, by linarith⟩
    have hcn : ‖KernelGrad.centeredRep (Torus.mk w)‖ = ‖w‖ := by
      rw [← KernelGrad.tdist_zero_right, KernelGrad.tdist_mk hwi]
    have e0 : concDens t ρ (Torus.mk w) = 0 := by
      unfold concDens
      rw [cs3_rho_zero ht hR hsupp _ (by rw [hcn]; exact hn), mul_zero]
    show F (Torus.mk w) * ENNReal.ofReal (concDens t ρ (Torus.mk w)) = 0
    rw [e0, ENNReal.ofReal_zero, mul_zero]
  have hsupΨ : Function.support Ψ ⊆ B := by
    intro y hy
    by_contra hyB
    exact hy (hΨ0 y hyB)
  have hcubeM : MeasurableSet (LocalDivAux.cube d) := LocalDivAux.measurableSet_cube
  -- step 1: torus integral to the cube
  have hL : ∫⁻ z, H z = ∫⁻ w, H (Torus.mk w) ∂(volume.restrict (LocalDivAux.cube d)) := by
    conv_lhs => rw [← hmp.map_eq]
    rw [lintegral_map hHm hmk]
  -- step 2: cube to ball
  have h2 : ∫⁻ w, H (Torus.mk w) ∂(volume.restrict (LocalDivAux.cube d)) =
      ∫⁻ w, B.indicator (fun w => H (Torus.mk w)) w ∂(volume.restrict (LocalDivAux.cube d)) := by
    refine setLIntegral_congr_fun hcubeM (fun w hw => ?_)
    by_cases hwB : w ∈ B
    · rw [Set.indicator_of_mem hwB]
    · rw [Set.indicator_of_notMem hwB, hH0 w hw hwB]
  have h2' : ∫⁻ w, B.indicator (fun w => H (Torus.mk w)) w ∂(volume.restrict (LocalDivAux.cube d)) =
      ∫⁻ w, B.indicator (fun w => H (Torus.mk w)) w := by
    refine setLIntegral_eq_of_support_subset ?_
    exact (Set.support_indicator_subset).trans hBcube
  -- step 3: on the ball, identify with the Euclidean integrand
  have h3 : ∫⁻ w, B.indicator (fun w => H (Torus.mk w)) w =
      ENNReal.ofReal ((t ^ d)⁻¹) * ∫⁻ w in B, Ψ w := by
    rw [lintegral_indicator hBm, setLIntegral_congr_fun hBm (fun w hw => hcR_small w hw),
      lintegral_const_mul _ hΨm]
  have h4 : ∫⁻ w in B, Ψ w = ∫⁻ w, Ψ w := setLIntegral_eq_of_support_subset (hsupΨ)
  -- right-hand side: scaling
  have hR' : ∫⁻ x, F (Torus.mk (t • x)) * ENNReal.ofReal (ρ x) = ∫⁻ x, Ψ (t • x) := by
    refine lintegral_congr (fun x => ?_)
    simp only [hΨdef, inv_smul_smul₀ ht.ne']
  show ∫⁻ z, H z = _
  rw [hR', cs3_lintegral_smul ht Ψ hΨm, hL, h2, h2', h3, h4]

theorem cs3_integrable {ρ : Euc d → ℝ} (hρ : Whole.IsProbDensity ρ) : Integrable ρ := by
  by_contra h
  have h1 := hρ.integral_one
  rw [integral_undef h] at h1
  norm_num at h1

/-- **CS3** (size M).  For `ρ` a `ℝ^d` probability density supported in `closedBall 0 R0` with
`t R0 ≤ 1/16`: the torus measure `ρ_t dz` is the push-forward of `ρ dx` under `concMap t` (so every
torus integral is a Euclidean integral, with no junk: `Measure.map` of the continuous map `concMap t`),
`ρ_t` is a torus probability density, `ρ_t ≤ (t^d)⁻¹ Λ` when `ρ ≤ Λ`, and an injective configuration in
`closedBall 0 R0` is sent to a collision-free torus configuration.
Reuses `LocalDivAux.mk_measurePreserving` (`HRS/Equilibrium/LocalDivAux.lean:25`, cube `(-1/2,1/2]^d`),
`integral_torus_local` (`:66`), `abs_apply_eq_of_mk` (`GradBasic.lean:121`), `tdist_mk` (`:126`). -/
theorem conc_measure_proof {t R0 : ℝ} (ht : 0 < t) (hR : t * R0 ≤ 1 / 16) {ρ : Euc d → ℝ}
    (hρ : Whole.IsProbDensity ρ) (hsupp : ∀ x, R0 < ‖x‖ → ρ x = 0) :
    withDensityReal (concDens t ρ) = (Whole.withDensityReal ρ).map (concMap t) ∧
      IsProbDensity (concDens t ρ) ∧
      (∀ Λ : ℝ, (∀ x, ρ x ≤ Λ) → ∀ z, concDens t ρ z ≤ (t ^ d)⁻¹ * Λ) ∧
      ∀ (X : Whole.EucConfig d N), Function.Injective X → (∀ i, ‖X i‖ ≤ R0) →
        (fun i => concMap t (X i)) ∉ collisionSet d N := by
  have hpos : (0 : ℝ) ≤ (t ^ d)⁻¹ := inv_nonneg.2 (pow_nonneg ht.le d)
  have hcm : Measurable (concMap t : Euc d → Torus d) :=
    (LocalDivAux.mk_measurePreserving (d := d)).measurable.comp (measurable_const_smul t)
  have hcd : Measurable (concDens t ρ) := cs3_measurable_concDens hρ.measurable
  have hnonneg : ∀ z, 0 ≤ concDens t ρ z := fun z => mul_nonneg hpos (hρ.nonneg _)
  -- (1) push-forward identity
  have hpart1 : withDensityReal (concDens t ρ) = (Whole.withDensityReal ρ).map (concMap t) := by
    refine Measure.ext fun A hA => ?_
    rw [Measure.map_apply hcm hA, HRS.withDensityReal, HRS.Whole.withDensityReal,
      withDensity_apply _ hA, withDensity_apply _ (hcm hA)]
    have e1 : ∫⁻ z in A, ENNReal.ofReal (concDens t ρ z) =
        ∫⁻ z, A.indicator (fun _ => (1 : ℝ≥0∞)) z * ENNReal.ofReal (concDens t ρ z) := by
      rw [← lintegral_indicator hA]
      congr 1; ext z
      by_cases hz : z ∈ A <;> simp [hz]
    have e2 : ∫⁻ x in (concMap t) ⁻¹' A, ENNReal.ofReal (ρ x) =
        ∫⁻ x, A.indicator (fun _ => (1 : ℝ≥0∞)) (concMap t x) * ENNReal.ofReal (ρ x) := by
      rw [← lintegral_indicator (hcm hA)]
      congr 1; ext x
      by_cases hx : concMap t x ∈ A <;> simp [hx]
    rw [e1, e2]
    exact cs3_key ht hR hρ hsupp _ (measurable_const.indicator hA)
  refine ⟨hpart1, ⟨hnonneg, hcd, ?_⟩, ?_, ?_⟩
  · -- (2) integral one
    have hint1 : ∫⁻ z, ENNReal.ofReal (concDens t ρ z) = 1 := by
      have := cs3_key ht hR hρ hsupp (fun _ => (1 : ℝ≥0∞)) measurable_const
      simp only [one_mul] at this
      rw [this, ← ofReal_integral_eq_lintegral_ofReal (cs3_integrable hρ)
        (Filter.Eventually.of_forall hρ.nonneg), hρ.integral_one, ENNReal.ofReal_one]
    rw [integral_eq_lintegral_of_nonneg_ae (Filter.Eventually.of_forall hnonneg)
      hcd.aestronglyMeasurable, hint1, ENNReal.toReal_one]
  · -- (3) bound
    intro Λ hΛ z
    exact mul_le_mul_of_nonneg_left (hΛ _) hpos
  · -- (4) no collisions
    intro X hX hXR hmem
    obtain ⟨i, j, hij, heq⟩ := hmem
    have heq' : Torus.mk (t • X i) = Torus.mk (t • X j) := heq
    have hmk0 : (Torus.mk (0 : Euc d) : Torus d) = 0 := by
      funext k; simp [Torus.mk]
    have hu : Torus.mk (t • X i - t • X j) = Torus.mk 0 := by
      rw [KernelGrad.mk_sub, heq', sub_self, hmk0]
    have hcoord : ∀ k : Fin d, |t * X i k - t * X j k| ≤ 1 / 8 := by
      intro k
      have ha : |X i k| ≤ R0 := by
        have := PiLp.norm_apply_le (X i) k
        simp only [Real.norm_eq_abs] at this
        exact this.trans (hXR i)
      have hb : |X j k| ≤ R0 := by
        have := PiLp.norm_apply_le (X j) k
        simp only [Real.norm_eq_abs] at this
        exact this.trans (hXR j)
      calc |t * X i k - t * X j k| ≤ |t * X i k| + |t * X j k| := abs_sub _ _
        _ = t * |X i k| + t * |X j k| := by
          rw [abs_mul, abs_mul, abs_of_pos ht]
        _ ≤ t * R0 + t * R0 := by
          gcongr
        _ = 2 * (t * R0) := by ring
        _ ≤ 1 / 8 := by linarith
    have hdiff : t • X i - t • X j = 0 := by
      ext k
      obtain ⟨n, hn⟩ := cs3_exists_int_of_mk_eq hu k
      have hc := hcoord k
      have hk : (t • X i - t • X j) k = t * X i k - t * X j k := by
        simp [PiLp.sub_apply, PiLp.smul_apply, smul_eq_mul]
      have h2 : |(n : ℝ)| < 1 := by
        have e : (n : ℝ) = t * X i k - t * X j k := by
          rw [← hk]; simp at hn; linarith
        rw [e]; linarith
      have h3 : n = 0 := by
        have h4 : |n| < 1 := by exact_mod_cast h2
        rw [abs_lt] at h4
        omega
      have e2 : (t • X i - t • X j) k = 0 := by
        rw [hk]
        have : (n : ℝ) = t * X i k - t * X j k := by
          rw [← hk]; simp at hn; linarith
        rw [← this, h3]; simp
      simpa using e2
    have hXeq : X i = X j := by
      have : t • X i = t • X j := sub_eq_zero.1 hdiff
      exact smul_right_injective _ ht.ne' this
    exact hij (hX hXeq)

end HRS.MH.CommSuper
