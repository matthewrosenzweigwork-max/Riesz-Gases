import HRS.Energy.Commutator.Slice
import HRS.Energy.Commutator.SmearAux
import HRS.Energy.Commutator.SmearAuxB
import HRS.Energy.Commutator.SmearAuxC
import HRS.Energy.Commutator.SmearAuxD
import HRS.Energy.Commutator.SmearAuxE
import HRS.Energy.Commutator.SmearAuxF

/-!
# Route S, packet S2: compactly supported radial charges with exact (Newton) potentials

For `l > 0` put `u_{l,η}(x) = Γ_l(max(|x|, η))` (the truncation `min(G_l, G_l(η))`) and
`σ_{l,η} := (l - Δ) u_{l,η}`.  A direct radial computation (Green's formula on the exterior of the
ball, polar coordinates `integral_fun_norm_addHaar`/`Measure.toSphere`, the ODE
`(r^{d-1}Γ')' = l r^{d-1} Γ`) gives
`σ_{l,η} = l Γ_l(η) 1_{B_η} dx + (-Γ_l'(η)) H^{d-1}|_{∂B_η}`,
a **positive** radial measure supported in `B̄_η` (`Γ_l' < 0`), of mass `1 - l ∫ f_{l,η}`, whose
periodic potential is `𝒢_l^{full} * σ_{l,η} = 𝒢_l^{full} - f_{l,η}` with the *compactly supported*
`f_{l,η} = (Γ_l(|x|) - Γ_l(η))_+`.  This is the slice version of `[RS] Lemma 3.5`
(`g * δ^{(η)} = g_η` on `ℝ^d × {0}`) and of `[PS17, §1.3]`; because `f_{l,η}` vanishes outside `B_η`,
interactions between charges with disjoint balls are *exactly* the point interactions.

Torus adaptation: the Euclidean construction is periodised (`η < 1/2`, the exponentially decaying
Yukawa kernel makes `∑_m` converge); for `l = 0` (Coulomb, `s = d-2`) the Newton kernel does not
periodise, but the periodic Green function `𝒢_0` satisfies `Δ 𝒢_0 = 1` off the origin, hence the
spherical mean of `𝒢_0(x - ·)` is `𝒢_0(x) + η²/(2d)` *exactly* (`Δ w ≡ 1 ⇒ mean_η w = w + η²/2d`):
Newton's theorem holds up to the additive constant `η²/(2d)`, which disappears from every force
`∇𝒢_0` and costs only `O(η²) = O(Λ λ^{d-s})` in the energy identity.
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator

variable {d : ℕ}

/-- The radial smearing measure `σ_{l,η}` on `ℝ^d` (ball part + sphere part, see above). -/
def smearEuc (d : ℕ) (l η : ℝ) : Measure (Euc d) :=
  ENNReal.ofReal (l * yukawa d l η) • (volume : Measure (Euc d)).restrict (Metric.closedBall 0 η) +
    ENNReal.ofReal (-(deriv (yukawa d l) η) * η ^ (d - 1)) •
      ((volume : Measure (Euc d)).toSphere.map (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)))

/-- `σ_{l,η}` seen on the torus (`η < 1/2`, so that the ball embeds). -/
def smearT (d : ℕ) (l η : ℝ) : Measure (Torus d) := (smearEuc d l η).map Torus.mk

/-- The uniform *probability* measure on the sphere `∂B_η ⊂ 𝕋^d` (the charge of the Coulomb slice
`l = 0`). -/
def sphereT (d : ℕ) (η : ℝ) : Measure (Torus d) :=
  (((volume : Measure (Euc d)).toSphere Set.univ)⁻¹ •
    ((volume : Measure (Euc d)).toSphere.map (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)))).map
      Torus.mk

/-- The compactly supported difference `f_{l,η} = (Γ_l(|x|) - Γ_l(η))_+` (`|x|` = torus norm,
`η < 1/2`). -/
def fTrunc (d : ℕ) (l η : ℝ) (z : Torus d) : ℝ :=
  max (yukawa d l ‖KernelGrad.centeredRep z‖ - yukawa d l η) 0

/-- The Newton profile: `Γ_0(r) = Γ(d/2-1) r^{2-d}/(4π^{d/2})` (`d ≥ 3`), `-log r/(2π)` (`d = 2`). -/
def newton (d : ℕ) (r : ℝ) : ℝ :=
  if d = 2 then -(1 / (2 * Real.pi)) * Real.log r
  else Real.Gamma ((d : ℝ) / 2 - 1) / (4 * Real.pi ^ ((d : ℝ) / 2)) * r ^ (2 - (d : ℝ))

/-- `f_{0,η} = (Γ_0(|x|) - Γ_0(η))_+` for the Coulomb slice. -/
def fTrunc0 (d : ℕ) (η : ℝ) (z : Torus d) : ℝ :=
  max (newton d ‖KernelGrad.centeredRep z‖ - newton d η) 0

/-- the sphere map `ω ↦ η ω` -/
def sphScale (d : ℕ) (η : ℝ) (ω : Metric.sphere (0 : Euc d) 1) : Euc d := η • (ω : Euc d)

theorem continuous_sphScale (d : ℕ) (η : ℝ) : Continuous (sphScale d η) := by
  unfold sphScale; fun_prop

theorem isFiniteMeasure_smearEuc (d : ℕ) (l η : ℝ) : IsFiniteMeasure (smearEuc d l η) := by
  unfold smearEuc
  have : IsFiniteMeasure ((volume : Measure (Euc d)).restrict (Metric.closedBall 0 η)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have := Measure.smul_finite ((volume : Measure (Euc d)).restrict (Metric.closedBall 0 η))
    (ENNReal.ofReal_ne_top (r := l * yukawa d l η))
  have := Measure.smul_finite (((volume : Measure (Euc d)).toSphere).map
      (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)))
    (ENNReal.ofReal_ne_top (r := -(deriv (yukawa d l) η) * η ^ (d - 1)))
  infer_instance

theorem smearEuc_neg (d : ℕ) (l η : ℝ) : (smearEuc d l η).map (fun x => -x) = smearEuc d l η := by
  unfold smearEuc
  have h1 : ((volume : Measure (Euc d)).restrict (Metric.closedBall 0 η)).map (fun x => -x) =
      (volume : Measure (Euc d)).restrict (Metric.closedBall 0 η) := by
    have := Measure.restrict_map (μ := (volume : Measure (Euc d))) (f := fun x : Euc d => -x)
      measurable_neg (s := Metric.closedBall 0 η) Metric.isClosed_closedBall.measurableSet
    have e : (fun x : Euc d => -x) ⁻¹' Metric.closedBall 0 η = Metric.closedBall 0 η := by
      ext x; simp
    rw [e] at this
    rw [← this, Measure.map_neg_eq_self]
  have h2 : (((volume : Measure (Euc d)).toSphere).map
        (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d))).map (fun x => -x) =
      ((volume : Measure (Euc d)).toSphere).map
        (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) := by
    have hm : Measurable (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) :=
      (continuous_sphScale d η).measurable
    rw [Measure.map_map measurable_neg hm]
    have e : ((fun x : Euc d => -x) ∘ (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d))) =
        (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) ∘ SmearAux.negS d := by
      funext ω; simp [SmearAux.negS]
    rw [e, ← Measure.map_map hm SmearAux.continuous_negS.measurable, SmearAux.toSphere_neg]
  rw [Measure.map_add _ _ (measurable_neg : Measurable (fun x : Euc d => -x)), Measure.map_smul,
    Measure.map_smul, h1, h2]
  all_goals exact measurable_neg.aemeasurable

theorem smearT_neg (d : ℕ) (l η : ℝ) : (smearT d l η).map (fun x => -x) = smearT d l η := by
  unfold smearT
  rw [Measure.map_map measurable_neg Torus.continuous_mk.measurable]
  have e : ((fun x : Torus d => -x) ∘ Torus.mk) = Torus.mk ∘ (fun x : Euc d => -x) := by
    funext x
    have : Torus.mk (-x) + Torus.mk x = 0 := by
      rw [← Torus.mk_add, neg_add_cancel]; funext i; simp [Torus.mk]
    simp only [Function.comp]
    exact (eq_neg_of_add_eq_zero_left this).symm
  rw [e, ← Measure.map_map Torus.continuous_mk.measurable measurable_neg, smearEuc_neg]

theorem smearEuc_compl (d : ℕ) (l η : ℝ) (hη : 0 < η) :
    smearEuc d l η (Metric.closedBall (0 : Euc d) η)ᶜ = 0 := by
  have hB : MeasurableSet (Metric.closedBall (0 : Euc d) η) := Metric.isClosed_closedBall.measurableSet
  unfold smearEuc
  have h1 : ((volume : Measure (Euc d)).restrict (Metric.closedBall 0 η)) (Metric.closedBall 0 η)ᶜ = 0 := by
    rw [Measure.restrict_apply hB.compl]; simp
  have h2 : (((volume : Measure (Euc d)).toSphere).map
      (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d))) (Metric.closedBall 0 η)ᶜ = 0 := by
    rw [Measure.map_apply (show Measurable (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) from
      (continuous_sphScale d η).measurable) hB.compl]
    have : (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) ⁻¹' (Metric.closedBall 0 η)ᶜ = ∅ := by
      ext ω
      simp only [mem_preimage, mem_compl_iff, Metric.mem_closedBall, dist_zero_right, norm_smul,
        Real.norm_eq_abs, mem_empty_iff_false, iff_false, not_not]
      have : ‖(ω : Euc d)‖ = 1 := by simp
      rw [this, mul_one, abs_of_pos hη]
    rw [this]; simp
  simp [h1, h2]

theorem smearT_compl (d : ℕ) (l η : ℝ) (hη : 0 < η) :
    smearT d l η ((Torus.mk '' Metric.closedBall (0 : Euc d) η)ᶜ) = 0 := by
  have hc : IsClosed (Torus.mk '' Metric.closedBall (0 : Euc d) η) :=
    ((isCompact_closedBall (0 : Euc d) η).image Torus.continuous_mk).isClosed
  unfold smearT
  rw [Measure.map_apply Torus.continuous_mk.measurable hc.measurableSet.compl]
  refine measure_mono_null ?_ (smearEuc_compl d l η hη)
  intro x hx
  simp only [mem_preimage, mem_compl_iff] at hx ⊢
  exact fun h => hx ⟨x, h, rfl⟩

theorem smearEuc_real_univ (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) :
    (smearEuc d l η).real Set.univ =
      l * yukawa d l η * (η ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1)) +
        (-(deriv (yukawa d l) η) * η ^ (d - 1)) * (volume : Measure (Euc d)).toSphere.real Set.univ := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  have hG0 : 0 ≤ l * yukawa d l η := (mul_pos hl ((yukawa_ode hd hl).1 η hη)).le
  have hG1 : 0 ≤ -(deriv (yukawa d l) η) * η ^ (d - 1) :=
    mul_nonneg (by linarith [SmearAux.deriv_yukawa_neg hd hl hη]) (pow_pos hη _).le
  unfold smearEuc
  have hB : MeasurableSet (Metric.closedBall (0 : Euc d) η) := Metric.isClosed_closedBall.measurableSet
  have hm : Measurable (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) :=
    (continuous_sphScale d η).measurable
  have hfin : IsFiniteMeasure ((volume : Measure (Euc d)).restrict (Metric.closedBall 0 η)) :=
    ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  have h1 : ((volume : Measure (Euc d)).restrict (Metric.closedBall 0 η)).real Set.univ =
      η ^ d * (volume : Measure (Euc d)).real (Metric.ball 0 1) := by
    rw [measureReal_def, Measure.restrict_apply_univ, Measure.addHaar_closedBall _ _ hη.le, hfr,
      ENNReal.toReal_mul, ENNReal.toReal_ofReal (pow_nonneg hη.le _)]
    rfl
  have h2 : (((volume : Measure (Euc d)).toSphere).map
      (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d))).real Set.univ =
      (volume : Measure (Euc d)).toSphere.real Set.univ := by
    rw [measureReal_def, measureReal_def, Measure.map_apply hm MeasurableSet.univ]; rfl
  rw [measureReal_def, Measure.add_apply, Measure.smul_apply, Measure.smul_apply, smul_eq_mul, smul_eq_mul,
    ENNReal.toReal_add (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _))
      (ENNReal.mul_ne_top ENNReal.ofReal_ne_top (measure_ne_top _ _)),
    ENNReal.toReal_mul, ENNReal.toReal_mul, ENNReal.toReal_ofReal hG0, ENNReal.toReal_ofReal hG1]
  rw [← measureReal_def, ← measureReal_def, h1, h2]

theorem integral_fTrunc (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∫ z : Torus d, fTrunc d l η z =
      (volume : Measure (Euc d)).toSphere.real Set.univ *
        ((∫ r in Set.Ioc 0 η, r ^ (d - 1) * yukawa d l r) - yukawa d l η * (η ^ d / d)) := by
  have hyk := yukawa_ode hd hl
  have hF : ∀ r, η ≤ r → max (yukawa d l r - yukawa d l η) 0 = 0 := by
    intro r hr
    rw [max_eq_right]
    rcases eq_or_lt_of_le hr with h | h
    · rw [← h]; simp
    · have := hyk.2.1 η r hη h
      linarith
  have h1 := SmearAux.integral_torus_radial hd hη2 (fun r => max (yukawa d l r - yukawa d l η) 0) hF
  have e : ∀ z : Torus d, fTrunc d l η z = max (yukawa d l ‖KernelGrad.centeredRep z‖ - yukawa d l η) 0 :=
    fun z => rfl
  simp_rw [e]
  rw [h1]
  congr 1
  obtain ⟨hint, -⟩ := SmearAux.int_flux hd hl hη
  have h2 : ∫ r in Set.Ioi (0 : ℝ), r ^ (d - 1) * max (yukawa d l r - yukawa d l η) 0 =
      ∫ r in Set.Ioc (0 : ℝ) η, r ^ (d - 1) * max (yukawa d l r - yukawa d l η) 0 := by
    refine setIntegral_eq_of_subset_of_forall_sdiff_eq_zero measurableSet_Ioi Set.Ioc_subset_Ioi_self ?_
    intro r hr
    have : η ≤ r := by
      by_contra h
      push_neg at h
      exact hr.2 ⟨hr.1, h.le⟩
    rw [hF r this, mul_zero]
  rw [h2]
  have h3 : ∫ r in Set.Ioc (0 : ℝ) η, r ^ (d - 1) * max (yukawa d l r - yukawa d l η) 0 =
      ∫ r in Set.Ioc (0 : ℝ) η, (r ^ (d - 1) * yukawa d l r - yukawa d l η * r ^ (d - 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun r hr => ?_
    rw [max_eq_left]
    · ring
    · rcases eq_or_lt_of_le hr.2 with h | h
      · rw [h]; simp
      · have := hyk.2.1 r η hr.1 h
        linarith
  have h4 : ∫ r in Set.Ioc (0 : ℝ) η, yukawa d l η * r ^ (d - 1) = yukawa d l η * (η ^ d / d) := by
    rw [integral_const_mul]
    congr 1
    rw [← intervalIntegral.integral_of_le hη.le, integral_pow]
    have : d - 1 + 1 = d := by omega
    rw [this]
    simp [zero_pow (by omega : d ≠ 0), Nat.cast_sub hd]
  have hint2 : IntegrableOn (fun r : ℝ => yukawa d l η * r ^ (d - 1)) (Set.Ioc 0 η) :=
    (continuous_const.mul (continuous_pow _)).integrableOn_Ioc
  rw [h3, integral_sub hint hint2, h4]

theorem smearT_real_univ (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) :
    (smearT d l η).real Set.univ = 1 - l * ∫ z, fTrunc d l η z := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  have hfr : Module.finrank ℝ (Euc d) = d := by simp
  have e1 : (smearT d l η).real Set.univ = (smearEuc d l η).real Set.univ := by
    unfold smearT
    rw [measureReal_def, measureReal_def, Measure.map_apply Torus.continuous_mk.measurable MeasurableSet.univ]
    rfl
  rw [e1, smearEuc_real_univ hd hl hη, integral_fTrunc hd hl hη hη2]
  obtain ⟨-, hF1⟩ := SmearAux.int_flux hd hl hη
  have hF2 := SmearAux.sphere_mass_mul_flux (d := d) hd
  have hF3 : (volume : Measure (Euc d)).toSphere.real Set.univ =
      d * (volume : Measure (Euc d)).real (Metric.ball 0 1) := by
    rw [Measure.toSphere_real_apply_univ, hfr]
  generalize (volume : Measure (Euc d)).toSphere.real Set.univ = S at hF2 hF3 ⊢
  generalize (volume : Measure (Euc d)).real (Metric.ball 0 1) = ω at hF3 ⊢
  generalize Real.Gamma ((d : ℝ) / 2) / (2 * Real.pi ^ ((d : ℝ) / 2)) = κ at hF1 hF2
  generalize (∫ r in Set.Ioc (0 : ℝ) η, r ^ (d - 1) * yukawa d l r) = I at hF1 ⊢
  have hd0 : (d : ℝ) ≠ 0 := by
    have : (0:ℝ) < d := by exact_mod_cast hd
    exact this.ne'
  have hω : ω = S / d := by rw [hF3]; field_simp
  have hpow : η ^ d = η * η ^ (d - 1) := by
    rw [← pow_succ']; congr 1; omega
  rw [hω]
  have : l * (S * (I - yukawa d l η * (η ^ d / d))) = S * (l * I) - l * yukawa d l η * η ^ d * S / d := by
    field_simp
  rw [this, hF1]
  field_simp
  linear_combination (d : ℝ) * hF2

/-- **S2.1 (structure of the charge).**  For `l > 0`, `0 < η < 1/2`: `σ_{l,η}` is a finite measure,
even (`x ↦ -x` invariant), carried by the closed ball, with total mass `1 - l ∫ f_{l,η}`. -/
theorem smearT_structure (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) :
    IsFiniteMeasure (smearT d l η) ∧
    (smearT d l η).map (fun x => -x) = smearT d l η ∧
    smearT d l η ((Torus.mk '' Metric.closedBall (0 : Euc d) η)ᶜ) = 0 ∧
    (smearT d l η).real Set.univ = 1 - l * ∫ z, fTrunc d l η z := by
  refine ⟨?_, smearT_neg d l η, smearT_compl d l η hη, smearT_real_univ hd hl hη hη2⟩
  have := isFiniteMeasure_smearEuc d l η
  unfold smearT
  infer_instance

theorem integral_smearEuc (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) {φ : Euc d → ℝ}
    (hφ : Continuous φ) :
    ∫ y, φ y ∂(smearEuc d l η) =
      l * yukawa d l η * (∫ y in Metric.closedBall (0 : Euc d) η, φ y) +
        (-(deriv (yukawa d l) η) * η ^ (d - 1)) * SmearAux.Phi φ η := by
  have hG0 : 0 ≤ l * yukawa d l η := (mul_pos hl ((yukawa_ode hd hl).1 η hη)).le
  have hG1 : 0 ≤ -(deriv (yukawa d l) η) * η ^ (d - 1) :=
    mul_nonneg (by linarith [SmearAux.deriv_yukawa_neg hd hl hη]) (pow_pos hη _).le
  have hm : Measurable (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) :=
    (continuous_sphScale d η).measurable
  have hi1 : Integrable φ ((volume : Measure (Euc d)).restrict (Metric.closedBall 0 η)) :=
    hφ.continuousOn.integrableOn_compact (isCompact_closedBall _ _)
  have hi2 : Integrable φ (((volume : Measure (Euc d)).toSphere).map
      (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d))) := by
    rw [integrable_map_measure hφ.aestronglyMeasurable hm.aemeasurable]
    exact SmearAux.integrable_sphere (hφ.comp (by fun_prop))
  unfold smearEuc
  rw [integral_add_measure (hi1.smul_measure ENNReal.ofReal_ne_top) (hi2.smul_measure ENNReal.ofReal_ne_top),
    integral_smul_measure, integral_smul_measure, ENNReal.toReal_ofReal hG0, ENNReal.toReal_ofReal hG1,
    integral_map hm.aemeasurable hφ.aestronglyMeasurable]
  simp only [smul_eq_mul]
  rfl

theorem smearEuc_singleton (hd : 2 ≤ d) (l η : ℝ) (hη : 0 < η) (z : Euc d) : smearEuc d l η {z} = 0 := by
  have hm : Measurable (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) :=
    (continuous_sphScale d η).measurable
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  unfold smearEuc
  have h1 : ((volume : Measure (Euc d)).restrict (Metric.closedBall 0 η)) {z} = 0 := by
    rw [Measure.restrict_apply (measurableSet_singleton z)]
    exact measure_mono_null Set.inter_subset_left (measure_singleton z)
  have h2 : (((volume : Measure (Euc d)).toSphere).map
      (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d))) {z} = 0 := by
    rw [Measure.map_apply hm (measurableSet_singleton z)]
    by_cases h : ∃ ω₀ : Metric.sphere (0 : Euc d) 1, η • (ω₀ : Euc d) = z
    · obtain ⟨ω₀, hω₀⟩ := h
      refine measure_mono_null ?_ (SmearAux.toSphere_singleton hd ω₀)
      intro ω hω
      have : η • (ω : Euc d) = η • (ω₀ : Euc d) := by rw [hω₀]; exact hω
      have := smul_right_injective (Euc d) hη.ne' this
      exact Subtype.ext this
    · push Not at h
      have : (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) ⁻¹' {z} = ∅ := by
        ext ω; simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]; exact h ω
      rw [this]; simp
  simp [h1, h2]

theorem newton_smear (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (z : Euc d)
    (hz : smearEuc d l η {z} = 0) :
    ∫⁻ y, ENNReal.ofReal (yukawa d l ‖y - z‖) ∂(smearEuc d l η) =
      ENNReal.ofReal (yukawa d l (max ‖z‖ η)) := by
  have := isFiniteMeasure_smearEuc d l η
  refine SmearAux.newton_yukawa hd hl hη z _ (fun s hs => ?_) ?_
  · rw [integral_smearEuc hd hl hη (SmearAux.contDiff_gφ s z).continuous]
    ring
  · have := (measure_eq_zero_iff_ae_notMem).1 hz
    filter_upwards [this] with y hy
    simpa using hy

theorem sliceGfull_conv_smear_core (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2)
    (x : Torus d) (hx : x ≠ 0)
    (hper : ∀ᵐ y ∂(smearEuc d l η),
      Summable (fun m : Lattice d => yukawa d l ‖(KernelGrad.centeredRep x - y) - Lattice.toEuc m‖) ∧
        sliceGfull d l (x - Torus.mk y) =
          ∑' m : Lattice d, yukawa d l ‖(KernelGrad.centeredRep x - y) - Lattice.toEuc m‖)
    (hNewt : ∀ m : Lattice d, ∫⁻ y, ENNReal.ofReal (yukawa d l ‖y - (KernelGrad.centeredRep x - Lattice.toEuc m)‖)
      ∂(smearEuc d l η) =
        ENNReal.ofReal (yukawa d l (max ‖KernelGrad.centeredRep x - Lattice.toEuc m‖ η))) :
    Integrable (fun y => sliceGfull d l (x - Torus.mk y)) (smearEuc d l η) ∧
    ∫ y, sliceGfull d l (x - y) ∂(smearT d l η) = sliceGfull d l x - fTrunc d l η x := by
  set x' : Euc d := KernelGrad.centeredRep x with hx'
  have hmk : Torus.mk x' = x := KernelGrad.mk_centeredRep x
  have hx'box : ∀ i, |x' i| ≤ 1 / 2 := KernelGrad.abs_centeredRep_le x
  have hfin := isFiniteMeasure_smearEuc d l η
  have hyk := yukawa_ode hd hl
  set ν := smearEuc d l η with hν
  -- Step 1: pull back to `ℝ^d`
  have hF : Measurable (fun w : Torus d => sliceGfull d l (x - w)) :=
    (SmearAux.measurable_sliceGfull l).comp (measurable_const.sub measurable_id)
  have step1 : ∫ y, sliceGfull d l (x - y) ∂(smearT d l η) =
      ∫ y, sliceGfull d l (x - Torus.mk y) ∂ν :=
    integral_map Torus.continuous_mk.measurable.aemeasurable hF.aestronglyMeasurable
  rw [step1]
  -- the lattice sum
  have hnorm_pos : ∀ (v : Euc d), Torus.mk v ≠ 0 → ∀ m : Lattice d, 0 < ‖v - Lattice.toEuc m‖ := by
    intro v hv m
    refine norm_pos_iff.2 fun h => hv ?_
    have : v = Lattice.toEuc m := sub_eq_zero.1 h
    rw [this, SliceAux.mk_toEuc']
  set G : Euc d → ℝ := fun y => ∑' m : Lattice d, yukawa d l ‖(x' - y) - Lattice.toEuc m‖ with hG
  have hGeq : ∀ᵐ y ∂ν, sliceGfull d l (x - Torus.mk y) = G y ∧
      Summable (fun m : Lattice d => yukawa d l ‖(x' - y) - Lattice.toEuc m‖) :=
    hper.mono fun y hy => ⟨hy.2, hy.1⟩
  have hGnn : ∀ᵐ y ∂ν, 0 ≤ G y :=
    Eventually.of_forall fun y => tsum_nonneg fun m => SmearAux.yukawa_nonneg d l _
  have hterm : ∀ m : Lattice d, Measurable fun y : Euc d => yukawa d l ‖(x' - y) - Lattice.toEuc m‖ :=
    fun m => (SmearAux.measurable_yukawa l).comp (measurable_norm.comp (measurable_const.sub measurable_id |>.sub_const _))
  have hGm : Measurable G := Measurable.tsum hterm
  have step2 : ∫ y, sliceGfull d l (x - Torus.mk y) ∂ν = ∫ y, G y ∂ν :=
    integral_congr_ae (hGeq.mono fun y hy => hy.1)
  rw [step2, integral_eq_lintegral_of_nonneg_ae hGnn hGm.aestronglyMeasurable]
  have hlint : ∫⁻ y, ENNReal.ofReal (G y) ∂ν =
      ∑' m : Lattice d, ENNReal.ofReal (yukawa d l (max ‖x' - Lattice.toEuc m‖ η)) := by
    have e1 : ∀ᵐ y ∂ν, ENNReal.ofReal (G y) =
        ∑' m : Lattice d, ENNReal.ofReal (yukawa d l ‖(x' - y) - Lattice.toEuc m‖) := by
      filter_upwards [hGeq] with y hy
      exact ENNReal.ofReal_tsum_of_nonneg (fun m => SmearAux.yukawa_nonneg d l _) hy.2
    rw [lintegral_congr_ae e1, lintegral_tsum (fun m => (hterm m).ennreal_ofReal.aemeasurable)]
    refine tsum_congr fun m => ?_
    rw [← hNewt m]
    refine lintegral_congr fun y => ?_
    have : (x' - y) - Lattice.toEuc m = -(y - (x' - Lattice.toEuc m)) := by abel
    simp only [this, norm_neg]
  have hxne : Torus.mk x' ≠ 0 := by rw [hmk]; exact hx
  obtain ⟨hsumΓ, hperx⟩ := SmearAux.periodization_vec hl hxne
  rw [hmk] at hperx
  have hpos : ∀ m : Lattice d, 0 < ‖x' - Lattice.toEuc m‖ := hnorm_pos x' hxne
  set fm : Lattice d → ℝ := fun m => max (yukawa d l ‖x' - Lattice.toEuc m‖ - yukawa d l η) 0 with hfm
  have hfm0 : ∀ m : Lattice d, m ≠ 0 → fm m = 0 := by
    intro m hm
    have h1 := SmearAux.one_half_le_norm_sub m hm hx'box
    have h2 : yukawa d l ‖x' - Lattice.toEuc m‖ ≤ yukawa d l η := by
      have := hyk.2.1 η ‖x' - Lattice.toEuc m‖ hη (by linarith)
      exact this.le
    simp only [hfm]
    exact max_eq_right (by linarith)
  have hsumf : Summable fm := summable_of_ne_finset_zero (s := {0}) fun m hm => hfm0 m (by simpa using hm)
  have hsumF : ∑' m, fm m = fTrunc d l η x := by
    rw [tsum_eq_single 0 (fun m hm => hfm0 m hm)]
    simp only [hfm, SmearAux.toEuc_zero, sub_zero]
    rfl
  have ha : ∀ m : Lattice d, yukawa d l (max ‖x' - Lattice.toEuc m‖ η) =
      yukawa d l ‖x' - Lattice.toEuc m‖ - fm m := fun m =>
    SmearAux.yukawa_max_eq hd hl hη (hpos m)
  have hsuma : Summable (fun m : Lattice d => yukawa d l (max ‖x' - Lattice.toEuc m‖ η)) := by
    simp_rw [ha]; exact hsumΓ.sub hsumf
  have hnna : ∀ m : Lattice d, 0 ≤ yukawa d l (max ‖x' - Lattice.toEuc m‖ η) := fun m =>
    (hyk.1 _ (lt_of_lt_of_le hη (le_max_right _ _))).le
  have hGint : Integrable G ν := by
    refine ⟨hGm.aestronglyMeasurable, ?_⟩
    rw [hasFiniteIntegral_iff_ofReal hGnn, hlint, ← ENNReal.ofReal_tsum_of_nonneg hnna hsuma]
    exact ENNReal.ofReal_lt_top
  refine ⟨hGint.congr (hGeq.mono fun y hy => hy.1.symm), ?_⟩
  rw [hlint, ← ENNReal.ofReal_tsum_of_nonneg hnna hsuma, ENNReal.toReal_ofReal (tsum_nonneg hnna)]
  simp_rw [ha]
  rw [hsumΓ.tsum_sub hsumf, hsumF, ← hperx]

theorem eq_of_mk_sub_eq_zero {η : ℝ} (hη2 : η < 1 / 2) {x' y : Euc d} (hx'box : ∀ i, |x' i| ≤ 1 / 2)
    (hy : ‖y‖ ≤ η) (h0 : Torus.mk (x' - y) = 0) : y = x' := by
  obtain ⟨m, hm⟩ := SliceAux.exists_lattice_of_mk_eq (h0.trans SmearAux.mk_zero'.symm)
  have hm0 : m = 0 := by
    funext i
    have h1 : |((m i : ℤ) : ℝ)| < 1 := by
      have e : ((m i : ℤ) : ℝ) = x' i - y i := by
        have := congrFun (congrArg (fun v : Euc d => v.ofLp) hm) i
        simpa [Lattice.toEuc] using this.symm
      rw [e]
      have h2 := hx'box i
      have h3 : |y i| ≤ η := (SmearAux.abs_apply_le_norm y i).trans hy
      calc |x' i - y i| ≤ |x' i| + |y i| := abs_sub _ _
        _ < 1 := by linarith
    have : |m i| < 1 := by exact_mod_cast h1
    simp only [Pi.zero_apply]
    exact abs_lt.1 this |> fun h => by omega
  rw [hm0, SmearAux.toEuc_zero] at hm
  have := sub_eq_zero.1 (by simpa using hm : x' - y = 0)
  exact this.symm

theorem sliceGfull_conv_smear_gen (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2)
    (x : Torus d) (hx : x ≠ 0) (hnull : smearEuc d l η {KernelGrad.centeredRep x} = 0) :
    Integrable (fun y => sliceGfull d l (x - Torus.mk y)) (smearEuc d l η) ∧
    ∫ y, sliceGfull d l (x - y) ∂(smearT d l η) = sliceGfull d l x - fTrunc d l η x := by
  set x' : Euc d := KernelGrad.centeredRep x with hx'
  have hmk : Torus.mk x' = x := KernelGrad.mk_centeredRep x
  have hx'box : ∀ i, |x' i| ≤ 1 / 2 := KernelGrad.abs_centeredRep_le x
  set ν := smearEuc d l η with hν
  refine sliceGfull_conv_smear_core hd hl hη hη2 x hx ?_ ?_
  · have hsupp : ∀ᵐ y ∂ν, y ∈ Metric.closedBall (0 : Euc d) η := by
      rw [ae_iff]
      exact smearEuc_compl d l η hη
    have hne : ∀ᵐ y ∂ν, y ≠ x' := by
      have := (measure_eq_zero_iff_ae_notMem).1 hnull
      filter_upwards [this] with y hy
      simpa using hy
    filter_upwards [hsupp, hne] with y hy hyx
    have hy0 : Torus.mk (x' - y) ≠ 0 := fun h0 =>
      hyx (eq_of_mk_sub_eq_zero hη2 hx'box (by simpa using hy) h0)
    have h := SmearAux.periodization_vec hl hy0
    have e : Torus.mk (x' - y) = x - Torus.mk y := by rw [SmearAux.mk_sub_eq, hmk]
    rw [e] at h
    exact ⟨h.1, h.2⟩
  · intro m
    have hz : ν {x' - Lattice.toEuc m} = 0 := by
      by_cases hm : m = 0
      · subst hm
        simpa [SmearAux.toEuc_zero] using hnull
      · refine measure_mono_null ?_ (smearEuc_compl d l η hη)
        intro z hz
        have hz' : z = x' - Lattice.toEuc m := hz
        have := SmearAux.one_half_le_norm_sub m hm hx'box
        simp only [mem_compl_iff, Metric.mem_closedBall, dist_zero_right, not_le]
        rw [hz']; linarith
    exact newton_smear hd hl hη _ hz

theorem sliceGfull_conv_smear_d1 (hd : d = 1) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2)
    (x : Torus d) (hx : x ≠ 0) :
    Integrable (fun y => sliceGfull d l (x - Torus.mk y)) (smearEuc d l η) ∧
    ∫ y, sliceGfull d l (x - y) ∂(smearT d l η) = sliceGfull d l x - fTrunc d l η x := by
  subst hd
  have hd1 : 1 ≤ 1 := le_rfl
  set x' : Euc 1 := KernelGrad.centeredRep x with hx'
  have hmk : Torus.mk x' = x := KernelGrad.mk_centeredRep x
  have hx'box : ∀ i, |x' i| ≤ 1 / 2 := KernelGrad.abs_centeredRep_le x
  set ν := smearEuc 1 l η with hν
  have hfin := isFiniteMeasure_smearEuc 1 l η
  refine sliceGfull_conv_smear_core hd1 hl hη hη2 x hx ?_ ?_
  · have hsupp : ∀ᵐ y ∂ν, y ∈ Metric.closedBall (0 : Euc 1) η := by
      rw [ae_iff]
      exact smearEuc_compl 1 l η hη
    filter_upwards [hsupp] with y hy
    show Summable (fun m : Lattice 1 => yukawa 1 l ‖(x' - y) - Lattice.toEuc m‖) ∧
      sliceGfull 1 l (x - Torus.mk y) = ∑' m : Lattice 1, yukawa 1 l ‖(x' - y) - Lattice.toEuc m‖
    have e : Torus.mk (x' - y) = x - Torus.mk y := by rw [SmearAux.mk_sub_eq, hmk]
    by_cases h0 : Torus.mk (x' - y) = 0
    · have hyx : y = x' := eq_of_mk_sub_eq_zero hη2 hx'box (by simpa using hy) h0
      have : x - Torus.mk y = 0 := by rw [← e]; exact h0
      rw [this]
      have h := SmearAux.periodization_zero_d1 hl
      have e2 : ∀ m : Lattice 1, ‖(x' - y) - Lattice.toEuc m‖ = ‖Lattice.toEuc m‖ := by
        intro m; rw [hyx]; simp [norm_neg]
      refine ⟨?_, ?_⟩
      · simp_rw [e2]; exact SmearAux.summable_yukawa_d1 hl
      · simp_rw [e2]; exact h
    · have h := SmearAux.periodization_vec hl h0
      rw [e] at h
      exact ⟨h.1, h.2⟩
  · intro m
    refine SmearAux.newton_yukawa' hd1 hl hη _ ν (fun s hs => ?_) (Eventually.of_forall fun y => ?_)
    · rw [integral_smearEuc hd1 hl hη (SmearAux.contDiff_gφ s _).continuous]
      ring
    · exact SmearAux.integrableOn_yk_d1 hl (norm_nonneg _)

theorem sliceGfull_conv_smear_all (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2)
    (x : Torus d) (hx : x ≠ 0) :
    Integrable (fun y => sliceGfull d l (x - Torus.mk y)) (smearEuc d l η) ∧
    ∫ y, sliceGfull d l (x - y) ∂(smearT d l η) = sliceGfull d l x - fTrunc d l η x := by
  by_cases hd2 : 2 ≤ d
  · exact sliceGfull_conv_smear_gen hd hl hη hη2 x hx (smearEuc_singleton hd2 l η hη _)
  · exact sliceGfull_conv_smear_d1 (by omega) hl hη hη2 x hx

/-- **S2.2 (Newton's theorem for `l - Δ`, exact).**  For `l > 0`, `0 < η < 1/2` and every `x ≠ 0`:
`∫ 𝒢_l^{full}(x - y) dσ_{l,η}(y) = 𝒢_l^{full}(x) - f_{l,η}(x)`; in particular
`= 𝒢_l^{full}(x)` for `|x| ≥ η`.
*Proof.*  `(l - Δ) u_{l,η} = σ_{l,η}` weakly (radial Green identity, 1D integration by parts after
polar coordinates), `u^{per} = 𝒢^{full} - f^{per}` and `𝒢^{full} * (l - Δ) u = u` by Fourier
(`sliceGfull_periodization`, the Fourier coefficient of `u^{per}` is `σ̂(k)/(l + 4π²|k|²)`). -/
theorem sliceGfull_conv_smear (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2)
    (x : Torus d) (hx : x ≠ 0) :
    ∫ y, sliceGfull d l (x - y) ∂(smearT d l η) = sliceGfull d l x - fTrunc d l η x :=
  (sliceGfull_conv_smear_all hd hl hη hη2 x hx).2

/-- **S2.3 (positivity of the weights).**  `Γ_l' < 0` on `(0,∞)` (so the sphere weight
`-Γ_l'(η) η^{d-1}` is positive and `smearEuc` is the positive measure it appears to be) and
`fTrunc ≥ 0`, supported in `B_η`. -/
theorem fTrunc_support (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) :
    (∀ z, 0 ≤ fTrunc d l η z) ∧ (∀ z : Torus d, η ≤ ‖KernelGrad.centeredRep z‖ → fTrunc d l η z = 0) ∧
    (∀ r : ℝ, 0 < r → deriv (yukawa d l) r < 0) := by
  refine ⟨fun z => le_max_right _ _, fun z hz => ?_, fun r hr => SmearAux.deriv_yukawa_neg hd hl hr⟩
  unfold fTrunc
  rw [max_eq_right]
  rcases eq_or_lt_of_le hz with h | h
  · rw [← h]; simp
  · have := (yukawa_ode hd hl).2.1 η _ hη h
    linarith

namespace SmearAux

theorem hasDerivAt_newton (hd : 2 ≤ d) {r : ℝ} (hr : 0 < r) :
    HasDerivAt (newton d) (-(kappa d) / r ^ (d - 1)) r := by
  by_cases h2 : d = 2
  · subst h2
    have := ((Real.hasDerivAt_log hr.ne').const_mul (-(1 / (2 * Real.pi))))
    have e : newton 2 = fun r => -(1 / (2 * Real.pi)) * Real.log r := by
      funext r; simp [newton]
    rw [e]
    have h1 : ((2:ℕ):ℝ) / 2 = 1 := by norm_num
    have hk : kappa 2 = 1 / (2 * Real.pi) := by
      unfold kappa; rw [h1, Real.Gamma_one, Real.rpow_one]
    rw [hk]
    refine this.congr_deriv ?_
    have : (2 - 1 : ℕ) = 1 := rfl
    rw [this, pow_one]
    field_simp
  · have hd3 : 3 ≤ d := by omega
    have hdr : (3:ℝ) ≤ d := by exact_mod_cast hd3
    have e : newton d = fun r => Real.Gamma ((d : ℝ) / 2 - 1) / (4 * Real.pi ^ ((d : ℝ) / 2)) * r ^ (2 - (d : ℝ)) := by
      funext r; simp [newton, h2]
    rw [e]
    have := (Real.hasDerivAt_rpow_const (x := r) (p := 2 - (d : ℝ)) (Or.inl hr.ne')).const_mul
      (Real.Gamma ((d : ℝ) / 2 - 1) / (4 * Real.pi ^ ((d : ℝ) / 2)))
    convert this using 1
    have hp : r ^ (2 - (d : ℝ) - 1) = 1 / r ^ (d - 1) := by
      rw [show (2 - (d : ℝ) - 1) = -((d - 1 : ℕ) : ℝ) by rw [Nat.cast_sub (by omega)]; push_cast; ring,
        Real.rpow_neg hr.le, Real.rpow_natCast, one_div]
    rw [hp]
    have hG : Real.Gamma ((d : ℝ) / 2) = ((d : ℝ) / 2 - 1) * Real.Gamma ((d : ℝ) / 2 - 1) := by
      have := Real.Gamma_add_one (s := (d : ℝ) / 2 - 1) (by linarith)
      rw [show (d : ℝ) / 2 - 1 + 1 = (d : ℝ) / 2 by ring] at this
      exact this
    unfold kappa
    rw [hG]
    have hpi : (0:ℝ) < Real.pi ^ ((d : ℝ) / 2) := by positivity
    field_simp
    ring



theorem f_sandwich (hd : 2 ≤ d) {l η r : ℝ} (hl : 0 < l) (hr : 0 < r) (hrη : r ≤ η) :
    0 ≤ (newton d r - newton d η) - (yukawa d l r - yukawa d l η) ∧
    (newton d r - newton d η) - (yukawa d l r - yukawa d l η) ≤
      Aint d l η * ∫ s in r..η, 1 / s ^ (d - 1) := by
  have hd1 : 1 ≤ d := by omega
  have hη : 0 < η := lt_of_lt_of_le hr hrη
  have hpos : ∀ s ∈ Icc r η, 0 < s := fun s hs => lt_of_lt_of_le hr hs.1
  -- FTC for yukawa
  have h1 : ∫ s in r..η, -deriv (yukawa d l) s = yukawa d l r - yukawa d l η := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := r) (b := η) (f := fun s => -yukawa d l s)
      (f' := fun s => -deriv (yukawa d l) s) (fun s hs => by
        rw [uIcc_of_le hrη] at hs
        exact (hasDerivAt_yukawa hd1 hl (hpos s hs)).neg) (by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hrη]
        exact fun s hs => (continuousAt_deriv_yukawa hd1 hl (hpos s hs)).neg.continuousWithinAt)
    rw [this]; ring
  have h2 : ∫ s in r..η, kappa d / s ^ (d - 1) = newton d r - newton d η := by
    have := intervalIntegral.integral_eq_sub_of_hasDerivAt (a := r) (b := η) (f := fun s => -newton d s)
      (f' := fun s => kappa d / s ^ (d - 1)) (fun s hs => by
        rw [uIcc_of_le hrη] at hs
        have := (hasDerivAt_newton hd (hpos s hs)).neg
        convert this using 1
        ring) (by
        refine ContinuousOn.intervalIntegrable ?_
        rw [uIcc_of_le hrη]
        exact continuousOn_const.div (continuousOn_id.pow _) fun s hs => (pow_pos (hpos s hs) _).ne')
    rw [this]; ring
  have hint1 : IntervalIntegrable (fun s => -deriv (yukawa d l) s) volume r η := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hrη]
    exact fun s hs => (continuousAt_deriv_yukawa hd1 hl (hpos s hs)).neg.continuousWithinAt
  have hint2 : IntervalIntegrable (fun s => kappa d / s ^ (d - 1)) volume r η := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hrη]
    exact continuousOn_const.div (continuousOn_id.pow _) fun s hs => (pow_pos (hpos s hs) _).ne'
  have hint3 : IntervalIntegrable (fun s : ℝ => 1 / s ^ (d - 1)) volume r η := by
    refine ContinuousOn.intervalIntegrable ?_
    rw [uIcc_of_le hrη]
    exact continuousOn_const.div (continuousOn_id.pow _) fun s hs => (pow_pos (hpos s hs) _).ne'
  have hdiff : (newton d r - newton d η) - (yukawa d l r - yukawa d l η) =
      ∫ s in r..η, (kappa d / s ^ (d - 1) - -deriv (yukawa d l) s) := by
    rw [intervalIntegral.integral_sub hint2 hint1, h1, h2]
  rw [hdiff]
  have hpt : ∀ s ∈ Icc r η, kappa d / s ^ (d - 1) - -deriv (yukawa d l) s = Aint d l s / s ^ (d - 1) := by
    intro s hs
    rw [neg_deriv_yukawa_eq hd1 hl (hpos s hs)]
    ring
  have hcongr : ∫ s in r..η, (kappa d / s ^ (d - 1) - -deriv (yukawa d l) s) =
      ∫ s in r..η, Aint d l s / s ^ (d - 1) := by
    refine intervalIntegral.integral_congr fun s hs => ?_
    rw [uIcc_of_le hrη] at hs
    exact hpt s hs
  rw [hcongr]
  constructor
  · refine intervalIntegral.integral_nonneg hrη fun s hs => ?_
    exact div_nonneg (Aint_nonneg hd1 hl s) (pow_pos (hpos s hs) _).le
  · have hc : ∫ s in r..η, Aint d l η * (1 / s ^ (d - 1)) = Aint d l η * ∫ s in r..η, 1 / s ^ (d - 1) :=
      intervalIntegral.integral_const_mul _ _
    rw [← hc]
    refine intervalIntegral.integral_mono_on hrη ?_ (hint3.const_mul _) fun s hs => ?_
    · have h3 := hint2.sub hint1
      refine h3.congr (fun s hs => ?_)
      rw [uIoc_of_le hrη] at hs
      exact hpt s (Ioc_subset_Icc_self hs)
    · have := Aint_mono hd1 hl (hpos s hs) hη hs.2
      rw [mul_one_div]
      exact div_le_div_of_nonneg_right this (pow_pos (hpos s hs) _).le



/-- ball part of `smearEuc` -/
abbrev ballPart (d : ℕ) (η : ℝ) : Measure (Euc d) := (volume : Measure (Euc d)).restrict (Metric.closedBall 0 η)
/-- sphere part of `smearEuc` -/
abbrev spherePart (d : ℕ) (η : ℝ) : Measure (Euc d) :=
  ((volume : Measure (Euc d)).toSphere).map (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d))

theorem coef_pos (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) :
    0 < l * yukawa d l η ∧ 0 < -(deriv (yukawa d l) η) * η ^ (d - 1) :=
  ⟨mul_pos hl ((yukawa_ode hd hl).1 η hη),
    mul_pos (by linarith [deriv_yukawa_neg hd hl hη]) (pow_pos hη _)⟩

theorem parts_of_integrable (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) {g : Euc d → ℝ}
    (hg : Integrable g (smearEuc d l η)) :
    Integrable g (ballPart d η) ∧ Integrable g (spherePart d η) ∧
    ∫ y, g y ∂(smearEuc d l η) = (l * yukawa d l η) * ∫ y, g y ∂(ballPart d η) +
      (-(deriv (yukawa d l) η) * η ^ (d - 1)) * ∫ y, g y ∂(spherePart d η) := by
  obtain ⟨ha, hb⟩ := coef_pos hd hl hη
  have h : Integrable g (ENNReal.ofReal (l * yukawa d l η) • ballPart d η +
      ENNReal.ofReal (-(deriv (yukawa d l) η) * η ^ (d - 1)) • spherePart d η) := hg
  obtain ⟨h1, h2⟩ := integrable_add_measure.1 h
  have hc1 : ENNReal.ofReal (l * yukawa d l η) ≠ 0 := (ENNReal.ofReal_pos.2 ha).ne'
  have hc2 : ENNReal.ofReal (-(deriv (yukawa d l) η) * η ^ (d - 1)) ≠ 0 := (ENNReal.ofReal_pos.2 hb).ne'
  refine ⟨(integrable_smul_measure hc1 ENNReal.ofReal_ne_top).1 h1,
    (integrable_smul_measure hc2 ENNReal.ofReal_ne_top).1 h2, ?_⟩
  show ∫ y, g y ∂(ENNReal.ofReal (l * yukawa d l η) • ballPart d η +
      ENNReal.ofReal (-(deriv (yukawa d l) η) * η ^ (d - 1)) • spherePart d η) = _
  rw [integral_add_measure h1 h2, integral_smul_measure, integral_smul_measure,
    ENNReal.toReal_ofReal ha.le, ENNReal.toReal_ofReal hb.le]
  simp only [smul_eq_mul]

theorem ballPart_singleton (hd : 1 ≤ d) (η : ℝ) (z : Euc d) : ballPart d η {z} = 0 := by
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  rw [Measure.restrict_apply (measurableSet_singleton z)]
  exact measure_mono_null Set.inter_subset_left (measure_singleton z)

theorem ballPart_compl (d : ℕ) (η : ℝ) : ballPart d η (Metric.closedBall (0 : Euc d) η)ᶜ = 0 := by
  rw [Measure.restrict_apply Metric.isClosed_closedBall.measurableSet.compl]; simp

theorem spherePart_compl (d : ℕ) {η : ℝ} (hη : 0 < η) :
    spherePart d η (Metric.closedBall (0 : Euc d) η)ᶜ = 0 := by
  have hB : MeasurableSet (Metric.closedBall (0 : Euc d) η) := Metric.isClosed_closedBall.measurableSet
  rw [Measure.map_apply (show Measurable (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) from
      (continuous_sphScale d η).measurable) hB.compl]
  have : (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) ⁻¹' (Metric.closedBall 0 η)ᶜ = ∅ := by
    ext ω
    simp only [mem_preimage, mem_compl_iff, Metric.mem_closedBall, dist_zero_right, norm_smul,
      Real.norm_eq_abs, mem_empty_iff_false, iff_false, not_not]
    have : ‖(ω : Euc d)‖ = 1 := by simp
    rw [this, mul_one, abs_of_pos hη]
  rw [this]; simp

theorem spherePart_singleton (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (z : Euc d) : spherePart d η {z} = 0 := by
  have hm : Measurable (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) :=
    (continuous_sphScale d η).measurable
  have : Nontrivial (Euc d) := Module.nontrivial_of_finrank_pos (R := ℝ) (by simp; omega)
  rw [Measure.map_apply hm (measurableSet_singleton z)]
  by_cases h : ∃ ω₀ : Metric.sphere (0 : Euc d) 1, η • (ω₀ : Euc d) = z
  · obtain ⟨ω₀, hω₀⟩ := h
    refine measure_mono_null ?_ (toSphere_singleton hd ω₀)
    intro ω hω
    have : η • (ω : Euc d) = η • (ω₀ : Euc d) := by rw [hω₀]; exact hω
    have := smul_right_injective (Euc d) hη.ne' this
    exact Subtype.ext this
  · push Not at h
    have : (fun ω : Metric.sphere (0 : Euc d) 1 => η • (ω : Euc d)) ⁻¹' {z} = ∅ := by
      ext ω; simp only [mem_preimage, mem_singleton_iff, mem_empty_iff_false, iff_false]; exact h ω
    rw [this]; simp

theorem good_ae (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) (x : Torus d) :
    (∀ᵐ y ∂(ballPart d η), x - Torus.mk y ≠ 0) ∧ (∀ᵐ y ∂(spherePart d η), x - Torus.mk y ≠ 0) := by
  set x' : Euc d := KernelGrad.centeredRep x with hx'
  have hmk : Torus.mk x' = x := KernelGrad.mk_centeredRep x
  have hbox : ∀ i, |x' i| ≤ 1 / 2 := KernelGrad.abs_centeredRep_le x
  have hsub : {y : Euc d | x - Torus.mk y = 0} ⊆ {x'} ∪ (Metric.closedBall (0 : Euc d) η)ᶜ := by
    intro y hy
    by_cases hyb : y ∈ Metric.closedBall (0 : Euc d) η
    · left
      have h0 : Torus.mk (x' - y) = 0 := by rw [mk_sub_eq, hmk]; exact hy
      exact eq_of_mk_sub_eq_zero hη2 hbox (by simpa using hyb) h0
    · right; exact hyb
  constructor
  · rw [ae_iff]
    exact measure_mono_null (fun y hy => hsub (by simpa using hy))
      (measure_union_null (ballPart_singleton (by omega) η _) (ballPart_compl d η))
  · rw [ae_iff]
    exact measure_mono_null (fun y hy => hsub (by simpa using hy))
      (measure_union_null (spherePart_singleton hd hη _) (spherePart_compl d hη))


theorem smearT_real_eq (d : ℕ) (l η : ℝ) : (smearT d l η).real Set.univ = (smearEuc d l η).real Set.univ := by
  unfold smearT
  rw [measureReal_def, measureReal_def, Measure.map_apply Torus.continuous_mk.measurable MeasurableSet.univ]
  rfl

theorem identity_l (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) (x : Torus d)
    (hx : x ≠ 0) :
    Integrable (fun y => sliceG d l (x - Torus.mk y)) (smearEuc d l η) ∧
    ∫ y, sliceG d l (x - Torus.mk y) ∂(smearEuc d l η) =
      sliceG d l x - fTrunc d l η x + ∫ z, fTrunc d l η z := by
  obtain ⟨hI, heq⟩ := sliceGfull_conv_smear_all hd hl hη hη2 x hx
  haveI := isFiniteMeasure_smearEuc d l η
  have hF : Measurable (fun w : Torus d => sliceGfull d l (x - w)) :=
    (measurable_sliceGfull l).comp (measurable_const.sub measurable_id)
  have step1 : ∫ y, sliceGfull d l (x - y) ∂(smearT d l η) =
      ∫ y, sliceGfull d l (x - Torus.mk y) ∂(smearEuc d l η) :=
    integral_map Torus.continuous_mk.measurable.aemeasurable hF.aestronglyMeasurable
  rw [step1] at heq
  have e : (fun y : Euc d => sliceG d l (x - Torus.mk y)) =
      fun y => sliceGfull d l (x - Torus.mk y) - 1 / l := by
    funext y; simp [sliceGfull]
  have hg : Integrable (fun y : Euc d => sliceG d l (x - Torus.mk y)) (smearEuc d l η) := by
    rw [e]; exact hI.sub (integrable_const _)
  refine ⟨hg, ?_⟩
  rw [e, integral_sub hI (integrable_const _), heq, integral_const, smul_eq_mul]
  have hm := smearT_real_univ hd hl hη hη2
  rw [smearT_real_eq] at hm
  rw [hm]
  have : sliceGfull d l x = sliceG d l x + 1 / l := rfl
  rw [this]
  field_simp
  ring


theorem kappa_mul (hd : 1 ≤ d) : (volume : Measure (Euc d)).toSphere.real univ * kappa d = 1 := by
  have := sphere_mass_mul_flux (d := d) hd
  unfold kappa; exact this

theorem aint_ge (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) :
    l * yukawa d l η * (η ^ d / d) ≤ Aint d l η := by
  have hyk := yukawa_ode hd hl
  unfold Aint
  have h4 : ∫ r in Set.Ioc (0 : ℝ) η, yukawa d l η * r ^ (d - 1) = yukawa d l η * (η ^ d / d) := by
    rw [integral_const_mul]
    congr 1
    rw [← intervalIntegral.integral_of_le hη.le, integral_pow]
    have : d - 1 + 1 = d := by omega
    rw [this]
    simp [zero_pow (by omega : d ≠ 0), Nat.cast_sub hd]
  have hint2 : IntegrableOn (fun r : ℝ => yukawa d l η * r ^ (d - 1)) (Set.Ioc 0 η) :=
    (continuous_const.mul (continuous_pow _)).integrableOn_Ioc
  have h1 : ∫ r in Set.Ioc (0 : ℝ) η, yukawa d l η * r ^ (d - 1) ≤
      ∫ r in Set.Ioc (0 : ℝ) η, r ^ (d - 1) * yukawa d l r := by
    refine setIntegral_mono_on hint2 (int_flux hd hl hη).1 measurableSet_Ioc fun r hr => ?_
    rw [mul_comm]
    refine mul_le_mul_of_nonneg_left ?_ (pow_nonneg hr.1.le _)
    rcases eq_or_lt_of_le hr.2 with h | h
    · rw [h]
    · exact (hyk.2.1 r η hr.1 h).le
  rw [h4] at h1
  rw [mul_assoc]
  exact mul_le_mul_of_nonneg_left h1 hl.le

theorem tendsto_a (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun l : ℝ => l * yukawa d l η) (𝓝[>] 0) (𝓝 0) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hc : (0:ℝ) < η ^ d / d := by positivity
  have h := (Aint_tendsto hd hη).div_const (η ^ d / d)
  rw [zero_div] at h
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with l hl
    exact (mul_pos hl ((yukawa_ode hd hl).1 η hη)).le
  · filter_upwards [self_mem_nhdsWithin] with l hl
    have := aint_ge hd (show (0:ℝ) < l from hl) hη
    rw [le_div_iff₀ hc]; exact this

theorem tendsto_b (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) :
    Tendsto (fun l : ℝ => -(deriv (yukawa d l) η) * η ^ (d - 1)) (𝓝[>] 0) (𝓝 (kappa d)) := by
  have h := (tendsto_const_nhds (x := kappa d)).sub (Aint_tendsto hd hη)
  rw [sub_zero] at h
  refine h.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with l hl
  have := qq_eq hd (show (0:ℝ) < l from hl) hη
  linarith

theorem int_fTrunc_eq (hd : 1 ≤ d) {l η : ℝ} (hl : 0 < l) (hη : 0 < η) (hη2 : η < 1 / 2) :
    ∫ z : Torus d, fTrunc d l η z = (volume : Measure (Euc d)).toSphere.real univ *
      ∫ r in Set.Ioc (0 : ℝ) η, r ^ (d - 1) * (yukawa d l r - yukawa d l η) := by
  rw [integral_fTrunc hd hl hη hη2]
  congr 1
  have h4 : ∫ r in Set.Ioc (0 : ℝ) η, yukawa d l η * r ^ (d - 1) = yukawa d l η * (η ^ d / d) := by
    rw [integral_const_mul]
    congr 1
    rw [← intervalIntegral.integral_of_le hη.le, integral_pow]
    have : d - 1 + 1 = d := by omega
    rw [this]
    simp [zero_pow (by omega : d ≠ 0), Nat.cast_sub hd]
  have hint2 : IntegrableOn (fun r : ℝ => yukawa d l η * r ^ (d - 1)) (Set.Ioc 0 η) :=
    (continuous_const.mul (continuous_pow _)).integrableOn_Ioc
  have h3 : ∫ r in Set.Ioc (0 : ℝ) η, r ^ (d - 1) * (yukawa d l r - yukawa d l η) =
      ∫ r in Set.Ioc (0 : ℝ) η, (r ^ (d - 1) * yukawa d l r - yukawa d l η * r ^ (d - 1)) := by
    refine setIntegral_congr_fun measurableSet_Ioc fun r _ => ?_
    ring
  rw [h3, integral_sub (int_flux hd hl hη).1 hint2, h4]

theorem tendsto_int_fTrunc (hd : 1 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) :
    Tendsto (fun l : ℝ => ∫ z : Torus d, fTrunc d l η z) (𝓝[>] 0) (𝓝 (η ^ 2 / (2 * d))) := by
  have hdr : (0:ℝ) < d := by exact_mod_cast hd
  have hS := kappa_mul hd
  set S := (volume : Measure (Euc d)).toSphere.real univ with hSdef
  have hS0 : 0 ≤ S := measureReal_nonneg
  have hlow : Tendsto (fun l : ℝ => (1 - S * Aint d l η) * (η ^ 2 / (2 * d))) (𝓝[>] 0)
      (𝓝 ((1 - S * 0) * (η ^ 2 / (2 * d)))) :=
    (((Aint_tendsto hd hη).const_mul S).const_sub 1).mul_const _
  rw [mul_zero, sub_zero, one_mul] at hlow
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' hlow tendsto_const_nhds ?_ ?_
  · filter_upwards [self_mem_nhdsWithin] with l hl
    have hl' : (0:ℝ) < l := hl
    rw [int_fTrunc_eq hd hl' hη hη2]
    have := (int_f_bounds hd hl' hη).1
    have h2 := mul_le_mul_of_nonneg_left this hS0
    calc (1 - S * Aint d l η) * (η ^ 2 / (2 * d)) = S * ((kappa d - Aint d l η) * (η ^ 2 / (2 * d))) := by
          rw [← hS]; ring
      _ ≤ _ := h2
  · filter_upwards [self_mem_nhdsWithin] with l hl
    have hl' : (0:ℝ) < l := hl
    rw [int_fTrunc_eq hd hl' hη hη2]
    have := (int_f_bounds hd hl' hη).2
    have h2 := mul_le_mul_of_nonneg_left this hS0
    calc _ ≤ S * (kappa d * (η ^ 2 / (2 * d))) := h2
      _ = η ^ 2 / (2 * d) := by rw [← mul_assoc, hS, one_mul]


theorem newton_anti (hd : 2 ≤ d) {a b : ℝ} (ha : 0 < a) (hab : a ≤ b) : newton d b ≤ newton d a := by
  have hd1 : 1 ≤ d := by omega
  have hderiv : ∀ r ∈ Ioi (0:ℝ), HasDerivAt (newton d) (-(kappa d) / r ^ (d - 1)) r :=
    fun r hr => hasDerivAt_newton hd hr
  have := antitoneOn_of_deriv_nonpos (f := newton d) (convex_Ioi (0:ℝ))
    (fun r hr => (hderiv r hr).continuousAt.continuousWithinAt)
    (by rw [interior_Ioi]; exact fun r hr => (hderiv r hr).differentiableAt.differentiableWithinAt)
    (by
      rw [interior_Ioi]
      intro r hr
      rw [(hderiv r hr).deriv]
      have := kappa_pos d hd1
      have : 0 < r ^ (d - 1) := pow_pos hr _
      exact div_nonpos_of_nonpos_of_nonneg (by linarith) this.le)
  exact this ha (lt_of_lt_of_le ha hab) hab

theorem tendsto_fTrunc_x (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) (x : Torus d) (hx : x ≠ 0) :
    Tendsto (fun l : ℝ => fTrunc d l η x) (𝓝[>] 0) (𝓝 (fTrunc0 d η x)) := by
  have hd1 : 1 ≤ d := by omega
  set r : ℝ := ‖KernelGrad.centeredRep x‖ with hr
  have hr0 : 0 < r := by
    refine norm_pos_iff.2 fun h => hx ?_
    rw [← KernelGrad.mk_centeredRep x, h]
    exact mk_zero'
  have e0 : ∀ l : ℝ, fTrunc d l η x = max (yukawa d l r - yukawa d l η) 0 := fun l => rfl
  have e1 : fTrunc0 d η x = max (newton d r - newton d η) 0 := rfl
  by_cases hrη : r ≤ η
  · set δ : ℝ → ℝ := fun l => (newton d r - newton d η) - (yukawa d l r - yukawa d l η) with hδ
    have hnn : 0 ≤ newton d r - newton d η := by
      have := (f_sandwich hd (l := 1) one_pos hr0 hrη).1
      have h2 := (yukawa_ode hd1 (one_pos : (0:ℝ) < 1)).2.1
      rcases eq_or_lt_of_le hrη with h | h
      · rw [h]; simp
      · have := h2 r η hr0 h
        linarith
    have hδ0 : Tendsto δ (𝓝[>] 0) (𝓝 0) := by
      have h := (Aint_tendsto hd1 hη).mul_const (∫ s in r..η, 1 / s ^ (d - 1))
      rw [zero_mul] at h
      refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds h ?_ ?_
      · filter_upwards [self_mem_nhdsWithin] with l hl
        exact (f_sandwich hd (show (0:ℝ) < l from hl) hr0 hrη).1
      · filter_upwards [self_mem_nhdsWithin] with l hl
        exact (f_sandwich hd (show (0:ℝ) < l from hl) hr0 hrη).2
    have h := (tendsto_const_nhds (x := newton d r - newton d η)).sub hδ0
    rw [sub_zero] at h
    rw [e1, max_eq_left hnn]
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with l hl
    have hl' : (0:ℝ) < l := hl
    rw [e0, max_eq_left]
    · simp only [hδ]; ring
    · rcases eq_or_lt_of_le hrη with h | h
      · rw [h]; simp
      · have := (yukawa_ode hd1 hl').2.1 r η hr0 h
        linarith
  · push Not at hrη
    have h0 : fTrunc0 d η x = 0 := by
      rw [e1, max_eq_right]
      have := newton_anti hd hη hrη.le
      linarith
    rw [h0]
    refine tendsto_const_nhds.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with l hl
    have := (fTrunc_support hd1 (show (0:ℝ) < l from hl) hη hη2).2.1 x hrη.le
    exact this.symm


theorem main_limit (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) (x : Torus d) (hx : x ≠ 0) :
    Tendsto (fun l : ℝ => ∫ y, sliceG d l (x - Torus.mk y) ∂(smearEuc d l η)) (𝓝[>] 0)
      (𝓝 (kappa d * ∫ y, sliceG d 0 (x - Torus.mk y) ∂(spherePart d η))) := by
  have hd1 : 1 ≤ d := by omega
  haveI : IsFiniteMeasure (ballPart d η) := ⟨by rw [Measure.restrict_apply_univ]; exact measure_closedBall_lt_top⟩
  haveI : IsFiniteMeasure (spherePart d η) := inferInstance
  obtain ⟨hI1, -⟩ := sliceGfull_conv_smear_all hd1 (l := 1) one_pos hη hη2 x hx
  obtain ⟨hB1, hS1, -⟩ := parts_of_integrable hd1 one_pos hη hI1
  set D : Euc d → ℝ := fun y => Real.exp 1 * sliceGfull d 1 (x - Torus.mk y) + 1 + Kc d with hD
  have hDB : Integrable D (ballPart d η) := ((hB1.const_mul _).add (integrable_const _)).add (integrable_const _)
  have hDS : Integrable D (spherePart d η) := ((hS1.const_mul _).add (integrable_const _)).add (integrable_const _)
  obtain ⟨gB, gS⟩ := good_ae hd hη hη2 x
  -- ball part
  have hball : Tendsto (fun l : ℝ => (l * yukawa d l η) * ∫ y, sliceG d l (x - Torus.mk y) ∂(ballPart d η))
      (𝓝[>] 0) (𝓝 0) := by
    have h := (tendsto_a hd1 hη).mul_const (∫ y, D y ∂(ballPart d η))
    rw [zero_mul] at h
    refine squeeze_zero_norm' ?_ h
    filter_upwards [self_mem_nhdsWithin] with l hl
    have hl' : (0:ℝ) < l := hl
    have ha := (coef_pos hd1 hl' hη).1
    rw [norm_mul, Real.norm_eq_abs, abs_of_pos ha]
    refine mul_le_mul_of_nonneg_left ?_ ha.le
    refine norm_integral_le_of_norm_le hDB ?_
    filter_upwards [gB] with y hy
    rw [Real.norm_eq_abs]
    exact sliceG_abs_le hy hl'.le
  -- sphere part
  have hsph : Tendsto (fun l : ℝ => ∫ y, sliceG d l (x - Torus.mk y) ∂(spherePart d η)) (𝓝[>] 0)
      (𝓝 (∫ y, sliceG d 0 (x - Torus.mk y) ∂(spherePart d η))) := by
    refine tendsto_integral_filter_of_dominated_convergence D ?_ ?_ hDS ?_
    · filter_upwards [self_mem_nhdsWithin] with l hl
      have hl' : (0:ℝ) < l := hl
      exact (parts_of_integrable hd1 hl' hη (identity_l hd1 hl' hη hη2 x hx).1).2.1.aestronglyMeasurable
    · filter_upwards [self_mem_nhdsWithin] with l hl
      have hl' : (0:ℝ) < l := hl
      filter_upwards [gS] with y hy
      rw [Real.norm_eq_abs]
      exact sliceG_abs_le hy hl'.le
    · filter_upwards [gS] with y hy
      exact sliceG_tendsto hy
  have hcomb := hball.add ((tendsto_b hd1 hη).mul hsph)
  rw [zero_add] at hcomb
  refine hcomb.congr' ?_
  filter_upwards [self_mem_nhdsWithin] with l hl
  have hl' : (0:ℝ) < l := hl
  exact (parts_of_integrable hd1 hl' hη (identity_l hd1 hl' hη hη2 x hx).1).2.2.symm



end SmearAux

/-- **S2.4 (Coulomb slice, Newton up to the constant `η²/(2d)`).**  For `d ≥ 2`, `0 < η < 1/2`, `x ≠ 0`:
`∫ 𝒢_0(x - y) d(sphere_η)(y) = 𝒢_0(x) - f_{0,η}(x) + η²/(2d)`, where `𝒢_0 = sliceG d 0` is the periodic
Green function of `-Δ` (`Δ 𝒢_0 = 1` off the origin, `𝒢_0 = Γ_0(|x|) + smooth`; the mean value
formula for functions with `Δ w ≡ const` is exact). -/
theorem sliceG0_conv_sphere (hd : 2 ≤ d) {η : ℝ} (hη : 0 < η) (hη2 : η < 1 / 2) (x : Torus d)
    (hx : x ≠ 0) :
    ∫ y, sliceG d 0 (x - y) ∂(sphereT d η) =
      sliceG d 0 x - fTrunc0 d η x + η ^ 2 / (2 * d) := by
  have hd1 : 1 ≤ d := by omega
  -- left side as `κ ∫ ... ∂spherePart`
  have hL : ∫ y, sliceG d 0 (x - y) ∂(sphereT d η) =
      SmearAux.kappa d * ∫ y, sliceG d 0 (x - Torus.mk y) ∂(SmearAux.spherePart d η) := by
    unfold sphereT
    have hF : Measurable (fun w : Torus d => sliceG d 0 (x - w)) :=
      (SmearAux.measurable_sliceG 0).comp (measurable_const.sub measurable_id)
    rw [integral_map Torus.continuous_mk.measurable.aemeasurable hF.aestronglyMeasurable,
      integral_smul_measure, ENNReal.toReal_inv, smul_eq_mul]
    congr 1
    have h1 := SmearAux.kappa_mul hd1
    have h2 : (volume : Measure (Euc d)).toSphere.real univ = ((volume : Measure (Euc d)).toSphere univ).toReal := rfl
    rw [← h2]
    exact inv_eq_of_mul_eq_one_right h1
  rw [hL]
  have hR : Tendsto (fun l : ℝ => ∫ y, sliceG d l (x - Torus.mk y) ∂(smearEuc d l η)) (𝓝[>] 0)
      (𝓝 (sliceG d 0 x - fTrunc0 d η x + η ^ 2 / (2 * d))) := by
    have h := ((SmearAux.sliceG_tendsto hx).sub (SmearAux.tendsto_fTrunc_x hd hη hη2 x hx)).add (SmearAux.tendsto_int_fTrunc hd1 hη hη2)
    refine h.congr' ?_
    filter_upwards [self_mem_nhdsWithin] with l hl
    exact (SmearAux.identity_l hd1 (show (0:ℝ) < l from hl) hη hη2 x hx).2.symm
  exact tendsto_nhds_unique (SmearAux.main_limit hd hη hη2 x hx) hR


end HRS.Commutator
