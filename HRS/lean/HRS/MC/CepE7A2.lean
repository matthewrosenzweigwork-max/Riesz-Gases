import HRS.MC.CepE7A1
import HRS.MC.CepE6Aux1

/-!
# Packet CEPE7, file A2: pathwise identification of the particle drift and of the pair forces

For a continuous chamber path `zl` that lies in the open alcove for almost every time, with `‖∇Φ(zl)‖` integrable:
* the particle drift of the lift `cep_unrank π (zl s)` is the `π⁻¹ i`-th coordinate of `-∇Φ(zl s) - ∇Ψ(zl s)` (E1),
  and its time integral is the corresponding coordinate of the chamber integral appearing in E6;
* each pair force `periodicRieszGrad 1 0 (x_i - x_j)` is locally integrable (K1 and `cep_pair_cot_le`).
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepE7

open HRS HRS.MC.Cepa HRS.MC.CepK1

variable {N : ℕ}

/-- The identification of the drift on strictly ordered lifts (conclusion of E1). -/
def cepE7_E1drift (D : DynData 1) (a : ℝ) (N : ℕ) (Ψ : Ch N → ℝ) : Prop :=
  ∀ (π : Equiv.Perm (Fin N)) (y : Fin N → Euc 1), cep_StrictlyOrdered π y → ∀ k : Fin N,
    liftedDrift D y (π k) 0 =
      -(gradient (cep_chamberPot a N) (cep_toCh π y)) k - (gradient Ψ (cep_toCh π y)) k

/-- `u ↦ u • e₀` as a continuous linear map `ℝ → Euc 1`. -/
def cepE7_ιL : ℝ →L[ℝ] Euc 1 :=
  ContinuousLinearMap.toSpanSingleton ℝ (EuclideanSpace.single (0 : Fin 1) (1 : ℝ))

theorem cepE7_ιL_apply (u : ℝ) : cepE7_ιL u = cepk1_ι u := by
  ext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  simp [cepE7_ιL, cepk1_ι]

theorem cepE7_gradient_measurable (f : Ch N → ℝ) : Measurable (gradient f) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Ch N)).symm.continuous.measurable.comp (measurable_fderiv ℝ f)

theorem cepE7_drift_pt {D : DynData 1} {a : ℝ} {Ψ : Ch N → ℝ} (h : cepE7_E1drift D a N Ψ)
    {z : Ch N} (hz : z ∈ cep_Alcove N) (π : Equiv.Perm (Fin N)) (i : Fin N) :
    particleDrift D (fun j => Torus.mk (cep_unrank π z j)) i =
      cepk1_ι (-(gradient (cep_chamberPot a N) z) (π.symm i) - (gradient Ψ z) (π.symm i)) := by
  have := h π (cep_unrank π z) (cepE7_unrank_strict hz π) (π.symm i)
  rw [cepE7_toCh_unrank, Equiv.apply_symm_apply] at this
  ext j
  have hj : j = 0 := Subsingleton.elim _ _
  subst hj
  exact this

theorem cepE7_drift_integral {D : DynData 1} {a : ℝ} {Ψ : Ch N → ℝ} (h : cepE7_E1drift D a N Ψ)
    (hΨc : Continuous (gradient Ψ)) {zl : ℝ → Ch N} (hzc : Continuous zl) {t : ℝ} (ht : 0 ≤ t)
    (hint : IntegrableOn (fun s => ‖gradient (cep_chamberPot a N) (zl s)‖) (Icc 0 t))
    (hal : ∀ᵐ s ∂(volume.restrict (Icc 0 t)), zl s ∈ cep_Alcove N)
    (π : Equiv.Perm (Fin N)) (i : Fin N) :
    IntegrableOn (fun s => particleDrift D (fun j => Torus.mk (cep_unrank π (zl s) j)) i) (Icc 0 t) ∧
    ∫ s in Icc 0 t, particleDrift D (fun j => Torus.mk (cep_unrank π (zl s) j)) i =
      cepk1_ι ((∫ s in (0 : ℝ)..t, (-(gradient (cep_chamberPot a N) (zl s)) + -(gradient Ψ (zl s))))
        (π.symm i)) := by
  have hΦm : Measurable fun s => gradient (cep_chamberPot a N) (zl s) :=
    (cepE7_gradient_measurable _).comp hzc.measurable
  have hΦi : IntegrableOn (fun s => gradient (cep_chamberPot a N) (zl s)) (Icc 0 t) :=
    (integrable_norm_iff hΦm.aestronglyMeasurable).1 hint
  have hΨi : IntegrableOn (fun s => gradient Ψ (zl s)) (Icc 0 t) :=
    (hΨc.comp hzc).integrableOn_Icc
  have hv : IntegrableOn (fun s => -(gradient (cep_chamberPot a N) (zl s)) + -(gradient Ψ (zl s)))
      (Icc 0 t) := hΦi.neg.add hΨi.neg
  set L : Ch N →L[ℝ] Euc 1 := cepE7_ιL.comp (EuclideanSpace.proj (π.symm i)) with hL
  have hae : (fun s => particleDrift D (fun j => Torus.mk (cep_unrank π (zl s) j)) i) =ᵐ[volume.restrict (Icc 0 t)]
      fun s => L (-(gradient (cep_chamberPot a N) (zl s)) + -(gradient Ψ (zl s))) := by
    filter_upwards [hal] with s hs
    rw [cepE7_drift_pt h hs π i]
    simp only [hL, ContinuousLinearMap.comp_apply, cepE7_ιL_apply]
    congr 1
  refine ⟨(L.integrable_comp hv).congr hae.symm, ?_⟩
  rw [integral_congr_ae hae, L.integral_comp_comm hv]
  have : ∫ s in (0 : ℝ)..t, (-(gradient (cep_chamberPot a N) (zl s)) + -(gradient Ψ (zl s))) =
      ∫ s in Icc 0 t, (-(gradient (cep_chamberPot a N) (zl s)) + -(gradient Ψ (zl s))) := by
    rw [intervalIntegral.integral_of_le ht, ← integral_Icc_eq_integral_Ioc]
  rw [this]
  simp only [hL, ContinuousLinearMap.comp_apply, cepE7_ιL_apply]
  rfl

/-- The pair force of the lift of an alcove point, in terms of the chamber coordinates. -/
theorem cepE7_pair_force {D : DynData 1} (hs : D.s = 0) {z : Ch N} (hz : z ∈ cep_Alcove N)
    (π : Equiv.Perm (Fin N)) {i j : Fin N} (hij : i ≠ j) :
    periodicRieszGrad 1 D.s (Torus.mk (cep_unrank π z i) - Torus.mk (cep_unrank π z j)) =
      cepk1_ι (-(Real.pi * (Real.cos (Real.pi * (z (π.symm i) - z (π.symm j))) /
        Real.sin (Real.pi * (z (π.symm i) - z (π.symm j))))) +
          cepk1_ρ (z (π.symm i) - z (π.symm j))) := by
  have hkl : π.symm i ≠ π.symm j := fun h' => hij (π.symm.injective h')
  have h := HRS.MC.CepE1.cepe1_force (cepE7_unrank_strict hz π) hkl
  simp only [Equiv.apply_symm_apply] at h
  have e : ∀ m : Fin N, cep_unrank π z m 0 = z (π.symm m) := fun m => rfl
  rw [e, e] at h
  rw [hs, HRS.MC.CepE1.cepe1_sub_mk]
  ext c
  have hc : c = 0 := Subsingleton.elim _ _
  subst hc
  exact h

theorem cepE7_pair_integrable {D : DynData 1} (hs : D.s = 0) {a : ℝ} (ha : 0 < a) {zl : ℝ → Ch N}
    (hzc : Continuous zl) {t : ℝ}
    (hint : IntegrableOn (fun s => ‖gradient (cep_chamberPot a N) (zl s)‖) (Icc 0 t))
    (hal : ∀ᵐ s ∂(volume.restrict (Icc 0 t)), zl s ∈ cep_Alcove N)
    (π : Equiv.Perm (Fin N)) {i j : Fin N} (hij : i ≠ j) :
    IntegrableOn (fun s => periodicRieszGrad 1 D.s
      (Torus.mk (cep_unrank π (zl s) i) - Torus.mk (cep_unrank π (zl s) j))) (Icc 0 t) := by
  have hkl : π.symm i ≠ π.symm j := fun h' => hij (π.symm.injective h')
  set k := π.symm i with hk
  set l := π.symm j with hl
  set d : ℝ → ℝ := fun s => zl s k - zl s l with hd
  have hdc : Continuous d := ((EuclideanSpace.proj k).continuous.comp hzc).sub
    ((EuclideanSpace.proj l).continuous.comp hzc)
  set g : ℝ → Euc 1 := fun s => cepk1_ι (-(Real.pi * (Real.cos (Real.pi * d s) / Real.sin (Real.pi * d s))) +
    cepk1_ρ (d s)) with hg
  have hgm : Measurable g := by
    refine cepk1_contDiff_ι.continuous.measurable.comp ?_
    refine Measurable.add (Measurable.neg (measurable_const.mul ?_)) ?_
    · exact (Real.continuous_cos.comp (continuous_const.mul hdc)).measurable.div
        (Real.continuous_sin.comp (continuous_const.mul hdc)).measurable
    · exact (cepk1_ρ_contDiff.continuous.comp hdc).measurable
  obtain ⟨C, hC0, hC⟩ := HRS.MC.CepE6.cep_pair_cot_le ha N
  obtain ⟨R, hR⟩ := (isCompact_Icc (a := (0 : ℝ)) (b := t)).exists_bound_of_continuousOn
    (f := fun s => cepk1_ρ (d s)) (cepk1_ρ_contDiff.continuous.comp hdc).continuousOn
  have hΦm : Measurable fun s => gradient (cep_chamberPot a N) (zl s) :=
    (cepE7_gradient_measurable _).comp hzc.measurable
  set bnd : ℝ → ℝ := fun s => C * ((N : ℝ) * ‖gradient (cep_chamberPot a N) (zl s)‖ + 1) + R with hbnd
  have hbi : IntegrableOn bnd (Icc 0 t) := by
    have h1 : IntegrableOn (fun s => (N : ℝ) * ‖gradient (cep_chamberPot a N) (zl s)‖) (Icc 0 t) :=
      hint.const_mul _
    have h2 : IntegrableOn (fun s => (N : ℝ) * ‖gradient (cep_chamberPot a N) (zl s)‖ + 1) (Icc 0 t) :=
      h1.add (integrableOn_const (by simp))
    exact (h2.const_mul C).add (integrableOn_const (by simp))
  have hgi : IntegrableOn g (Icc 0 t) := by
    refine Integrable.mono' hbi hgm.aestronglyMeasurable ?_
    rw [ae_restrict_iff' measurableSet_Icc] at hal ⊢
    filter_upwards [hal] with s hsa hsI
    have hz := hsa hsI
    rw [hg]
    simp only [cepk1_norm_ι]
    have hcot : |Real.pi * (Real.cos (Real.pi * d s) / Real.sin (Real.pi * d s))| ≤
        C * (∑ m, |(gradient (cep_chamberPot a N) (zl s)) m| + 1) := by
      rcases lt_or_gt_of_ne hkl with hlt | hgt
      · have h2 := (hC (zl s) hz).2 k l hlt
        have e : Real.pi * (Real.cos (Real.pi * d s) / Real.sin (Real.pi * d s)) =
            -(Real.pi * (Real.cos (Real.pi * (zl s l - zl s k)) /
              Real.sin (Real.pi * (zl s l - zl s k)))) := by
          have : Real.pi * d s = -(Real.pi * (zl s l - zl s k)) := by simp only [hd]; ring
          rw [this, Real.cos_neg, Real.sin_neg, div_neg, mul_neg]
        rw [e, abs_neg]
        exact h2
      · exact (hC (zl s) hz).2 l k hgt
    have hsum : ∑ m, |(gradient (cep_chamberPot a N) (zl s)) m| ≤
        (N : ℝ) * ‖gradient (cep_chamberPot a N) (zl s)‖ := by
      calc ∑ m, |(gradient (cep_chamberPot a N) (zl s)) m|
          ≤ ∑ _m : Fin N, ‖gradient (cep_chamberPot a N) (zl s)‖ :=
            Finset.sum_le_sum fun m _ => by
              simpa using PiLp.norm_apply_le (gradient (cep_chamberPot a N) (zl s)) m
        _ = (N : ℝ) * ‖gradient (cep_chamberPot a N) (zl s)‖ := by simp
    have hρ : |cepk1_ρ (d s)| ≤ R := by
      have := hR s hsI
      simpa using this
    calc |-(Real.pi * (Real.cos (Real.pi * d s) / Real.sin (Real.pi * d s))) + cepk1_ρ (d s)|
        ≤ |-(Real.pi * (Real.cos (Real.pi * d s) / Real.sin (Real.pi * d s)))| + |cepk1_ρ (d s)| :=
          abs_add_le _ _
      _ = |Real.pi * (Real.cos (Real.pi * d s) / Real.sin (Real.pi * d s))| + |cepk1_ρ (d s)| := by
          rw [abs_neg]
      _ ≤ bnd s := by
          rw [hbnd]
          have := mul_le_mul_of_nonneg_left (add_le_add_right hsum 1) hC0
          linarith
  have hae : (fun s => periodicRieszGrad 1 D.s
      (Torus.mk (cep_unrank π (zl s) i) - Torus.mk (cep_unrank π (zl s) j))) =ᵐ[volume.restrict (Icc 0 t)] g := by
    filter_upwards [hal] with s hsa
    exact cepE7_pair_force hs hsa π hij
  exact hgi.congr hae.symm

end HRS.MC.CepE7
