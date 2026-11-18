import HRS.MC.CepE7A3

/-!
# Packet CEPE7, file A4: the lift equation along a chamber path, measurability of `X`, small helpers
-/

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.CepE7

open HRS HRS.MC.Cepa HRS.MC.CepK1

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem cepE7_lip_neg {E : Type*} [NormedAddCommGroup E] {K : ℝ≥0} {f : E → E} (hf : LipschitzWith K f) :
    LipschitzWith K (fun x => -f x) :=
  LipschitzWith.of_dist_le_mul fun x y => by
    rw [dist_neg_neg]
    exact hf.dist_le_mul x y

theorem cepE7_hal {zl : ℝ → Ch N} {T : ℝ}
    (h : volume {s : ℝ | s ∈ Icc 0 T ∧ zl s ∉ cep_Alcove N} = 0) :
    ∀ᵐ s ∂(volume.restrict (Icc 0 T)), zl s ∈ cep_Alcove N := by
  rw [ae_restrict_iff' measurableSet_Icc, ae_iff]
  convert h using 2
  ext s
  simp [and_assoc]

theorem cepE7_lift_path {D : DynData 1} {a : ℝ} {Ψ : Ch N → ℝ} (h : cepE7_E1drift D a N Ψ)
    (hΨc : Continuous (gradient Ψ)) {zl : ℝ → Ch N} (hzc : Continuous zl)
    (π : Equiv.Perm (Fin N)) (c : Ch N) (nz : ℝ → Ch N) (σ' : ℝ)
    (heq : ∀ t, 0 ≤ t → zl t = c +
      (∫ s in (0 : ℝ)..t, (-(gradient (cep_chamberPot a N) (zl s)) + -(gradient Ψ (zl s)))) + σ' • nz t)
    (hint : ∀ T : ℝ, IntegrableOn (fun s => ‖gradient (cep_chamberPot a N) (zl s)‖) (Icc 0 T))
    (hnull : ∀ T : ℝ, volume {s : ℝ | s ∈ Icc 0 T ∧ zl s ∉ cep_Alcove N} = 0)
    {t : ℝ} (ht : 0 ≤ t) (i : Fin N) :
    IntegrableOn (fun s => particleDrift D (fun j => Torus.mk (cep_unrank π (zl s) j)) i) (Icc 0 t) ∧
    cep_unrank π (zl t) i = cep_unrank π (zl 0) i +
      (∫ s in Icc 0 t, particleDrift D (fun j => Torus.mk (cep_unrank π (zl s) j)) i) +
      σ' • cepk1_ι (nz t (π.symm i) - nz 0 (π.symm i)) := by
  obtain ⟨hI, hEq⟩ := cepE7_drift_integral h hΨc hzc ht (hint t) (cepE7_hal (hnull t)) π i
  refine ⟨hI, ?_⟩
  rw [hEq]
  have e1 := congrArg (fun v : Ch N => v (π.symm i)) (heq t ht)
  have e0 := congrArg (fun v : Ch N => v (π.symm i)) (heq 0 le_rfl)
  simp only [intervalIntegral.integral_same, add_zero, WithLp.ofLp_add, Pi.add_apply,
    WithLp.ofLp_smul, Pi.smul_apply, smul_eq_mul, WithLp.ofLp_zero, Pi.zero_apply] at e1 e0
  ext c0
  have hc : c0 = 0 := Subsingleton.elim _ _
  subst hc
  simp only [cepE7_unrank_apply, cepk1_ι, WithLp.ofLp_add, Pi.add_apply, WithLp.ofLp_smul,
    Pi.smul_apply, smul_eq_mul, WithLp.ofLp_toLp]
  linarith

/-- The configuration `ω ↦ mk ∘ unrank_{π ω}(zt ω)` is measurable when `π`, `zt` are. -/
theorem cepE7_X_measurable {m : MeasurableSpace Ω} {π : Ω → Equiv.Perm (Fin N)}
    (hπ : ∀ σ, MeasurableSet[m] {ω | π ω = σ}) {zt : Ω → Ch N} (hz : Measurable[m] zt) :
    Measurable[m] (fun ω => fun i => Torus.mk (cep_unrank (π ω) (zt ω) i)) := by
  refine cepE7_glue (m := m) π (fun σ ω => fun i => Torus.mk (cep_unrank σ (zt ω) i)) (fun σ => ?_) hπ
  refine measurable_pi_iff.2 fun i => ?_
  have h1 : Measurable[m] (fun ω => zt ω (σ.symm i)) :=
    (EuclideanSpace.proj (σ.symm i)).continuous.measurable.comp hz
  have h2 : Measurable[m] (fun ω => cep_unrank σ (zt ω) i) :=
    cepk1_contDiff_ι.continuous.measurable.comp h1
  exact Torus.continuous_mk.measurable.comp h2

theorem cepE7_X_continuous (π : Equiv.Perm (Fin N)) {zl : ℝ → Ch N} (hzc : Continuous zl) :
    Continuous fun t : ℝ≥0 => (fun i => Torus.mk (cep_unrank π (zl (t : ℝ)) i) : Config 1 N) := by
  refine continuous_pi fun i => Torus.continuous_mk.comp ?_
  exact cepk1_contDiff_ι.continuous.comp
    ((EuclideanSpace.proj (π.symm i)).continuous.comp (hzc.comp NNReal.continuous_coe))

end HRS.MC.CepE7
