import HRS.Commutator.Torus.TENAux3

/-!
# Torus energy layer (packet T-EN), helper part 4: the energy identity on `𝕋^d`

Prefix `ten_`.  `f_η^𝕋` is integrable (`f = R - g` a.e., with `R = periodicRiesz` integrable and `g = g_η^𝕋`
continuous); the identity `(2.energyidentity)` on the torus follows from `ten_kerEnergy_charge` by splitting
`g = R - f` off the diagonal.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

/-- `{z}` is `volume`-null on the torus of positive dimension. -/
theorem ten_volume_singleton {d : ℕ} (hd : 0 < d) (z : Torus d) :
    (volume : Measure (Torus d)) {z} = 0 := by
  have h0 : (volume : Measure (Torus d)) {0} = 0 := by
    have := HRS.KernelAux.torus_ae_ne hd
    rw [ae_iff] at this
    simpa using this
  have hset : ({z} : Set (Torus d)) = (fun y => y + -z) ⁻¹' {0} := by
    ext y
    simp [sub_eq_add_neg]
  rw [hset, measure_preimage_add_right]
  exact h0

/-- For a fixed point, almost every `y` differs from it. -/
theorem ten_ae_ne {d : ℕ} (hd : 0 < d) (z : Torus d) :
    ∀ᵐ y ∂(volume : Measure (Torus d)), y ≠ z := by
  rw [ae_iff]
  simpa using ten_volume_singleton hd z

/-- `(x,y) ↦ h(x-y) ρ(x) ρ(y)` is integrable for integrable `h` and bounded measurable `ρ`. -/
theorem ten_joint_integrable {h : Torus d → ℝ} (hh : Integrable h) {ρ : Torus d → ℝ}
    (hρ : BddDensityT ρ) : Integrable (fun p : Torus d × Torus d => h (p.1 - p.2) * ρ p.1 * ρ p.2) := by
  obtain ⟨B, hB⟩ := hρ.bdd
  have hρint : Integrable ρ :=
    ten_integrable_of_bdd (μ := volume) hρ.measurable B (fun x => by
      rw [Real.norm_eq_abs]; exact hB x)
  have hconv := MeasureTheory.Integrable.convolution_integrand (ContinuousLinearMap.mul ℝ ℝ) hρint hh
  have hb := hconv.bdd_mul (c := B) ((hρ.measurable.comp measurable_fst).aestronglyMeasurable)
    (ae_of_all _ fun p => by simpa [Real.norm_eq_abs] using hB p.1)
  refine hb.congr (ae_of_all _ fun p => ?_)
  simp only [ContinuousLinearMap.mul_apply', Function.comp_apply]
  ring

/-- `y ↦ h(z - y) ρ(y)` is integrable. -/
theorem ten_sec_integrable {h : Torus d → ℝ} (hh : Integrable h) {ρ : Torus d → ℝ}
    (hρ : BddDensityT ρ) (z : Torus d) : Integrable (fun y => h (z - y) * ρ y) := by
  obtain ⟨B, hB⟩ := hρ.bdd
  have hb := (hh.comp_sub_left z).bdd_mul (c := B) hρ.measurable.aestronglyMeasurable
    (ae_of_all _ fun y => by simpa [Real.norm_eq_abs] using hB y)
  exact hb.congr (ae_of_all _ fun y => mul_comm _ _)

/-- `f_η^𝕋` is integrable, since `f = R - g` off the origin with `R` integrable and `g` continuous. -/
theorem ten_fTorus_integrable {d : ℕ} {s η : ℝ} (hR : Integrable (periodicRiesz d s))
    (hG : Continuous (gTorus (d := d) s η)) (hd : 0 < d) : Integrable (fTorus (d := d) s η) := by
  obtain ⟨C, hC⟩ := ten_bound_of_continuous hG
  have hGi : Integrable (gTorus (d := d) s η) := ten_integrable_of_bdd (μ := volume) hG.measurable C hC
  have hae : fTorus (d := d) s η =ᵐ[volume] (fun x => periodicRiesz d s x - gTorus (d := d) s η x) := by
    filter_upwards [HRS.KernelAux.torus_ae_ne hd] with x hx
    simp only [gTorus, fTorus, if_neg hx]
    ring
  exact (hR.sub hGi).congr hae.symm


/-- The energy identity for a kernel `G = R - f` off the origin (`R` and `f` integrable, `G` continuous and
even), with the diagonal value `G(0) = g0`: the abstract form of `(2.energyidentity)` on the torus. -/
theorem ten_identity_abstract {d : ℕ} (hd : 0 < d) {G R f : Torus d → ℝ} {g0 : ℝ}
    (hG : Continuous G) (hGe : ∀ z, G (-z) = G z) (hR : Integrable R) (hf : Integrable f)
    (hGoff : ∀ x : Torus d, x ≠ 0 → G x = R x - f x) (hG0 : G 0 = g0)
    {N : ℕ} (hN : 1 ≤ N) (X : Config d N) (hX : X ∉ collisionSet d N) (ρ : Torus d → ℝ)
    (hρ : BddDensityT ρ) :
    kerEnergyT G (chargeT X ρ) +
        (1 / (N : ℝ) ^ 2) * ∑ i, ∑ j ∈ Finset.univ.erase i, f (X i - X j) +
        ∫ x, ∫ y, f (x - y) * ρ x * ρ y =
      2 * ((1 / 2) * pairT (fun x y => R (x - y)) X ρ) + g0 / (N : ℝ) +
        (2 / (N : ℝ)) * ∑ i, ∫ y, f (X i - y) * ρ y := by
  have hne : ∀ i j : Fin N, i ≠ j → X i ≠ X j := fun i j hij h => hX ⟨i, j, hij, h⟩
  have hN0 : (N : ℝ) ≠ 0 := by
    have : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
    exact this.ne'
  rw [ten_kerEnergy_charge G hG hGe ρ hρ hN X]
  -- the diagonal of the particle sum
  have hdiag : ∀ i : Fin N, ∑ j, G (X i - X j) = g0 + ∑ j ∈ Finset.univ.erase i, G (X i - X j) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), sub_self, hG0]
  have hsumG : ∑ i, ∑ j, G (X i - X j) = (N : ℝ) * g0 + ∑ i, ∑ j ∈ Finset.univ.erase i, G (X i - X j) := by
    simp only [hdiag, Finset.sum_add_distrib]
    simp
  -- off-diagonal splitting
  have hoff : ∀ i : Fin N, ∑ j ∈ Finset.univ.erase i, G (X i - X j) =
      ∑ j ∈ Finset.univ.erase i, R (X i - X j) - ∑ j ∈ Finset.univ.erase i, f (X i - X j) := by
    intro i
    rw [← Finset.sum_sub_distrib]
    refine Finset.sum_congr rfl fun j hj => hGoff _ (sub_ne_zero.2 (hne i j ?_))
    exact (Finset.ne_of_mem_erase hj).symm
  -- one-variable integrals (the diagonal `y = X i` is null)
  have hyG : ∀ i : Fin N, ∫ y, G (X i - y) * ρ y =
      (∫ y, R (X i - y) * ρ y) - ∫ y, f (X i - y) * ρ y := by
    intro i
    rw [← integral_sub (ten_sec_integrable hR hρ (X i)) (ten_sec_integrable hf hρ (X i))]
    refine integral_congr_ae ?_
    filter_upwards [ten_ae_ne hd (X i)] with y hy
    rw [hGoff _ (sub_ne_zero.2 (Ne.symm hy))]
    ring
  -- the two-variable integral
  have hGdouble : ∫ x, ∫ y, G (x - y) * ρ x * ρ y =
      (∫ x, ∫ y, R (x - y) * ρ x * ρ y) - ∫ x, ∫ y, f (x - y) * ρ x * ρ y := by
    have inner : ∀ x : Torus d, ∫ y, G (x - y) * ρ x * ρ y =
        (∫ y, R (x - y) * ρ x * ρ y) - ∫ y, f (x - y) * ρ x * ρ y := by
      intro x
      have hiR : Integrable (fun y => R (x - y) * ρ x * ρ y) :=
        ((ten_sec_integrable hR hρ x).const_mul (ρ x)).congr (ae_of_all _ fun y => by ring)
      have hif : Integrable (fun y => f (x - y) * ρ x * ρ y) :=
        ((ten_sec_integrable hf hρ x).const_mul (ρ x)).congr (ae_of_all _ fun y => by ring)
      rw [← integral_sub hiR hif]
      refine integral_congr_ae ?_
      filter_upwards [ten_ae_ne hd x] with y hy
      rw [hGoff _ (sub_ne_zero.2 (Ne.symm hy))]
      ring
    rw [integral_congr_ae (ae_of_all _ inner), integral_sub
      (ten_joint_integrable hR hρ).integral_prod_left (ten_joint_integrable hf hρ).integral_prod_left]
  -- the right-hand side, unfolded
  simp only [pairT]
  simp only [hsumG, hoff, hyG, hGdouble, Finset.sum_sub_distrib]
  field_simp
  ring

end HRS.Commutator.TorusNote
