import HRS.MS.S11Q3A9
import HRS.MS.S113X2C4
import HRS.MS.S113EndAux23
import HRS.MS.MovSchAux8

/-!
# S11.3 / S11.4 (worker S11Q3), B1: ingredients of the producer

* `s11q3_rho_jet`: the clamped family `ρ_{max t 0}` is a `s11q3_Jet2`.
* `s11q3_F0c_contDiff`: the cut-off pair energy `θ · F0 ∘ J` is globally `C²`.
* `s11q3_movQ_eq`: `q_N^t(X) = K̂(t)⁻¹ W_t(X)` for a probability density `ρ_t`.
-/

set_option linter.unusedSectionVars false
set_option linter.style.longLine false

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.S11Q3

open HRS HRS.Whole HRS.MS.MovForce HRS.MS.S113BD
open HRS.MC.CepP3 (Jc)
open HRS.MS.S113X2 HRS.MS.S113X2B HRS.MS.S113X2C

variable {d N : ℕ} {s : ℝ}

section Rho

variable {ρ D : ℝ → Euc d → ℝ} {c B : ℝ}

theorem s11q3_rho_jet (R : s11q3_Reg d ρ D c B) :
    s11q3_Jet2 (fun t x => ρ (max t 0) x) (fun t x => fderiv ℝ (ρ (max t 0)) x)
      (fun t x => fderiv ℝ (fderiv ℝ (ρ (max t 0))) x) where
  c0 := R.j0.comp_continuous s11q3_clamp_cont s11q3_clamp_mem
  c1 := R.j1.comp_continuous s11q3_clamp_cont s11q3_clamp_mem
  c2 := R.j2.comp_continuous s11q3_clamp_cont s11q3_clamp_mem
  h1 t z := (((R.cd _ (le_max_right t 0)).differentiable (by norm_num)) z).hasFDerivAt
  h2 t z := ((((R.cd _ (le_max_right t 0)).fderiv_right (m := 1) (by norm_num)).differentiable
    (by norm_num)) z).hasFDerivAt

end Rho

theorem s11q3_F0_contDiffOn : ContDiffOn ℝ ∞ (s11q3_F0 d s N) (eucCollisionSet d N)ᶜ := by
  unfold s11q3_F0
  refine ContDiffOn.mul contDiffOn_const (ContDiffOn.sum fun i _ => ContDiffOn.sum fun j hj => ?_)
  have hij : i ≠ j := fun h => (Finset.mem_erase.1 hj).1 h.symm
  refine (rieszKernel_contDiffOn (d := d) (s := s)).comp (f := fun x : EucConfig d N => x i - x j) ?_ ?_
  · exact ((contDiff_apply ℝ (Euc d) i).sub (contDiff_apply ℝ (Euc d) j)).contDiffOn
  · intro x hx h
    exact hx ⟨i, j, hij, sub_eq_zero.1 h⟩

theorem s11q3_F0c_contDiff {θ : s113b_E (N * d) → ℝ} (hθ : ContDiff ℝ ∞ θ)
    (hθs : tsupport θ ⊆ {z | Jc d N z ∉ eucCollisionSet d N}) :
    ContDiff ℝ 2 (fun z => θ z * s11q3_F0 d s N (Jc d N z)) := by
  rw [contDiff_iff_contDiffAt]
  intro z
  by_cases hz : z ∈ tsupport θ
  · have hfree : Jc d N z ∈ (eucCollisionSet d N)ᶜ := hθs hz
    have hopen : IsOpen {w : s113b_E (N * d) | Jc d N w ∈ (eucCollisionSet d N)ᶜ} :=
      (s113a_isOpen_free d N).preimage (Jc d N).continuous
    have hb : ContDiffOn ℝ ∞ (fun w => s11q3_F0 d s N (Jc d N w)) {w | Jc d N w ∈ (eucCollisionSet d N)ᶜ} :=
      (s11q3_F0_contDiffOn (d := d) (s := s) (N := N)).comp (Jc d N).contDiff.contDiffOn (fun w hw => hw)
    exact ((hθ.contDiffAt).mul ((hb.contDiffAt (hopen.mem_nhds hfree)))).of_le (by simp)
  · have hev : θ =ᶠ[𝓝 z] fun _ => 0 := (notMem_tsupport_iff_eventuallyEq).1 hz
    have : (fun w => θ w * s11q3_F0 d s N (Jc d N w)) =ᶠ[𝓝 z] fun _ => (0 : ℝ) := by
      filter_upwards [hev] with w hw
      simp [hw]
    exact (contDiffAt_const).congr_of_eventuallyEq this

section MovQ

variable {ρ D : ℝ → Euc d → ℝ} {c B : ℝ}

theorem s11q3_gibbsNormalizer_eq (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : s11q3_Reg d ρ D c B) {β : ℝ}
    (hN : 1 ≤ N) {t : ℝ} (ht : 0 ≤ t) (hprob : HRS.Whole.IsProbDensity (ρ t)) :
    HRS.Whole.gibbsNormalizer (rieszKernel d s) N β (HRS.Whole.withDensityReal (ρ t)) =
      Real.exp (-(β * N * ((1 / 2) * ∫ x, ρ t x * ∫ z, rieszKernel d s z * ρ t (x - z)))) *
        s11q3_Khat d s β N ρ t := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN' : (N : ℝ) ≠ 0 := by linarith
  unfold HRS.Whole.gibbsNormalizer
  rw [HRS.MS.Canon.cn_pi_withDensityReal (ρ t) hprob.nonneg (HRS.MS.Canon.cn_integrable_of_prob (ρ t) hprob)]
  have hm : Measurable (fun X : EucConfig d N => ENNReal.ofReal (∏ i, ρ t (X i))) :=
    Measurable.ennreal_ofReal (Finset.measurable_prod _ fun i _ => hprob.measurable.comp (measurable_pi_apply i))
  rw [integral_withDensity_eq_integral_toReal_smul₀ hm.aemeasurable
    (Filter.Eventually.of_forall fun X => ENNReal.ofReal_lt_top)]
  unfold s11q3_Khat
  rw [← integral_const_mul]
  refine integral_congr_ae (Filter.Eventually.of_forall fun X => ?_)
  have hFm := s113x_Fm_eq (N := N) hprob.measurable hprob.nonneg s X
  have hmod : HRS.Whole.modulatedEnergy (rieszKernel d s) X (HRS.Whole.withDensityReal (ρ t)) =
      HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (ρ t)) := rfl
  beta_reduce
  rw [hmod, hFm]
  simp only [smul_eq_mul, s11q3_W, s11q3_E, s11q3_P, s11q3_Gam, s11q3_F0]
  rw [ENNReal.toReal_ofReal (Finset.prod_nonneg fun i _ => hprob.nonneg _)]
  have : -β * N * ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (X i - X j) -
        (1 / (N : ℝ)) * (∑ a, ∫ z, rieszKernel d s z * ρ t (X a - z)) +
        (1 / 2) * ∫ x, ρ t x * ∫ z, rieszKernel d s z * ρ t (x - z)) =
      (-β * N * ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (X i - X j)) +
        β * (∑ a, ∫ z, rieszKernel d s z * ρ t (X a - z))) +
        (-(β * N * ((1 / 2) * ∫ x, ρ t x * ∫ z, rieszKernel d s z * ρ t (x - z)))) := by
    field_simp
    ring
  rw [this, Real.exp_add]
  ring

theorem s11q3_movQ_eq (hd : 1 ≤ d) (hs0 : 0 ≤ s) (hsd : s < d) (R : s11q3_Reg d ρ D c B) {β : ℝ}
    (hN : 1 ≤ N) {t : ℝ} (ht : 0 ≤ t) (hprob : HRS.Whole.IsProbDensity (ρ t)) (X : EucConfig d N) :
    movQDensity d s β N (ρ t) X = (s11q3_Khat d s β N ρ t)⁻¹ * s11q3_W d s β N ρ t X := by
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hN' : (N : ℝ) ≠ 0 := by linarith
  have hK := s11q3_gibbsNormalizer_eq hd hs0 hsd R (β := β) hN ht hprob
  unfold movQDensity
  rw [hK]
  have hFm := s113x_Fm_eq (N := N) hprob.measurable hprob.nonneg s X
  have hmod : HRS.Whole.rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (ρ t)) =
      (1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (X i - X j) -
        (1 / (N : ℝ)) * ∑ a, (∫ z, rieszKernel d s z * ρ t (X a - z)) +
        (1 / 2) * ∫ x, ρ t x * ∫ z, rieszKernel d s z * ρ t (x - z) := hFm
  rw [hmod]
  simp only [s11q3_W, s11q3_E, s11q3_P, s11q3_Gam, s11q3_F0]
  have : -β * N * ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (X i - X j) -
        (1 / (N : ℝ)) * (∑ a, ∫ z, rieszKernel d s z * ρ t (X a - z)) +
        (1 / 2) * ∫ x, ρ t x * ∫ z, rieszKernel d s z * ρ t (x - z)) =
      (-β * N * ((1 / (2 * (N : ℝ) ^ 2)) * ∑ i, ∑ j ∈ Finset.univ.erase i, rieszKernel d s (X i - X j)) +
        β * (∑ a, ∫ z, rieszKernel d s z * ρ t (X a - z))) +
        (-(β * N * ((1 / 2) * ∫ x, ρ t x * ∫ z, rieszKernel d s z * ρ t (x - z)))) := by
    field_simp
    ring
  rw [this, Real.exp_add, mul_inv, mul_comm (Real.exp _)⁻¹ _]
  have h1 : Real.exp (-(β * N * ((1 / 2) * ∫ x, ρ t x * ∫ z, rieszKernel d s z * ρ t (x - z)))) ≠ 0 :=
    (Real.exp_pos _).ne'
  field_simp

end MovQ

end HRS.MS.S11Q3

end
