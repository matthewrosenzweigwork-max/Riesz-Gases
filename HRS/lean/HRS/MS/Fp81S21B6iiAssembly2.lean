import HRS.MS.Fp81S21B6iiAssembly
import HRS.MS.Fp81S21B6iiNoise

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Set Filter
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- Physical drift of the compact-test empirical equation. -/
def fp81s21_b6ii_physicalDrift (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (N : ℕ) (A : Particle R N) (f : Euc p.d → ℝ) (v : ℝ) (ω : A.Ω) : ℝ :=
  fp81s21_particleEmpField R N A v ω (generatorW (r26t3_coeff R) v f) -
    (Real.sqrt (N : ℝ))⁻¹ * fp81s21_particleQuadRawField R N A v ω f

/-- The Hilbert-valued drift assembled from the strong empirical representative. -/
def fp81s21_b6ii_vectorDrift (N : ℕ) {Ω : Type*}
    (L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (qs qB0 : ℝ → Ω → r26t6_Coeff) (v : ℝ) (ω : Ω) : r26t6_Coeff :=
  L v (qs v ω) - (Real.sqrt (N : ℝ))⁻¹ • qB0 v ω

/-- Conditional simultaneous-time assembly of the raw empirical equation. -/
theorem fp81s21_b6ii_vector_assembly
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ) (N : ℕ)
    (A : Particle R N) (Fp : FilteredParticle A)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (qs qB0 m : ℝ → A.Ω → r26t6_Coeff)
    (L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (hcommon : ∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ,
      IsR2Test f → fp81s21_chartAction E
        (fp81s21_gaussian_chartEmbed p Es E (qs u ω)) f =
          fp81s21_particleEmpField R N A u ω f)
    (hIto : IsHilbertItoIntegral A.P Fp.ℱ Fp.Wc
      (fp81s21_b6i_gradientNoise p E A Fp) m)
    (hZ : ∀ T, IsHSIntegrand A.P Fp.ℱ T (fp81s21_b6i_gradientNoise p E A Fp))
    (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (hU2 : ∀ f : Euc p.d → ℝ, IsR2Test f →
      ∀ᵐ ω ∂A.P,
        IntegrableOn (fun v => fp81s21_b6ii_physicalDrift p R N A f v ω) (Icc 0 (a + H)) ∧
        ∀ u ∈ Icc 0 (a + H),
          fp81s21_particleEmpField R N A u ω f =
            fp81s21_particleEmpField R N A 0 ω f +
            (∫ v in Icc 0 u, fp81s21_b6ii_physicalDrift p R N A f v ω) +
            fp81s21_b6ii_scalarNoise p E A Fp f u ω -
            fp81s21_b6ii_scalarNoise p E A Fp f 0 ω)
    (hU5a : Integrable (fun z : ℝ × A.Ω =>
      fp81s21_b6ii_vectorDrift N L qs qB0 (a + z.1) z.2)
      ((volume.restrict (Icc 0 H)).prod A.P))
    (hU5b : ∀ j : ℕ, (fun z : ℝ × A.Ω =>
      fp81s21_b6ii_physicalDrift p R N A (E.test j) (a + z.1) z.2)
      =ᵐ[(volume.restrict (Icc 0 H)).prod A.P]
      (fun z => fp81s21_chartAction E
        (fp81s21_b6ii_vectorDrift N L qs qB0 (a + z.1) z.2) (E.test j))) :
    ∀ᵐ ω ∂A.P,
      IntegrableOn (fun v => fp81s21_b6ii_vectorDrift N L qs qB0 (a + v) ω) (Icc 0 H) ∧
      ∀ s t : Icc (0 : ℝ) H, s ≤ t →
        fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω) -
          fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω) =
        (∫ v in Icc (s : ℝ) (t : ℝ), fp81s21_b6ii_vectorDrift N L qs qB0 (a + v) ω) +
          m (a + t) ω - m (a + s) ω := by
  have hcoord (z : r26t6_Coeff) (j : ℕ) :
      fp81s21_chartAction E z (E.test j) = z j := by
    have he : E.encode (E.test j) = (lp.single 2 j (1 : ℝ) : r26t6_Coeff) := by
      ext i
      change E.encode (E.test j) i = _
      rw [E.test_coord]
      simp [lp.single_apply, Pi.single_apply, eq_comm]
    rw [fp81s21_chartAction, he]
    simp [lp.inner_single_right]
  have hu2 : ∀ᵐ ω ∂A.P, ∀ j : ℕ,
      IntegrableOn (fun v => fp81s21_b6ii_physicalDrift p R N A (E.test j) v ω) (Icc 0 (a + H)) ∧
      ∀ u ∈ Icc 0 (a + H),
        fp81s21_particleEmpField R N A u ω (E.test j) =
          fp81s21_particleEmpField R N A 0 ω (E.test j) +
          (∫ v in Icc 0 u, fp81s21_b6ii_physicalDrift p R N A (E.test j) v ω) +
          fp81s21_b6ii_scalarNoise p E A Fp (E.test j) u ω -
          fp81s21_b6ii_scalarNoise p E A Fp (E.test j) 0 ω :=
    ae_all_iff.mpr (fun j => hU2 (E.test j) (E.test_smooth j))
  have hsections : ∀ᵐ ω ∂A.P, ∀ j : ℕ,
      (fun v => fp81s21_b6ii_physicalDrift p R N A (E.test j) (a + v) ω)
        =ᵐ[volume.restrict (Icc 0 H)]
      (fun v => fp81s21_chartAction E
        (fp81s21_b6ii_vectorDrift N L qs qB0 (a + v) ω) (E.test j)) := by
    apply ae_all_iff.mpr
    intro j
    have hswap := (Measure.measurePreserving_swap (μ := A.P)
      (ν := volume.restrict (Icc 0 H))).quasiMeasurePreserving.ae (hU5b j)
    exact Measure.ae_ae_of_ae_prod hswap
  filter_upwards [hU5a.prod_left_ae, hsections, hu2, hcommon,
    fp81s21_b6ii_noise_coordinates p E A Fp hIto hZ] with ω hD hsec hphys hemp hnoise
  refine ⟨hD, ?_⟩
  intro s t hst
  have hs : (s : ℝ) ≤ t := hst
  have hsub : Icc (s : ℝ) (t : ℝ) ⊆ Icc 0 H := Icc_subset_Icc s.property.1 t.property.2
  have hDi : IntegrableOn (fun v => fp81s21_b6ii_vectorDrift N L qs qB0 (a + v) ω) (Icc 0 H) := hD
  have hD' := hDi.mono_set hsub
  apply lp.ext (funext fun j => ?_)
  have hpair := (lp.evalCLM ℝ (fun _ : ℕ => ℝ) (2 : ℝ≥0∞) j).integral_comp_comm hD'
  change (∫ v in Icc (s : ℝ) (t : ℝ),
      fp81s21_b6ii_vectorDrift N L qs qB0 (a + v) ω j) =
    (∫ v in Icc (s : ℝ) (t : ℝ), fp81s21_b6ii_vectorDrift N L qs qB0 (a + v) ω) j at hpair
  have heq : (∫ v in Icc (s : ℝ) (t : ℝ),
      fp81s21_b6ii_physicalDrift p R N A (E.test j) (a + v) ω) =
      (∫ v in Icc (s : ℝ) (t : ℝ),
      fp81s21_b6ii_vectorDrift N L qs qB0 (a + v) ω j) := by
    apply integral_congr_ae
    filter_upwards [ae_restrict_of_ae_restrict_of_subset hsub (hsec j)] with v hv
    exact hv.trans (hcoord _ j)
  have hshift := fp81s21_b6ii_shifted_primitive
    (fun v => fp81s21_b6ii_physicalDrift p R N A (E.test j) v ω)
    ha s.property.1 hs t.property.2 (hphys j).1
  have ht0 : 0 ≤ a + (t : ℝ) := add_nonneg ha t.property.1
  have hs0 : 0 ≤ a + (s : ℝ) := add_nonneg ha s.property.1
  have htt : a + (t : ℝ) ∈ Icc 0 (a + H) := ⟨ht0, by linarith [t.property.2]⟩
  have hss : a + (s : ℝ) ∈ Icc 0 (a + H) := ⟨hs0, by linarith [s.property.2]⟩
  have hpT := (hphys j).2 _ htt
  have hpS := (hphys j).2 _ hss
  have heT := hemp _ ht0 (E.test j) (E.test_smooth j)
  have heS := hemp _ hs0 (E.test j) (E.test_smooth j)
  have hnT := hnoise j _ ht0
  have hnS := hnoise j _ hs0
  rw [hcoord] at heT heS hnT hnS
  change (fp81s21_gaussian_chartEmbed p Es E (qs (a + t) ω)) j -
      (fp81s21_gaussian_chartEmbed p Es E (qs (a + s) ω)) j =
    (∫ v in Icc (s : ℝ) (t : ℝ), fp81s21_b6ii_vectorDrift N L qs qB0 (a + v) ω) j +
      m (a + t) ω j - m (a + s) ω j
  rw [← hpair, ← heq, ← hshift]
  linarith

#print axioms fp81s21_b6ii_vector_assembly
end HRS.Fp81.S21
end
