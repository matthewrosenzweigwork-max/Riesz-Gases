import HRS.MS.Fp81S21TimeRep14
import HRS.MS.Fp81S21VersionTime

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6

/-- Compact-test observations of the moving reference measure vary continuously. -/
theorem fp81s21_particle_reference_pair_continuous
    (p : Parameters) {δ H : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2) (hH : 0 ≤ H)
    (f : Euc p.d → ℝ) (hf : IsR2Test f) :
    ContinuousOn (fun u => HRS.Whole.pair (r26t3_mu R u) f) (Icc 0 H) := by
  have hc := fp81s21_particle_density_clip_continuous p R hδ hδh
  have hi : ContinuousOn (fun u : ℝ => ∫ x : Euc p.d,
      f x * R.ρ ((max u 0).toNNReal) x) (Icc 0 H) := by
    refine continuousOn_integral_of_compact_support (f := fun (u : ℝ) (x : Euc p.d) =>
      f x * R.ρ ((max u 0).toNNReal) x) hf.2.isCompact ?_ ?_
    · exact ((hf.1.continuous.comp continuous_snd).mul hc).continuousOn
    · intro u hu x hx
      rw [image_eq_zero_of_notMem_tsupport hx, zero_mul]
  apply hi.congr
  intro u hu
  dsimp only
  have hρ := (R.resulting.global H).density u hu
  rw [show r26t3_mu R u = HRS.Whole.withDensityReal (R.ρ u) by rfl,
    HRS.Whole.Q09A.pair_withDensityReal hρ]
  congr 1
  funext x
  simp [max_eq_left hu.1, Real.coe_toNNReal _ hu.1, mul_comm]

/-- Every compact-test empirical observation has an almost surely continuous path. -/
theorem fp81s21_particle_observation_continuous
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (N : ℕ) (hN : 2 ≤ N) (A : Particle R N)
    (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H) :
    ∀ᵐ ω ∂A.P, ∀ f : Euc p.d → ℝ, IsR2Test f →
      Continuous (fun t : Icc (0 : ℝ) H =>
        fp81s21_particleEmpField R N A (a + t) ω f) := by
  have hpath : ∀ᵐ ω ∂A.P, ∀ k : Fin N,
      Continuous (fun t : ℝ≥0 => A.X t ω k) := (A.strong (a + H)).cont
  filter_upwards [hpath] with ω hω
  intro f hf
  have href := fp81s21_particle_reference_pair_continuous p R hδ hδh
    (show 0 ≤ a + H by linarith) f hf
  have hshift : Continuous (fun t : Icc (0 : ℝ) H => a + (t : ℝ)) :=
    continuous_const.add continuous_subtype_val
  have href' : Continuous (fun t : Icc (0 : ℝ) H =>
      HRS.Whole.pair (r26t3_mu R (a + t)) f) := by
    exact href.comp_continuous hshift (fun t =>
      ⟨add_nonneg ha t.property.1, by linarith [t.property.2]⟩)
  have hsum : Continuous (fun t : Icc (0 : ℝ) H =>
      (N : ℝ)⁻¹ * ∑ k : Fin N, f (A.X (a + (t : ℝ)).toNNReal ω k)) := by
    refine continuous_const.mul (continuous_finsetSum _ fun k _ => ?_)
    exact hf.1.continuous.comp ((hω k).comp (continuous_real_toNNReal.comp hshift))
  have hN0 : 0 < N := by omega
  have heq : (fun t : Icc (0 : ℝ) H =>
      fp81s21_particleEmpField R N A (a + t) ω f) =
      fun (t : Icc (0 : ℝ) H) => Real.sqrt N * ((N : ℝ)⁻¹ *
        (∑ k : Fin N, f (A.X (a + (t : ℝ)).toNNReal ω k)) -
        HRS.Whole.pair (r26t3_mu R (a + t)) f) := by
    funext t
    simp [fp81s21_particleEmpField, r2EmpDistr, HRS.Whole.pair_empirical hN0]
  rw [heq]
  exact continuous_const.mul (hsum.sub href')

/-- Fixed-time chart agreement transfers to a simultaneous physical identity. -/
theorem fp81s21_particle_simultaneous_identity
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2))
    (N : ℕ) (hN : 2 ≤ N) (A : Particle R N)
    (a H : ℝ) (ha : 0 ≤ a) (hH : 0 < H)
    (M : ℝ) (q : ℝ → A.Ω → r26t6_Coeff)
    (hrep : fp81s21_MomentRep E A.P (fp81s21_particleEmpField R N A) q M)
    (X : A.Ω → fp81s21_SmoothCH H)
    (hsec : ∀ t : Icc (0 : ℝ) H, (fun ω => X ω t) =ᵐ[A.P] q (a + t)) :
    ∀ᵐ ω ∂A.P, ∀ t : Icc (0 : ℝ) H, ∀ f, IsR2Test f →
      fp81s21_chartAction E (X ω t) f =
        fp81s21_particleEmpField R N A (a + t) ω f := by
  letI : Nonempty (Icc (0 : ℝ) H) := ⟨⟨0, le_rfl, hH.le⟩⟩
  let s : ℕ → Icc (0 : ℝ) H := TopologicalSpace.denseSeq _
  have hs : DenseRange s := TopologicalSpace.denseRange_denseSeq _
  have hdense : ∀ᵐ ω ∂A.P, ∀ n, ∀ f, IsR2Test f →
      fp81s21_chartAction E (X ω (s n)) f =
        fp81s21_particleEmpField R N A (a + s n) ω f := by
    apply ae_all_iff.mpr
    intro n
    have hu : 0 ≤ a + (s n : ℝ) := add_nonneg ha (s n).property.1
    filter_upwards [hsec (s n), (hrep.2 _ hu).2.2] with ω hx hω
    intro f hf
    rw [hx]
    exact hω.1 f hf
  filter_upwards [hdense, fp81s21_particle_observation_continuous p R hδ hδh N hN A a H ha hH] with ω hω hc
  intro t f hf
  have hchart : Continuous (fun x : Icc (0 : ℝ) H =>
      fp81s21_chartAction E (X ω x) f) := by
    change Continuous (fun x => inner ℝ (X ω x) (E.encode f))
    exact (continuous_id.inner continuous_const).comp (X ω).continuous
  have hseq : (fun x : Icc (0 : ℝ) H => fp81s21_chartAction E (X ω x) f) ∘ s =
      (fun x : Icc (0 : ℝ) H => fp81s21_particleEmpField R N A (a + x) ω f) ∘ s := by
    funext n
    exact hω n f hf
  exact congrFun (DenseRange.equalizer hs hchart (hc f hf) hseq) t

#print axioms HRS.Fp81.S21.fp81s21_particle_reference_pair_continuous
#print axioms HRS.Fp81.S21.fp81s21_particle_observation_continuous
#print axioms HRS.Fp81.S21.fp81s21_particle_simultaneous_identity

end HRS.Fp81.S21
