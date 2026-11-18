import HRS.MS.Fp81S21JointDBridge
import HRS.MS.Fp81S21JointN3

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter
open scoped BigOperators
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- At fixed rank and horizon the diagonal constant is uniform in particle
count, realization, starting time and the supplied physical time classes. -/
theorem fp81s21_jointN_sqerr_physical_fixed_rank
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
    ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
    ∀ εN εG εB : ℕ → ℝ, ∀ S : fp81s21_Physical31 p R Es E εN εG εB,
    ∀ m : ℕ, 0 ≤ εN m → ∀ Λ : ℝ,
    ∀ θ : Fin m → HRS.MS.R2S11.s11V p.d Λ,
    ∀ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
    ∀ k : ℕ, ∀ H : ℝ, ∀ hH : 0 < H,
    ∃ Ddiag : ℝ, 0 ≤ Ddiag ∧
    ∀ N : ℕ, ∀ hN : 2 ≤ N, ∀ A : Particle R N,
    ∀ a : ℝ, 0 ≤ a → ∀ Uη UB : A.Ω → fp81s21_jointP_U H,
    fp81s21_TimeL2Rep A.P
      (fun u ω => fp81s21_particle_embedField p Es E (S.qsηN N hN A u ω)) S.MN a H Uη →
    fp81s21_TimeL2Rep A.P
      (fun u ω => fp81s21_particle_embedField p Es E (S.qsBN N hN A u ω)) S.MN a H UB →
    ∀ τ : ℝ, 0 ≤ τ → ∀ Ur : A.Ω → fp81s21_jointP_U H,
    fp81s21_ParticleRankTime31 p R m Λ θ D k N A a H Ur →
    fp81s21_SqErr A.P Ur (fun ω => fp81s21_timeProject H m (UB ω))
      (Real.sqrt (H * (m : ℝ)) * τ) →
    fp81s21_SqErr A.P (fun ω => (Uη ω, UB ω))
      (fun ω => fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
          (flucPathW (wholeSpaceIndex p.d : ℝ) H a (Real.sqrt (N : ℝ)) A.X R.ρ ω) -
        fp81s21_jointC_partialCenter H (∫ ω',
          fp81s21_jointP_map H hH E m (fun j => D (θ j) k)
            (flucPathW (wholeSpaceIndex p.d : ℝ) H a (Real.sqrt (N : ℝ)) A.X R.ρ ω') ∂A.P))
      (Real.sqrt (H * S.MN) * εN m + Real.sqrt (H * S.MN) * εN m +
        Real.sqrt (H * (m : ℝ)) * τ + Ddiag / Real.sqrt (N : ℝ)) := by
  obtain ⟨δa, ha, hah, hdiag⟩ := fp81s21_particle_rankDiagonal_timeSqErr p Es E
  obtain ⟨δb, hb, hbh, hcommon⟩ := fp81s21_particleCoeffMoments_embedded_common p Es
  refine ⟨min δa δb, lt_min ha hb, (min_le_left _ _).trans hah, ?_⟩
  intro δ hδ hδle R εN εG εB S m hε Λ θ D k H hH
  have hδa := hδle.trans (min_le_left _ _)
  have hδb := hδle.trans (min_le_right _ _)
  obtain ⟨M2, hM2, hd⟩ := hdiag δ hδ hδa R
  obtain ⟨M2', M6, hM2', hM6, hc⟩ := hcommon δ hδ hδb R
  obtain ⟨Ddiag, hDdiag, hd⟩ := hd m Λ θ D k H hH
  refine ⟨Ddiag, hDdiag, ?_⟩
  intro N hN A a ha Uη UB hUη hUB τ hτ Ur hUr hker
  obtain ⟨q, hrep, hsix, _, _, _, hqcommon⟩ :=
    hc E N hN A (fp81s21_particleEmpField R N A) (by simp)
  obtain ⟨r, hr, hrsec, Mr, Uraw, hrawrep⟩ :=
    fp81s21_particle_rawPolynomial_time_section_of_common p hδ
      (hδa.trans hah) R Es hN A m (fun j => D (θ j) k) q M6 hM6
      hrep.1 hsix (hqcommon rfl).1 a H ha hH
  have hraw : fp81s21_ParticleRawPolynomialTime31 p R m Λ θ D k N A a H Uraw :=
    (fp81s21_particleRawPolynomialTime31_iff p R m Λ θ D k N A a H Uraw).2
      ⟨Mr, r, hr, hrsec, hrawrep⟩
  have hdiag' := hd N hN A a ha Uraw Mr r hr hrsec hrawrep Ur hUr
  exact fp81s21_jointN_sqerr_of_raw_time p R Es E εN εG εB S m hε Λ θ D k N hN A
    a H ha hH Uη UB Uraw Ur hUη hUB hraw hUr τ _ hτ
    (div_nonneg hDdiag (Real.sqrt_nonneg _)) hker hdiag'

#print axioms fp81s21_jointN_sqerr_physical_fixed_rank
end HRS.Fp81.S21
end
