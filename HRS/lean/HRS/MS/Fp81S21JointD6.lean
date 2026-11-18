import HRS.MS.Fp81S21JointD5

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open Classical MeasureTheory Filter
open scoped BigOperators RealInnerProductSpace

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The uniform time-class diagonal error for the actual particle rank field.
The raw polynomial representative is quantified by its measurable field,
simultaneous a.e. polynomial identity, and `TimeL2Rep`; the rank representative
uses the repository's `ParticleRankTime31` predicate. The error constant is
fixed after the time horizon and finite-rank data, and before particle count. -/
theorem fp81s21_particle_rankDiagonal_timeSqErr
    (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ M2 : ℝ, 0 ≤ M2 ∧
          ∀ m : ℕ, ∀ Λ : ℝ,
          ∀ θ : Fin m → HRS.MS.R2S11.s11V p.d Λ,
          ∀ D : HRS.MS.R2S11.s11V p.d Λ → ℕ → fp81s21_RankKernel p.d,
          ∀ k : ℕ, ∀ H : ℝ, 0 < H →
            ∃ Ddiag : ℝ, 0 ≤ Ddiag ∧
              ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
              ∀ a : ℝ, 0 ≤ a →
              ∀ Uraw : A.Ω → Lp r26t6_Coeff 2
                (volume.restrict (Set.Icc (0 : ℝ) H)),
              ∀ Mraw : ℝ, ∀ qraw : ℝ → A.Ω → r26t6_Coeff,
                Measurable (Function.uncurry qraw) →
                (∀ᵐ ω ∂A.P, ∀ u : ℝ, 0 ≤ u →
                  qraw u ω = ∑ j : Fin m,
                    fp81s21_polyAtD (D (θ j) k)
                      (fp81s21_rawEtaAt R A u ω) • fp81s21_coeffBasis j) →
                fp81s21_TimeL2Rep A.P qraw Mraw a H Uraw →
                ∀ Urank : A.Ω → Lp r26t6_Coeff 2
                  (volume.restrict (Set.Icc (0 : ℝ) H)),
                  fp81s21_ParticleRankTime31 p R m Λ θ D k N A a H Urank →
                  fp81s21_SqErr A.P (fp81s21_center A.P Uraw) Urank
                    (Ddiag / Real.sqrt (N : ℝ)) := by
  obtain ⟨δ0, hδ0, hδhalf, hUniform⟩ :=
    fp81s21_particle_rankDiagonal_per_time p Es E
  refine ⟨δ0, hδ0, hδhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨M2, hM2, hdiagUniform⟩ := hUniform δ hδ hδle R
  refine ⟨M2, hM2, ?_⟩
  intro m Λ θ D k H hH
  let Ds : Fin m → fp81s21_RankKernel p.d := fun j => D (θ j) k
  let Ddiag : ℝ := Real.sqrt (H * ((m : ℝ) * ∑ j : Fin m,
    M2 * (weightedSobolevE (2 * p.d + 6) ((p.d : ℝ) + 4)
      (fp81s21_rankKernelDiagonal (Ds j))).toReal ^ 2 / 4))
  have hDdiag : 0 ≤ Ddiag := by
    exact Real.sqrt_nonneg _
  refine ⟨Ddiag, hDdiag, ?_⟩
  intro N hN A a ha Uraw Mraw qraw hqraw hraw hrawRep Urank hRank
  rcases hRank with ⟨Mrank, qrank, hqrank, hrank, hrankRep⟩
  have hfixed := fp81s21_particle_rankDiagonal_timeSqErr_fixed
    p hδ (le_trans hδle hδhalf) R Es E M2 hM2 m Ds hN A a H ha hH
    (fun j u hu => hdiagUniform (Ds j) N hN A u hu)
    Uraw Mraw qraw hqraw hraw hrawRep
    Urank Mrank qrank hqrank hrank hrankRep
  simpa [Ddiag, Ds] using hfixed

#print axioms fp81s21_particle_rankDiagonal_timeSqErr

end HRS.Fp81.S21
end
