import HRS.MS.Fp81S21WickMomRep10

/-! Physical quadratic weak-chart time sections and spatial projection tails. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The universal projection profile with propositionally equal chart indices. -/
theorem fp81s21_wick_time_projection_profile_normalized
    {d r r' : ℕ} {Pw Ps : ℝ}
    (hr : r + 2 = r') (hp : Pw + 2 = Ps)
    (hP : (d : ℝ) < 2 * Pw) (hPs : (d : ℝ) < 2 * Ps)
    (Es : r26t6_WeightedChart d r Ps) (E : r26t6_WeightedChart d r' Pw) :
    ∃ ε : ℕ → ℝ, (∀ m, 0 ≤ ε m) ∧ Tendsto ε atTop (𝓝 0) ∧
      ∀ M : ℝ, 0 ≤ M → ∀ {Ω : Type*} [MeasurableSpace Ω]
        (P : Measure Ω) [IsProbabilityMeasure P]
        (Q : ℝ → Ω → (Euc d → ℝ) → ℝ)
        (qs : ℝ → Ω → r26t6_Coeff),
        fp81s21_MomentRep Es P Q qs M →
        ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 ≤ H →
          ∃ U : Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
            let qe : ℝ → Ω → r26t6_Coeff := fun u ω =>
              fp81s21_embedField_normalized hr hp hP hPs Es E (qs u ω)
            fp81s21_TimeL2Rep P qe M a H U ∧
            fp81s21_TimeRep E P (fun u ω => fp81s21_chartAction E (qe u ω))
              qe M a H U ∧
            ∀ m, fp81s21_SqErr P U (fun ω => fp81s21_timeProject H m (U ω))
              (Real.sqrt (H * M) * ε m) ∧
              ∀ ρ : ℝ, 0 < ρ →
                P {ω | ρ < ‖U ω - fp81s21_timeProject H m (U ω)‖} ≤
                  ENNReal.ofReal (H * M * (ε m) ^ 2 / ρ ^ 2) := by
  subst r'
  subst Ps
  simpa [fp81s21_embedField_normalized] using
    fp81s21_wick_time_projection_profile hP hPs Es E

/-- A single spatial tail profile precedes the physical parameters and all
realizations. The time projection retains finitely many spatial coordinates. -/
theorem fp81s21_gaussian_wick_weakChart_time_tails (p : Parameters)
    (Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4))
    (E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2)) :
    ∃ ε : ℕ → ℝ, (∀ m, 0 ≤ ε m) ∧ Tendsto ε atTop (𝓝 0) ∧
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
      ∃ Kstar B : ℝ, 0 ≤ Kstar ∧ 0 ≤ B ∧ ∀ G : GaussianRealization R,
      ∃ T : ℝ → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ) →L[ℝ] Lp ℝ 2 G.P,
      ∃ W : ℝ → Lp ℝ 2 ((HRS.Whole.withDensityReal R.ρβ).prod
        (HRS.Whole.withDensityReal R.ρβ)) →L[ℝ] Lp ℝ 2 G.P,
      ∃ q qe : ℝ → G.Ω → r26t6_Coeff,
        (∀ u : ℝ, 0 ≤ u → ∃ hL : ‖T u‖ ≤ Kstar,
          ∃ hJoint : ∀ n (v : Fin n → Lp ℝ 2 (HRS.Whole.withDensityReal R.ρβ)),
            HRS.IsCenteredGaussian (G.P.map fun ω => fun i => (T u (v i)) ω),
            W u = fp81s21_wickFam_operator R G (T u) Kstar hL hJoint) ∧
        (∀ u : ℝ, 0 ≤ u → ∀ φ : Euc p.d → ℝ,
          IsOscTest (wholeSpaceIndex p.d : ℝ) φ →
          ∀ hφ : MemLp φ 2 (HRS.Whole.withDensityReal R.ρβ),
          (T u (hφ.toLp φ) : G.Ω → ℝ) =ᵐ[G.P]
            fun ω => OscDual.eval (G.Z u ω) φ) ∧
        (∀ u ω, qe u ω = fp81s21_gaussian_chartEmbed p Es E (q u ω)) ∧
        fp81s21_MomentRep Es G.P (fp81s21_wickChartField Es q) q
          (Kstar ^ 4 * B / 2) ∧
        fp81s21_MomentRep E G.P (fp81s21_wickChartField Es q) qe
          (Kstar ^ 4 * B / 2) ∧
        (∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ, IsR2Test f →
          ∃ hker : MemLp (fun xy : Euc p.d × Euc p.d =>
            commutatorKernel p.d p.s (gradient f) xy.1 xy.2) 2
            ((HRS.Whole.withDensityReal R.ρβ).prod (HRS.Whole.withDensityReal R.ρβ)),
          (fun ω => fp81s21_wickChartField Es q u ω f) =ᵐ[G.P]
            (W u (hker.toLp (fun xy : Euc p.d × Euc p.d =>
              commutatorKernel p.d p.s (gradient f) xy.1 xy.2)) : G.Ω → ℝ)) ∧
        (∀ u : ℝ, 0 ≤ u →
          (AEMeasurable (fun ω => dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
            (fp81s21_wickChartField Es q u ω)) G.P ∧
            (∫⁻ ω, dualNormE (2 * p.d + 6) ((p.d : ℝ) + 4)
              (fp81s21_wickChartField Es q u ω) ∂G.P) ≤
                ENNReal.ofReal (Real.sqrt (Kstar ^ 4 * B / 2))) ∧
          (AEMeasurable (fun ω => dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
            (fp81s21_wickChartField Es q u ω)) G.P ∧
            (∫⁻ ω, dualNormE (2 * p.d + 8) ((p.d : ℝ) + 2)
              (fp81s21_wickChartField Es q u ω) ∂G.P) ≤
                ENNReal.ofReal (Real.sqrt (Kstar ^ 4 * B / 2)))) ∧
        ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
          ∃ U : G.Ω → Lp r26t6_Coeff 2 (volume.restrict (Set.Icc (0 : ℝ) H)),
            fp81s21_TimeL2Rep G.P qe (Kstar ^ 4 * B / 2) a H U ∧
            fp81s21_TimeRep E G.P (fun u ω => fp81s21_chartAction E (qe u ω))
              qe (Kstar ^ 4 * B / 2) a H U ∧
            ∀ m, fp81s21_SqErr G.P U (fun ω => fp81s21_timeProject H m (U ω))
              (Real.sqrt (H * (Kstar ^ 4 * B / 2)) * ε m) ∧
              ∀ ρ : ℝ, 0 < ρ →
                G.P {ω | ρ < ‖U ω - fp81s21_timeProject H m (U ω)‖} ≤
                  ENNReal.ofReal (H * (Kstar ^ 4 * B / 2) * (ε m) ^ 2 / ρ ^ 2) := by
  obtain ⟨ε, hε, hεlim, hprofile⟩ :=
    fp81s21_wick_time_projection_profile_normalized (by omega) (by ring)
      (by nlinarith) (by nlinarith) Es E
  obtain ⟨δ0, hδ0, hhalf, hphys⟩ := fp81s21_wick_momentRep_physical p
  refine ⟨ε, hε, hεlim, δ0, hδ0, hhalf, ?_⟩
  intro δ hδ hδle R
  obtain ⟨K, B, hK, hB, hG⟩ := hphys δ hδ hδle R Es E
  refine ⟨K, B, hK, hB, ?_⟩
  intro G
  obtain ⟨T, W, q, hW, hT, hs, hw, hag, hfirst⟩ := hG G
  let qe : ℝ → G.Ω → r26t6_Coeff := fun u ω =>
    fp81s21_gaussian_chartEmbed p Es E (q u ω)
  refine ⟨T, W, q, qe, hW, hT, (fun _ _ => rfl), hs, hw, hag, hfirst, ?_⟩
  intro a ha H hH
  have hM : 0 ≤ K ^ 4 * B / 2 := by positivity
  have ht := hprofile (K ^ 4 * B / 2) hM G.P
    (fp81s21_wickChartField Es q) q hs a ha H (le_of_lt hH)
  simpa [qe, fp81s21_gaussian_chartEmbed] using ht

#print axioms fp81s21_wick_time_projection_profile_normalized
#print axioms fp81s21_gaussian_wick_weakChart_time_tails
end HRS.Fp81.S21
end
