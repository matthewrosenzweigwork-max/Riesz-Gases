import HRS.MS.Fp81S21RespRecon13

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.S111X2

/-- The actual response commutes almost everywhere with the normalized
cosine integral defining a shifted qwin feature. -/
theorem fp81s21_respRecon_qwin_interchange_ae (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, 0 < p.γ →
        ∀ a : ℝ, 0 ≤ a → ∀ j : ℕ,
          r26t3_a R (r26t3_qwin R a j) =ᵐ[r26t3_mu R 0]
            fun x => ∫ t in Icc (0 : ℝ) p.T,
              r26t3_a R (fun y =>
                (1 + ((r26t3_feature_enum p.d j).1 : ℝ) ^ 2) ^ (3 / 8 : ℝ) *
                r26t3_cosine p.T (r26t3_feature_enum p.d j).1 t *
                r26t3_U R 0 (a + t)
                  (oscTestFun (wholeSpaceIndex p.d : ℝ) (r26t3_feature_enum p.d j).2) y) x := by
  obtain ⟨δi, hi, hihalf, hinter⟩ := fp81s21_respRecon_orbit_interchange_ae p
  obtain ⟨δq, hq, hqhalf, hqwin⟩ := fp81s21_qwin_uniform p
  refine ⟨min δi δq, lt_min hi hq, (min_le_left _ _).trans hihalf,
    fun δ hδ hδle R hγ a ha j => ?_⟩
  have hδi := hδle.trans (min_le_left δi δq)
  have hδq := hδle.trans (min_le_right δi δq)
  have hδh := hδi.trans hihalf
  obtain ⟨-, -, -, href⟩ := r26t3_reference_data p δ hδ hδh R
  obtain ⟨M, c, S, hc, hTc⟩ := href 0
  haveI : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hTc.prob
  obtain ⟨_, _, hfamily⟩ := hqwin δ hδ hδq R
  let n := (r26t3_feature_enum p.d j).1
  let α := (r26t3_feature_enum p.d j).2
  let A : ℝ := (1 + (n : ℝ) ^ 2) ^ (3 / 8 : ℝ)
  let w : ℝ → ℝ := fun t => A * r26t3_cosine p.T n t
  have hcos : ∀ t, r26t3_cosine p.T n t = r2CosBasis p.T n t := by
    intro t
    unfold r26t3_cosine r2CosBasis
    split_ifs <;> simp [one_div]
  have hw : Continuous w := by
    simp only [w, hcos]
    exact continuous_const.mul (HRS.MS.R2WinOrb.s103_cosBasis_continuous p.T n)
  let C := |A| * Real.sqrt (2 / p.T)
  have hC : 0 ≤ C := mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hwbound : ∀ t ∈ Icc (0 : ℝ) p.T, |w t| ≤ C := by
    intro t ht
    dsimp [w, C]
    rw [abs_mul, hcos]
    exact mul_le_mul_of_nonneg_left (s11p_cos_bound p.hT n t) (abs_nonneg _)
  have hQ : (fun x => ∫ t in Icc (0 : ℝ) p.T,
      w t * r26t3_U R 0 (a + t) (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x) =
      r26t3_qwin R a j := by
    funext x
    dsimp [w, A, n, α, r26t3_qwin]
    rw [← integral_const_mul]
    apply integral_congr_ae
    filter_upwards with t
    ring
  have hQmem : MemLp (fun x => ∫ t in Icc (0 : ℝ) p.T,
      w t * r26t3_U R 0 (a + t) (oscTestFun (wholeSpaceIndex p.d : ℝ) α) x)
      2 (r26t3_mu R 0) := by
    rw [hQ]
    exact HRS.MS.Tc5.tc5_memLp_of_cb ((hfamily a ha).1.1 j)
  have h := hinter δ hδ hδi R hγ a ha α w hw C hC hwbound hQmem
  rw [hQ] at h
  exact h

#print axioms fp81s21_respRecon_qwin_interchange_ae

end HRS.Fp81.S21
end
