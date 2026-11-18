import HRS.MS.Fp81S21RespRecon16

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3

/-- Every cosine analysis coordinate of the response window is the
response of the corresponding shifted qwin feature. -/
theorem fp81s21_respRecon_obs (p : Parameters) :
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ, 0 < p.γ →
        ∀ a : ℝ, 0 ≤ a → ∀ x : Euc p.d, ∀ j : ℕ,
          fp81s21_cosRecon_obs26 p (responseWindow R a x) j =
            r26t3_a R (r26t3_qwin R a j) x := by
  obtain ⟨δa, ha0, hahalf, hae⟩ := fp81s21_respRecon_obs_ae p
  obtain ⟨δc, hc0, hchalf, hcont⟩ := fp81s21_respRecon_obs_continuous p
  obtain ⟨δq, hq0, hqhalf, hqwin⟩ := fp81s21_qwin_uniform p
  let D := min δa (min δc δq)
  have hDa : D ≤ δa := min_le_left _ _
  have hDc : D ≤ δc := (min_le_right _ _).trans (min_le_left _ _)
  have hDq : D ≤ δq := (min_le_right _ _).trans (min_le_right _ _)
  refine ⟨D, lt_min ha0 (lt_min hc0 hq0), hDa.trans hahalf,
    fun δ hδ hδle R hγ a ha x j => ?_⟩
  have hδh := hδle.trans (hDa.trans hahalf)
  obtain ⟨_, _, hfamily⟩ := hqwin δ hδ (hδle.trans hDq) R
  obtain ⟨C, hC, hsmooth⟩ := r26t3_response_smooth hδ hδh R hγ
  have hleft := hcont δ hδ (hδle.trans hDc) R hγ a ha j
  have hright : Continuous (r26t3_a R (r26t3_qwin R a j)) :=
    (hsmooth _ ((hfamily a ha).1.1 j)).1.1.continuous
  have heq := fp81s21_respRecon_ae_to_everywhere hδ hδh R
    (fun x => fp81s21_cosRecon_obs26 p (responseWindow R a x) j)
    (r26t3_a R (r26t3_qwin R a j)) hleft hright
    (hae δ hδ (hδle.trans hDa) R hγ a ha j)
  exact congrFun heq x

#print axioms fp81s21_respRecon_obs

end HRS.Fp81.S21
end
