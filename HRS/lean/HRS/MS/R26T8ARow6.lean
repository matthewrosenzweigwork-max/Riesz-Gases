import HRS.MS.R26T8ARow5

/-!
# S8.2 row lemma, step 6: integrability of the row
`r26t8a_row_integrable`: under the hypotheses of `r26t8a_row_lemma`, `y |-> rho y * F x y` is integrable for every `x`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology Metric
open scoped ContDiff
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

namespace HRS.MS.R26T8A

variable {d : ℕ}

theorem r26t8a_row_integrable (hd : 2 ≤ d) (k b : ℕ) {M : ℝ} (hM : 0 ≤ M) (σ : ℝ) (hσd : σ < d) (K : ℝ) (hK0 : 0 ≤ K)
    {ρ : Euc d → ℝ} (hρ : ContDiff ℝ (k : WithTop ℕ∞) ρ)
    (hK : ∀ i ≤ k, ∀ y : Euc d, ‖iteratedFDeriv ℝ i ρ y‖ ≤ K * (1 + ‖y‖) ^ (-(M + (d : ℝ) + 1)))
    {F : Euc d → Euc d → ℝ} {A : ℝ} (hA : 0 ≤ A) (hF : Conormal k b M σ A F) (x : Euc d) :
    Integrable (fun y => ρ y * F x y) := by
  obtain ⟨s, cE, Cint, hs0, hsd, hcE, hCint0, hmaj⟩ := r26t8a_row_maj hd b σ hσd
  obtain ⟨hWi, -, hWdom⟩ := hmaj x
  set W : Euc d → ℝ := fun u => 2 * (1 + ‖x - u‖) ^ (-((d : ℝ) + 1)) +
      cE * (closedBall (0 : Euc d) 2).indicator (fun u => ‖u‖ ^ (-s)) u with hW
  have hgi : Integrable (fun u => K * jbracket x ^ M * A * W u) := hWi.const_mul _
  have hGm : AEStronglyMeasurable (fun u => r26t8a_row_Gd ρ F u x) volume := by
    refine r26t8a_p07_ae_meas (m := fun u => r26t8a_row_Gd ρ F u x) ?_ hd
    have hcn : ContinuousOn (fun u : Euc d => ρ (x - u) * F x (x - u)) {u : Euc d | u ≠ 0} := by
      have h1 : Continuous (fun u : Euc d => ρ (x - u)) := (hρ.continuous).comp (continuous_const.sub continuous_id)
      have h2 : ContinuousOn (fun u : Euc d => F x (x - u)) {u : Euc d | u ≠ 0} := by
        have hc := (hF.1.continuousOn).comp (continuous_const.prodMk (continuous_const.sub continuous_id)).continuousOn
          (t := {p : Euc d × Euc d | p.1 ≠ p.2}) (s := {u : Euc d | u ≠ 0}) (fun u hu => by
            intro h; apply hu
            have h' : x - (x - u) = 0 := sub_eq_zero.2 h
            simpa using h')
        exact hc
      exact h1.continuousOn.mul h2
    refine hcn.congr (fun u hu => ?_)
    simp [r26t8a_row_Gd, show u ≠ 0 from hu]
  have hGi : Integrable (fun u => r26t8a_row_Gd ρ F u x) := by
    refine Integrable.mono' hgi hGm ?_
    filter_upwards [r26t8a_ae_ne_zero hd] with u hu
    have h1 := r26t8a_row_Gd_bound hM k b σ A K hA hρ hK hF hu x 0 (Nat.zero_le _)
    have hdom := hWdom u (norm_pos_iff.2 hu)
    have hjb0 : 0 ≤ jbracket x ^ M := Real.rpow_nonneg (s83_jb_pos x).le _
    rw [← norm_iteratedFDeriv_zero (𝕜 := ℝ) (f := r26t8a_row_Gd ρ F u) (x := x)]
    refine h1.trans ?_
    simp only [pow_zero, one_mul]
    calc K * jbracket x ^ M * (A * ((1 + ‖x - u‖) ^ (-((d : ℝ) + 1)) *
          (1 + (min 1 ‖u‖) ^ (-(σ + ((0 : ℕ) : ℝ))) * (1 + |Real.log (min 1 ‖u‖)|) ^ b)))
        ≤ K * jbracket x ^ M * (A * W u) :=
          mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hdom hA) (by positivity)
      _ = K * jbracket x ^ M * A * W u := by ring
  have h2 := hGi.comp_sub_left x
  refine h2.congr ?_
  have hne : ∀ᵐ y : Euc d ∂volume, y ≠ x := by
    haveI := r26t8a_nontrivial hd
    rw [ae_iff]; simpa using (measure_singleton x : (volume : Measure (Euc d)) {x} = 0)
  filter_upwards [hne] with y hy
  have hxy : x - y ≠ 0 := sub_ne_zero.2 (Ne.symm hy)
  simp [r26t8a_row_Gd, hxy]

end HRS.MS.R26T8A
