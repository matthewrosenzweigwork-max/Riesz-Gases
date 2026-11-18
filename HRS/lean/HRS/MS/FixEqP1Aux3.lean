import HRS.MS.FixEqP1Aux2

/-!
# S5.7 `fixed_equation` (worker S57P), part 3: continuous version of the Gaussian noise (packet P4 core)

`s57p_noise_exists`: for an isonormal process `W` on a Hilbert space `H` and a Hilbert-Schmidt kernel family
`kappa_t(alpha) in H` that is `1/2`-Holder in `t` in the Hilbert-Schmidt norm, there is a measurable `OscDual`-valued process `X`,
continuous in `t in [0,T]` for EVERY sample point, with `coord_alpha (X_t) = W(kappa_t(alpha))` a.s. for each `t in [0,T]`.
Proof: fourth moments (`s57p_fourth_moment`) and Kolmogorov-Chentsov (`HRS.MP.KC.mkc_Zc_ae_eq`).
Two families sharing the same `W` (the coupling of `fixed_equation`) are obtained by applying this twice.
-/

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology
open scoped ENNReal NNReal

namespace HRS.MS.FixEq

open HRS HRS.Whole

variable {d : ℕ}

open HRS.MS.U10 in
theorem s57p_noise_exists {H : Type} [NormedAddCommGroup H] [InnerProductSpace ℝ H] [CompleteSpace H]
    {Ω₀ : Type} [MeasurableSpace Ω₀] {Q : Measure Ω₀} [IsProbabilityMeasure Q] {W : H → Ω₀ → ℝ}
    (hI : Sb7Iso Q W) (hlaw : ∀ g, Q.map (W g) = gaussianReal 0 (Real.toNNReal (‖g‖ ^ 2)))
    {T K : ℝ} (hT : 0 < T) (m : ℝ) (κ : ℝ → MultiIndex d → H)
    (hκ0 : ∀ t ∈ Set.Icc (0 : ℝ) T, Summable fun α => ‖κ t α‖ ^ 2)
    (hκ : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∑' α, ‖κ t α - κ s α‖ ^ 2 ≤ K * |t - s|) :
    ∃ X : ℝ → Ω₀ → OscDual d m, (∀ t, Measurable (X t)) ∧
      (∀ w, ContinuousOn (fun t => X t w) (Set.Icc 0 T)) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α, ∀ᵐ w ∂Q, OscDual.coord (X t w) α = W (κ t α) w := by
  obtain ⟨M, hM0, hM⟩ := HRS.MP.RdLGS.rlg_gauss_fourth
  let Xr : ℝ → Ω₀ → OscDual d m := fun t w => ellVec m (fun α => W (κ t α) w)
  have hXm : ∀ t, Measurable (Xr t) := fun t => s57p_measurable_ellVec _ (fun α => hI.meas _)
  have hmom : ∀ s ∈ Set.Icc (0 : ℝ) T, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ∫⁻ w, ‖Xr t w - Xr s w‖ₑ ^ (4 : ℝ) ∂Q ≤ ENNReal.ofReal (M * K ^ 2 * |t - s| ^ (1 + (1 : ℝ))) := by
    intro s hs t ht
    have e : ∫⁻ w, ‖Xr t w - Xr s w‖ₑ ^ (4 : ℝ) ∂Q = ∫⁻ w, ‖Xr t w - Xr s w‖ₑ ^ 4 ∂Q :=
      lintegral_congr fun w => HRS.MP.RdLGS.rlg_rpow4 _
    rw [e]
    refine (s57p_fourth_moment hI hlaw hM0 hM (m := m) (κ t) (κ s) (hκ0 t ht) (hκ0 s hs)).trans ?_
    apply ENNReal.ofReal_le_ofReal
    rw [HRS.MP.RdLGS.rlg_rpow2]
    have h1 := hκ s hs t ht
    have h0 : 0 ≤ ∑' α, ‖κ t α - κ s α‖ ^ 2 := tsum_nonneg fun α => sq_nonneg _
    have h2 : (∑' α, ‖κ t α - κ s α‖ ^ 2) ^ 2 ≤ (K * |t - s|) ^ 2 := pow_le_pow_left₀ h0 h1 2
    calc M * (∑' α, ‖κ t α - κ s α‖ ^ 2) ^ 2 ≤ M * (K * |t - s|) ^ 2 := mul_le_mul_of_nonneg_left h2 hM0
      _ = M * K ^ 2 * |t - s| ^ 2 := by ring
  obtain ⟨r, q, hr0, hr1, hq0, hq1, hqr⟩ := HRS.MP.KC.mkc_consts (β := 1) (p := 4) one_pos (by norm_num)
  refine ⟨HRS.MP.KC.mkc_Zc Xr T r, HRS.MP.KC.mkc_Zc_meas Xr T r hT hr0.le hr1 hXm, fun w => ?_, ?_⟩
  · exact continuousOn_iff_continuous_restrict.2 (HRS.MP.KC.mkc_continuous Xr T r hT hr0.le hr1 w)
  · intro t ht α
    have h1 := HRS.MP.KC.mkc_Zc_ae_eq Xr T r Q hXm (p := 4) (β := 1) (C := M * K ^ 2) (q := q) hT
      (by norm_num) one_pos hmom hr0 hr1 hq0 hq1 hqr ht
    filter_upwards [h1, s57p_ae_memℓp hI (κ t) (hκ0 t ht)] with w hw hmem
    rw [hw]
    exact s57p_coord_ellVec hmem α

end HRS.MS.FixEq
