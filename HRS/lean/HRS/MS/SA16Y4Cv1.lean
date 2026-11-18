import HRS.MS.SA16Y4Fam1
import HRS.MS.SA16SOp3

/-!
# S.A.16 (SA16Y4) Cv1: uniform convergence of `div(χ_{n+1}(ρ_n ⋆ b) ψ)` to `div(b ψ)`

`sa16y4_mol_unif_tendsto`: for `h` continuous and `R0`, `ρ_n ⋆ h → h` uniformly on `closedBall 0 R0`.
`sa16y4_divFun_zero_far`: `div(c ψ) = 0` off `closedBall 0 R0` if `ψ = 0` there.
`sa16y4_divFun_tendsto`: for `b_i ∈ C^1`, `ψ ∈ C_c^∞` supported in `closedBall 0 R0`, the functions `div(tm_n(b) ψ)` converge to
`div(b ψ)` uniformly on `Euc d`, with a common support.
-/

noncomputable section
set_option autoImplicit false
open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Whole.AppendixA.Phase2SA16R
open HRS HRS.Whole HRS.Whole.AppendixA Phase2SA16

section Cv1
variable {d : ℕ}

lemma sa16y4_mol_unif_tendsto {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : Continuous h) (R0 : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∃ N : ℕ, ∀ n ≥ N, ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ R0 →
      |(∫ y, h y * sa16y_rho d n (x - y)) - h x| ≤ ε := by
  have hK : IsCompact (closedBall (0 : EuclideanSpace ℝ (Fin d)) (R0 + 1)) := isCompact_closedBall _ _
  obtain ⟨δ, hδ, hδh⟩ := Metric.uniformContinuousOn_iff.1 (hK.uniformContinuousOn_of_continuous hh.continuousOn) ε hε
  obtain ⟨N, hN⟩ := exists_nat_one_div_lt hδ
  refine ⟨N, fun n hn x hx => ?_⟩
  have hρ0 : ∀ z, 0 ≤ sa16y_rho d n z := sa16y_rho_nonneg n
  have hρ1 := sa16y_rho_int (d := d) n
  have hρi : Integrable (fun y => sa16y_rho d n (x - y)) :=
    ((sa16y_rho_smooth (d := d) n).continuous.comp (continuous_const.sub continuous_id)).integrable_of_hasCompactSupport
      (sa16y4_cc_shift (sa16y4_rho_cc n) x)
  have hsub : (∫ y, h y * sa16y_rho d n (x - y)) - h x = ∫ y, (h y - h x) * sa16y_rho d n (x - y) := by
    have : ∫ y, (h y - h x) * sa16y_rho d n (x - y) =
        (∫ y, h y * sa16y_rho d n (x - y)) - h x * ∫ y, sa16y_rho d n (x - y) := by
      rw [← integral_const_mul, ← integral_sub]
      · refine integral_congr_ae (Eventually.of_forall fun y => ?_); ring
      · exact (hh.mul ((sa16y_rho_smooth (d := d) n).continuous.comp (continuous_const.sub continuous_id))).integrable_of_hasCompactSupport
          (sa16y4_cc_shift (sa16y4_rho_cc n) x).mul_left
      · exact hρi.const_mul _
    rw [this, sa16y4_shift_integral hρ1 x, mul_one]
  rw [hsub]
  have := norm_integral_le_of_norm_le (hρi.const_mul ε) (μ := volume)
    (f := fun y => (h y - h x) * sa16y_rho d n (x - y)) (Eventually.of_forall fun y => by
      rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 _)]
      by_cases hz : 1 / ((n : ℝ) + 1) < ‖x - y‖
      · rw [sa16y_rho_supp n _ hz]; simp
      · refine mul_le_mul_of_nonneg_right ?_ (hρ0 _)
        have hz' : ‖x - y‖ ≤ 1 / ((n : ℝ) + 1) := not_lt.1 hz
        have hn1 : 1 / ((n : ℝ) + 1) ≤ 1 / ((N : ℝ) + 1) :=
          one_div_le_one_div_of_le (by positivity) (by exact_mod_cast Nat.succ_le_succ hn)
        have hdist : dist y x < δ := by
          rw [dist_comm, dist_eq_norm]
          exact lt_of_le_of_lt (hz'.trans hn1) hN
        have hy : y ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) (R0 + 1) := by
          rw [mem_closedBall_zero_iff]
          have : ‖y‖ ≤ ‖x‖ + ‖x - y‖ := by
            calc ‖y‖ = ‖x - (x - y)‖ := by congr 1; abel
              _ ≤ ‖x‖ + ‖x - y‖ := norm_sub_le _ _
          have h1 : 1 / ((n : ℝ) + 1) ≤ 1 := by
            rw [div_le_one (by positivity)]; have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith
          linarith
        have hx' : x ∈ closedBall (0 : EuclideanSpace ℝ (Fin d)) (R0 + 1) := by
          rw [mem_closedBall_zero_iff]; linarith
        have := hδh y hy x hx' hdist
        rw [Real.dist_eq] at this
        exact this.le)
  rw [integral_const_mul, sa16y4_shift_integral hρ1 x, mul_one] at this
  simpa [Real.norm_eq_abs] using this

lemma sa16y4_mol_unif_ev {h : EuclideanSpace ℝ (Fin d) → ℝ} (hh : Continuous h) (R0 : ℝ) {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ R0 →
      |(∫ y, h y * sa16y_rho d n (x - y)) - h x| ≤ ε := by
  obtain ⟨N, hN⟩ := sa16y4_mol_unif_tendsto hh R0 hε
  exact (eventually_ge_atTop N).mono fun n hn => hN n hn

lemma sa16y4_divFun_zero_far (bc : Fin d → EuclideanSpace ℝ (Fin d) → ℝ) {ψ : EuclideanSpace ℝ (Fin d) → ℝ}
    {R0 : ℝ} (hψ0 : ∀ x, R0 < ‖x‖ → ψ x = 0) {x : EuclideanSpace ℝ (Fin d)} (hx : R0 < ‖x‖) :
    sa16so_divFun bc ψ x = 0 := by
  have hz : ∀ i : Fin d, fderiv ℝ (fun y => bc i y * ψ y) x = 0 := by
    intro i
    have hev : (fun y => bc i y * ψ y) =ᶠ[𝓝 x] fun _ => (0 : ℝ) := by
      have hn : ∀ᶠ y in 𝓝 x, R0 < ‖y‖ := (isOpen_lt continuous_const continuous_norm).mem_nhds hx
      filter_upwards [hn] with y hy
      simp [hψ0 y hy]
    rw [hev.fderiv_eq]
    simp
  simp [sa16so_divFun, hz]

theorem sa16y4_divFun_tendsto {b : Fin d → EuclideanSpace ℝ (Fin d) → ℝ} (hb : ∀ i, ContDiff ℝ 1 (b i))
    {ψ : EuclideanSpace ℝ (Fin d) → ℝ} (hψ : IsCcInfty ψ) {R0 : ℝ} (hψ0 : ∀ x, R0 < ‖x‖ → ψ x = 0)
    {ε : ℝ} (hε : 0 < ε) :
    ∀ᶠ n : ℕ in atTop, ∀ x : EuclideanSpace ℝ (Fin d),
      |sa16so_divFun (fun i => sa16y4_tm d n (b i)) ψ x - sa16so_divFun b ψ x| ≤ ε := by
  obtain ⟨S, hS⟩ := hψ.1.continuous.bounded_above_of_compact_support hψ.2
  have hψ' : ∀ i : Fin d, IsCcInfty (fun y => fderiv ℝ ψ y (EuclideanSpace.single i 1)) := fun i =>
    sa16s_cc_fderiv hψ _
  have hS' : ∀ i : Fin d, ∃ S', ∀ y, |fderiv ℝ ψ y (EuclideanSpace.single i 1)| ≤ S' := fun i => by
    obtain ⟨S', h⟩ := (hψ' i).1.continuous.bounded_above_of_compact_support (hψ' i).2
    exact ⟨S', fun y => by simpa [Real.norm_eq_abs] using h y⟩
  choose S' hS' using hS'
  set Sm : ℝ := max S 0 + ∑ i, max (S' i) 0 + 1 with hSm
  have hSm0 : 0 < Sm := by
    have : 0 ≤ max S 0 := le_max_right _ _
    have : 0 ≤ ∑ i, max (S' i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
    rw [hSm]; linarith
  set η : ℝ := ε / (2 * ((d : ℝ) + 1) * Sm) with hη
  have hη0 : 0 < η := by positivity
  have hψS : ∀ y, |ψ y| ≤ Sm := fun y => by
    have := hS y
    rw [Real.norm_eq_abs] at this
    have h1 : S ≤ max S 0 := le_max_left _ _
    have : 0 ≤ ∑ i, max (S' i) 0 := Finset.sum_nonneg fun i _ => le_max_right _ _
    have : 0 ≤ max S 0 := le_max_right _ _
    linarith [hS y, Real.norm_eq_abs (ψ y)]
  have hψS' : ∀ i y, |fderiv ℝ ψ y (EuclideanSpace.single i 1)| ≤ Sm := fun i y => by
    have h1 : S' i ≤ max (S' i) 0 := le_max_left _ _
    have h2 : max (S' i) 0 ≤ ∑ j, max (S' j) 0 :=
      Finset.single_le_sum (f := fun j => max (S' j) 0) (fun j _ => le_max_right _ _) (Finset.mem_univ i)
    have : 0 ≤ max S 0 := le_max_right _ _
    linarith [hS' i y]
  have hev1 : ∀ᶠ n : ℕ in atTop, ∀ i : Fin d, ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ R0 →
      |(∫ y, b i y * sa16y_rho d n (x - y)) - b i x| ≤ η := by
    rw [Filter.eventually_all]
    exact fun i => sa16y4_mol_unif_ev (hb i).continuous R0 hη0
  have hev2 : ∀ᶠ n : ℕ in atTop, ∀ i : Fin d, ∀ x : EuclideanSpace ℝ (Fin d), ‖x‖ ≤ R0 →
      |(∫ y, fderiv ℝ (b i) y (EuclideanSpace.single i 1) * sa16y_rho d n (x - y)) -
        fderiv ℝ (b i) x (EuclideanSpace.single i 1)| ≤ η := by
    rw [Filter.eventually_all]
    exact fun i => sa16y4_mol_unif_ev (((hb i).continuous_fderiv (by simp)).clm_apply continuous_const) R0 hη0
  have hev3 : ∀ᶠ n : ℕ in atTop, R0 < (n : ℝ) + 1 := by
    obtain ⟨N, hN⟩ := exists_nat_gt R0
    exact (eventually_ge_atTop N).mono fun n hn => by
      have : (N : ℝ) ≤ n := by exact_mod_cast hn
      linarith
  filter_upwards [hev1, hev2, hev3] with n h1 h2 h3 x
  by_cases hx : R0 < ‖x‖
  · rw [sa16y4_divFun_zero_far _ hψ0 hx, sa16y4_divFun_zero_far _ hψ0 hx]
    simp [hε.le]
  · have hxn : ‖x‖ ≤ R0 := not_lt.1 hx
    have hpd1 : ∀ (f : EuclideanSpace ℝ (Fin d) → ℝ) (i : Fin d) (z : EuclideanSpace ℝ (Fin d)),
        partialDeriv (fun _ : Fin 1 => i) f z = fderiv ℝ f z (EuclideanSpace.single i 1) := by
      intro f i z
      simp [partialDeriv, iteratedFDeriv_one_apply]
    have hterm : ∀ i : Fin d, |fderiv ℝ (fun y => sa16y4_tm d n (b i) y * ψ y) x (EuclideanSpace.single i 1) -
        fderiv ℝ (fun y => b i y * ψ y) x (EuclideanSpace.single i 1)| ≤ 2 * η * Sm := by
      intro i
      set g : EuclideanSpace ℝ (Fin d) → ℝ := fun x => ∫ y, b i y * sa16y_rho d n (x - y) with hg
      have hgs : ContDiff ℝ ∞ g := sa16y4_mol_smooth n (hb i).continuous
      have hev : (fun y => sa16y4_tm d n (b i) y * ψ y) =ᶠ[𝓝 x] fun y => g y * ψ y := by
        have hn : ∀ᶠ y in 𝓝 x, ‖y‖ < (n : ℝ) + 1 := by
          refine (isOpen_lt continuous_norm continuous_const).mem_nhds ?_
          show ‖x‖ < (n : ℝ) + 1
          linarith
        filter_upwards [hn] with y hy
        unfold sa16y4_tm
        rw [sa16j_chi_one d (by positivity) hy.le, one_mul]
      rw [hev.fderiv_eq]
      have hd1 : DifferentiableAt ℝ g x := (hgs.differentiable (by simp)) x
      have hd2 : DifferentiableAt ℝ ψ x := (hψ.1.differentiable (by simp)) x
      have hd3 : DifferentiableAt ℝ (b i) x := ((hb i).differentiable (by simp)) x
      rw [show (fun y => g y * ψ y) = g * ψ from rfl, fderiv_mul hd1 hd2,
        show (fun y => b i y * ψ y) = b i * ψ from rfl, fderiv_mul hd3 hd2]
      simp only [ContinuousLinearMap.add_apply, ContinuousLinearMap.smul_apply, smul_eq_mul]
      have hg' : fderiv ℝ g x (EuclideanSpace.single i 1) =
          ∫ y, fderiv ℝ (b i) y (EuclideanSpace.single i 1) * sa16y_rho d n (x - y) := by
        rw [← hpd1 g i x, hg, sa16y4_mol_pd (sa16y4_rho_cc n) 1 (b i) (by simpa using hb i) (fun _ => i)]
        simp only [hpd1]
      rw [hg']
      have e1 := h1 i x hxn
      have e2 := h2 i x hxn
      have e3 := hψS' i x
      have e4 := hψS x
      have hSm' : 0 ≤ Sm := hSm0.le
      calc |g x * fderiv ℝ ψ x (EuclideanSpace.single i 1) +
            ψ x * (∫ y, fderiv ℝ (b i) y (EuclideanSpace.single i 1) * sa16y_rho d n (x - y)) -
          (b i x * fderiv ℝ ψ x (EuclideanSpace.single i 1) + ψ x * fderiv ℝ (b i) x (EuclideanSpace.single i 1))|
          = |(g x - b i x) * fderiv ℝ ψ x (EuclideanSpace.single i 1) +
            ψ x * ((∫ y, fderiv ℝ (b i) y (EuclideanSpace.single i 1) * sa16y_rho d n (x - y)) -
              fderiv ℝ (b i) x (EuclideanSpace.single i 1))| := by congr 1; ring
        _ ≤ |(g x - b i x) * fderiv ℝ ψ x (EuclideanSpace.single i 1)| +
            |ψ x * ((∫ y, fderiv ℝ (b i) y (EuclideanSpace.single i 1) * sa16y_rho d n (x - y)) -
              fderiv ℝ (b i) x (EuclideanSpace.single i 1))| := abs_add_le _ _
        _ ≤ η * Sm + Sm * η := by
            rw [abs_mul, abs_mul]
            exact add_le_add (mul_le_mul e1 e3 (abs_nonneg _) hη0.le) (mul_le_mul e4 e2 (abs_nonneg _) hSm')
        _ = 2 * η * Sm := by ring
    unfold sa16so_divFun
    rw [← Finset.sum_sub_distrib]
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    refine (Finset.sum_le_sum fun i _ => hterm i).trans ?_
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
    have : (d : ℝ) * (2 * η * Sm) ≤ ε := by
      rw [hη]
      have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      calc (d : ℝ) * (2 * (ε / (2 * ((d : ℝ) + 1) * Sm)) * Sm) = ε * ((d : ℝ) / ((d : ℝ) + 1)) := by
            field_simp
        _ ≤ ε * 1 := mul_le_mul_of_nonneg_left (by rw [div_le_one (by positivity)]; linarith) hε.le
        _ = ε := mul_one ε
    exact this

end Cv1

end HRS.Whole.AppendixA.Phase2SA16R
