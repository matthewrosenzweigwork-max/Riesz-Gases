import HRS.MC.S7S7dAux8

/-!
# Packet `s7_S7d_uniform_limits`, helper 9: finite-dimensional core of (R3), uniform over the Stein class

For `0 < γ`, smooth `v` with uniformly bounded fourth moments of `B_N(v)`, `κ : Fin p → modes` and `η > 0` there is `N₀`
such that for all `N ≥ N₀`, `f` in `s7d_Cl` and `‖u‖ ≤ 1`:
`| E[B_N Df(ι cs_N)[u]] - ½ Σ_{b,c} Q_{v;bc} ∫ D³f(ι z)[u,ι e_b,ι e_c] dN(0,C)(z) | ≤ η`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7d

open HRS HRS.Sec7 HRS.MC.SEdge

variable {d : ℕ} {s : ℝ} {r : ℝ}

theorem s7d_prod_norm_pow {p : ℕ} (x : ℝ × EuclideanSpace ℝ (Fin p)) :
    ‖x‖ ^ ((2 : ℝ) + 2) ≤ |x.1| ^ (2 * 2) + ‖x.2‖ ^ ((2 : ℝ) + 2) := by
  rw [s7d_rpow_four, s7d_rpow_four, Prod.norm_def, Real.norm_eq_abs]
  have h1 : (2 * 2 : ℕ) = 4 := rfl
  rw [h1]
  rcases le_total |x.1| ‖x.2‖ with h | h
  · rw [max_eq_right h]; have : 0 ≤ |x.1| ^ 4 := by positivity
    linarith
  · rw [max_eq_left h]; have : 0 ≤ ‖x.2‖ ^ 4 := by positivity
    linarith

theorem s7d_core_R3 (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {γ : ℝ} (hγ : 0 < γ)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {p : ℕ} (κ : Fin p → NonzeroLattice d)
    {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j))
    (hBm : ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      Integrable (fun X => |sed_B d s ρ γ v X| ^ (2 * 2)) (sed_Q d s N γ ρ) ∧
        ∫ X, |sed_B d s ρ γ v X| ^ (2 * 2) ∂(sed_Q d s N γ ρ) ≤ C)
    {η : ℝ} (hη : 0 < η) :
    ∃ N₀ : ℕ, ∀ N ≥ N₀, 1 ≤ N → ∀ f : NegSobolev d r → ℝ, s7d_Cl f → ∀ u : NegSobolev d r, ‖u‖ ≤ 1 →
      |∫ X, sed_B d s ρ γ v X *
            fderiv ℝ f (HRS.MC.Sec7.S7c.s7c_iota r κ
              (centeredStat (sed_Q d s N γ ρ) (fun a => s7_phi r (κ a)) X)) u ∂(sed_Q d s N γ ρ) -
        (1 / 2) * ∑ b, ∑ c,
          sed_Qt d s ρ v (responseInverse (periodicRiesz d s) (withDensityReal ρ) γ (s7_phi r (κ b)))
              (responseInverse (periodicRiesz d s) (withDensityReal ρ) γ (s7_phi r (κ c))) *
            ∫ z, iteratedFDeriv ℝ 3 f (HRS.MC.Sec7.S7c.s7c_iota r κ z)
              ![u, s7_eps r (κ b), s7_eps r (κ c)]
              ∂(multivariateGaussian 0 (sed_Cmat d s γ ρ (fun a => s7_phi r (κ a))))| ≤ η := by
  classical
  set φ : Fin p → Torus d → ℝ := fun a => s7_phi r (κ a) with hφdef
  have hφ : ∀ a, Torus.IsSmooth (φ a) := fun a => HRS.MC.Sec7.S7a.s7a_phi_smooth r (κ a)
  have hφc : ∀ a, Continuous (φ a) := fun a => HRS.Q66.q66_cont_of_smooth (hφ a)
  have hQ : ∀ n : ℕ, IsProbabilityMeasure (sed_Q d s (n + 1) γ ρ) := fun n =>
    HRS.MC.SEdge.B4b.b4b_isProb hd hs0 hs hγ.le hρ (n + 1) (by omega)
  obtain ⟨ν, hν, hνw⟩ := s7d_B_weak hd hs0 hs hγ hρ hφ hv
  -- measurability of the pair
  have hBmeas : ∀ n : ℕ, Measurable (fun X : Config d (n + 1) => sed_B d s ρ γ v X) := by
    intro n
    obtain ⟨B, c, hc, hB⟩ := HRS.MC.SEdge.B2a.sed_B2a_envelope_proof hd hs0 hs hv
    have hsd : s < (d : ℝ) := by
      have : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg d
      linarith
    have hvc : ∀ j, Continuous (v j) := fun j => HRS.Q66.q66_cont_of_smooth (hv j)
    have hmeas := HRS.Q66.q66_hv_measurable hsd hvc
    have hsymm := HRS.Q66.q66_hv_symm hsd v
    obtain ⟨e, he⟩ := HRS.MC.SEdge.B3.sed_B3_onb_proof (by omega) hρ
    have hφ' : ∀ a, Measurable (φ a) ∧ ∃ M, ∀ x, |φ a x| ≤ M := fun a =>
      ⟨(HRS.MC.SEdge.B9.b9_cont_of_smooth (hφ a)).2.1, (HRS.MC.SEdge.B9.b9_cont_of_smooth (hφ a)).2.2⟩
    let D : HRS.Q08.Q08Data d := HRS.MC.SEdge.B9a.b9a_D hd hs0 hs hγ hρ c hc B (HRS.Q66.q66_hv d s v)
      hmeas hsymm hB e he p φ hφ'
    exact (HRS.Q08.q08_measurable_stat D (n + 1)).fst
  have hcsmeas : ∀ n : ℕ, Measurable (centeredStat (sed_Q d s (n + 1) γ ρ) φ) := fun n =>
    HRS.MC.Sec7.S7c.s7c_cs_meas (by omega) _ φ hφc
  have hpm : ∀ n : ℕ, Measurable (fun X : Config d (n + 1) =>
      (sed_B d s ρ γ v X, centeredStat (sed_Q d s (n + 1) γ ρ) φ X)) := fun n =>
    (hBmeas n).prodMk (hcsmeas n)
  let μ : ℕ → Measure (ℝ × EuclideanSpace ℝ (Fin p)) := fun n =>
    (sed_Q d s (n + 1) γ ρ).map (fun X => (sed_B d s ρ γ v X, centeredStat (sed_Q d s (n + 1) γ ρ) φ X))
  haveI hμ : ∀ n, IsProbabilityMeasure (μ n) := fun n =>
    (Measure.isProbabilityMeasure_map_iff (hpm n).aemeasurable).2 (hQ n)
  have hweak : ∀ F : ℝ × EuclideanSpace ℝ (Fin p) → ℝ, Continuous F → (∃ M, ∀ x, |F x| ≤ M) →
      Tendsto (fun n => ∫ x, F x ∂(μ n)) atTop (𝓝 (∫ x, F x ∂ν)) := by
    intro F hF hb
    refine (hνw F hF hb).congr fun n => ?_
    exact (integral_map (hpm n).aemeasurable hF.aestronglyMeasurable).symm
  obtain ⟨CB, hCB⟩ := hBm
  obtain ⟨C4, hC4⟩ := s7d_fourth_moment hd hs0 hs hγ.le hρ hφ
  have hmom : ∀ n, Integrable (fun x : ℝ × EuclideanSpace ℝ (Fin p) => ‖x‖ ^ ((2 : ℝ) + 2)) (μ n) ∧
      ∫ x, ‖x‖ ^ ((2 : ℝ) + 2) ∂(μ n) ≤ CB + C4 := by
    intro n
    obtain ⟨hB1, hB2⟩ := hCB (n + 1) (by omega)
    obtain ⟨hC1, hC2⟩ := hC4 (n + 1) (by omega)
    have hc : Continuous fun x : ℝ × EuclideanSpace ℝ (Fin p) => ‖x‖ ^ ((2 : ℝ) + 2) := by
      simp only [s7d_rpow_four]; fun_prop
    have hI : Integrable (fun X : Config d (n + 1) =>
        ‖(sed_B d s ρ γ v X, centeredStat (sed_Q d s (n + 1) γ ρ) φ X)‖ ^ ((2 : ℝ) + 2))
        (sed_Q d s (n + 1) γ ρ) := by
      refine (hB1.add hC1).mono' (hc.measurable.comp (hpm n)).aestronglyMeasurable
        (Filter.Eventually.of_forall fun X => ?_)
      rw [Real.norm_eq_abs, abs_of_nonneg (by positivity)]
      exact s7d_prod_norm_pow _
    refine ⟨(integrable_map_measure hc.aestronglyMeasurable (hpm n).aemeasurable).2 hI, ?_⟩
    have hmap : ∫ x, ‖x‖ ^ ((2 : ℝ) + 2) ∂(μ n) =
        ∫ X, ‖(sed_B d s ρ γ v X, centeredStat (sed_Q d s (n + 1) γ ρ) φ X)‖ ^ ((2 : ℝ) + 2)
          ∂(sed_Q d s (n + 1) γ ρ) := integral_map (hpm n).aemeasurable hc.aestronglyMeasurable
    rw [hmap]
    refine le_trans (integral_mono hI (hB1.add hC1) fun X => s7d_prod_norm_pow _) ?_
    exact ((integral_add hB1 hC1).trans_le (add_le_add hB2 hC2) :)
  set ι := HRS.MC.Sec7.S7c.s7c_iota r κ with hι
  set h : ℝ × EuclideanSpace ℝ (Fin p) →L[ℝ] ℝ := ContinuousLinearMap.fst ℝ ℝ (EuclideanSpace ℝ (Fin p)) with hh
  obtain ⟨n₀, hn₀⟩ := s7d_uniform_ident μ ν hweak hmom h zero_le_one ‖ι‖₊ hη
  refine ⟨n₀ + 1, fun N hN hN1 f hf u hu => ?_⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  have hn : n ≥ n₀ := by omega
  set Ψ := s7d_Psi1 f ι u with hΨ
  have hΨc : Continuous Ψ := (s7d_Psi1_contDiff hf.1 ι u).continuous
  have hb : ∀ x : ℝ × EuclideanSpace ℝ (Fin p), |Ψ x.2| ≤ 1 := fun x =>
    (s7d_Psi1_bdd hf ι u x.2).trans hu
  have hl : LipschitzWith ‖ι‖₊ (fun x : ℝ × EuclideanSpace ℝ (Fin p) => Ψ x.2) := by
    have h1 := (s7d_Psi1_lip hf ι u).comp (LipschitzWith.prod_snd (α := ℝ) (β := EuclideanSpace ℝ (Fin p)))
    refine h1.weaken ?_
    have : ‖u‖₊ ≤ 1 := by exact_mod_cast hu
    calc ‖ι‖₊ * ‖u‖₊ * 1 ≤ ‖ι‖₊ * 1 * 1 := by gcongr
      _ = ‖ι‖₊ := by simp
  have hB := HRS.MC.SEdge.B9.sed_B9_B_window_proof hd hs0 hs hγ hρ hφ hv (ψ := Ψ)
    (s7d_Psi1_memCb hf ι u)
  have hB' := hB.comp (tendsto_add_atTop_nat 1)
  have hcongr : ∀ m : ℕ, ∫ x, h x * Ψ x.2 ∂(μ m) =
      ∫ X, sed_B d s ρ γ v X * Ψ (centeredStat (sed_Q d s (m + 1) γ ρ) φ X) ∂(sed_Q d s (m + 1) γ ρ) := by
    intro m
    have hc : Continuous fun x : ℝ × EuclideanSpace ℝ (Fin p) => h x * Ψ x.2 :=
      h.continuous.mul (hΨc.comp continuous_snd)
    rw [integral_map (hpm m).aemeasurable hc.aestronglyMeasurable]
    rfl
  have hB'' : Tendsto (fun m : ℕ => ∫ x, h x * Ψ x.2 ∂(μ m)) atTop (𝓝 _) :=
    hB'.congr fun m => (hcongr m).symm
  have key := hn₀ n hn (fun x => Ψ x.2) hb hl _ hB''
  rw [hcongr n] at key
  have hi2 : ∀ b c : Fin p, ∫ z, iteratedFDeriv ℝ 2 Ψ z ![stdVec b, stdVec c]
        ∂(multivariateGaussian 0 (sed_Cmat d s γ ρ φ)) =
      ∫ z, iteratedFDeriv ℝ 3 f (ι z) ![u, s7_eps r (κ b), s7_eps r (κ c)]
        ∂(multivariateGaussian 0 (sed_Cmat d s γ ρ φ)) := by
    intro b c
    refine integral_congr_ae (Filter.Eventually.of_forall fun z => ?_)
    show iteratedFDeriv ℝ 2 (s7d_Psi1 f ι u) z ![stdVec b, stdVec c] = _
    rw [s7d_Psi1_iter2 (hf.1.of_le (by norm_num)) ι u z,
      show ι (stdVec b) = s7_eps r (κ b) from HRS.MC.Sec7.S7c.s7c_iota_std r κ b,
      show ι (stdVec c) = s7_eps r (κ c) from HRS.MC.Sec7.S7c.s7c_iota_std r κ c]
  simp only [hi2] at key
  exact key

end HRS.MC.Sec7.S7d

end
