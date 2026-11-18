import HRS.MC.E213R3

/-!
# Packet e213r, part 4: existence of the future Gaussians along a smooth positive trajectory

For `htr : IsSmoothPositiveTrajectory`, `m > d/2 + 2`, `T > 0`: there is `γ : ℝ → Measure (PathSpace d m T)` with
`IsFutureGaussian htr.dyn ρ m T u (γ u)` for every `u ∈ [0,T]`.  `γ u` is the law of the window of the stochastic convolution
`Γ_u = ∫_0^· Vev(·,σ) dG^u(σ)` of the shifted global Gaussian martingale `G^u = G(τ ∨ u) - G(u)` (part 1), whose
finite-dimensional laws and covariance are those of part 2/3, and path-level Gaussianity is `gaussian_window_of_fdd`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.E213R

open HRS HRS.Sec7 HRS.Uniform HRS.Uniform.Q54c HRS.GF HRS.T25P HRS.AdjK HRS.MC.E213Q

variable {d : ℕ} {s β : ℝ} {V ρ₀ : Torus d → ℝ} {ρ : ℝ → Torus d → ℝ}

theorem e213r_future_exists_traj (hd : 2 ≤ d) (htr : IsSmoothPositiveTrajectory d s β V ρ₀ ρ) {m : ℝ}
    (hm : (d : ℝ) / 2 + 2 < m) {T : ℝ} (hT : 0 < T) :
    ∃ γ : ℝ → Measure (PathSpace d m T), ∀ u ∈ Set.Icc (0 : ℝ) T, IsFutureGaussian htr.dyn ρ m T u (γ u) := by
  classical
  obtain ⟨Cr, cr, hCr, hcr, VA, hdualA, -, hdecA, -⟩ := adjk_evolution_along_trajectory hd htr m
  obtain ⟨Vev, hdual, hplain, hB1⟩ := adjk_evolution_moment_proof hd htr m 2 le_rfl
  have hKb : ∀ r t : ℝ, 0 ≤ r → r ≤ t → ‖Vev t r‖ ≤ Cr := by
    intro r t hr hrt
    rw [t25p_dual_unique hdual hdualA hr hrt]
    refine (hdecA r t hr hrt).trans ?_
    have h1 : Real.exp (-cr * (t - r)) ≤ 1 := by
      rw [Real.exp_le_one_iff]
      nlinarith [sub_nonneg.2 hrt]
    nlinarith
  obtain ⟨Ωg, mΩg, Pg, hPg, ℱ, G, hGc, hGz, hmart⟩ :=
    HRS.MC.E213K.exists_gaussian_martingale_top (HRS.MC.E213N.noiseDens m β⁻¹ ρ)
      (HRS.MC.E213K.e213k_isDetCovDensity_global_traj hd htr hm)
  haveI := hPg
  obtain ⟨C, hC0, hC⟩ := hB1 T hT
  have key : ∀ u ∈ Set.Icc (0 : ℝ) T, ∃ μ : Measure (PathSpace d m T),
      IsFutureGaussian htr.dyn ρ m T u μ := by
    intro u hu
    have hG : IsHilbertMartingaleWithCovariation Pg ℱ T G (fun r _ => HRS.MC.E213N.noiseDens m β⁻¹ ρ r) :=
      hmart T hT.le
    have hGu := e213r_shift_hmc hu.1 hu.2 hG
    set Gu : ℝ → Ωg → NegSobolev d m := fun τ ω => G (Kot.clampI u T τ) ω - G u ω with hGu_def
    set Cd := e213rCd m β⁻¹ ρ u T with hCd
    have hGu' : IsHilbertMartingaleWithCovariation Pg (augFiltration Pg ℱ) T Gu (fun r _ => Cd r) := hGu
    have hGuc : ∀ ω, Continuous fun τ => Gu τ ω := fun ω =>
      ((hGc ω).comp (Kot.continuous_clampI u T)).sub continuous_const
    have hGuz : ∀ ω, Gu 0 ω = 0 := fun ω => by
      simp only [hGu_def]
      rw [Kot.clampI_of_le_left hu.1, sub_self]
    have hGu0 : IsHilbertMartingaleWithCovariation Pg (augFiltration Pg ℱ) (0 + T) Gu (fun r _ => Cd r) := by
      rw [zero_add]; exact hGu'
    obtain ⟨Z, hZS, hZc, hZm, -⟩ := hC Ωg Pg (augFiltration Pg ℱ) 0 T le_rfl hT le_rfl Gu
      (fun r _ => Cd r) hGu0
    simp only [zero_add] at hZS hZc hZm
    obtain ⟨Zm, hZmm, hZmc, hZmae⟩ := HRS.ThermLin.thermlin_measurable_version hT.le Z hZm hZc
    have hZmS : ∀ t ∈ Set.Icc (0 : ℝ) T,
        IsStochConv Pg Vev (ContinuousLinearMap.id ℝ (NegSobolev d m)) Gu 0 t (Zm t) := fun t ht =>
      HRS.ThermLin.thermlin_isStochConv_congr (hZS t ht) (hZmae t ht)
    obtain ⟨hfdd, hcov⟩ := e213r_conv_fdd_cov hCr.le hT Vev (hplain T hT.le).2.2
      (fun r t hr hrt _ => hKb r t hr hrt) Pg Gu Cd hGu' hGuc hGuz Zm hZmS hZmm
    have hfdd0 : FddGaussian Pg Zm (Set.Icc 0 (0 + T)) := by rw [zero_add]; exact hfdd
    have hcont0 : ∀ᵐ ω ∂Pg, ContinuousOn (fun t => Zm t ω) (Set.Icc 0 (0 + T)) := by
      rw [zero_add]; exact hZmc
    obtain ⟨hWm, hWg⟩ := gaussian_window_of_fdd T hT Pg Zm 0 le_rfl hZmm hcont0 hfdd0
    refine ⟨law Pg (procWin m T 0 Zm), hWg, ?_⟩
    intro ta tb φa φb hφa hφb hta htb
    have hfc : Continuous fun z : PathSpace d m T =>
        NegSobolev.eval (pathAt z ta) φa * NegSobolev.eval (pathAt z tb) φb :=
      (HRS.MC.Sec7.S7PIS2.S7PIS2_obsFun m T hta hφa).continuous.mul
        (HRS.MC.Sec7.S7PIS2.S7PIS2_obsFun m T htb hφb).continuous
    have h1 : ∫ z, NegSobolev.eval (pathAt z ta) φa * NegSobolev.eval (pathAt z tb) φb
        ∂(law Pg (procWin m T 0 Zm)) =
        ∫ ω, NegSobolev.eval (pathAt (procWin m T 0 Zm ω) ta) φa *
          NegSobolev.eval (pathAt (procWin m T 0 Zm ω) tb) φb ∂Pg :=
      integral_map hWm hfc.aestronglyMeasurable
    have h2 : ∫ ω, NegSobolev.eval (pathAt (procWin m T 0 Zm ω) ta) φa *
          NegSobolev.eval (pathAt (procWin m T 0 Zm ω) tb) φb ∂Pg =
        ∫ ω, NegSobolev.eval (Zm ta ω) φa * NegSobolev.eval (Zm tb ω) φb ∂Pg := by
      refine integral_congr_ae ?_
      filter_upwards [hcont0] with ω hω
      have hat : ∀ t ∈ Set.Icc (0 : ℝ) T, pathAt (procWin m T 0 Zm ω) t = Zm t ω := by
        intro t ht
        unfold pathAt
        rw [dif_pos ht]
        have := e213q_procWin_at (Z := Zm) T 0 le_rfl ω hω ⟨t, ht⟩
        simpa using this
      simp only [hat ta hta, hat tb htb]
    rw [h1, h2, hcov ta tb φa φb hφa hφb hta htb]
    have hi : htr.dyn.invβ = β⁻¹ := rfl
    rw [hi]
    exact e213r_cov_integral hd htr hm hu.1 hdual hCr.le hKb hta htb hφa hφb
  refine ⟨fun u => if h : u ∈ Set.Icc (0 : ℝ) T then (key u h).choose else 0, fun u hu => ?_⟩
  simp only [dif_pos hu]
  exact (key u hu).choose_spec

end HRS.MC.E213R
