import HRS.MC.E214E5
import HRS.MC.E214G4
import HRS.MC.L2C6a
import HRS.MC.L2C6b
import HRS.Equilibrium.FieldSingAux

/-!
# E214G5: the coupled pair with the weighted coordinate-increment bound

`exists_coupled_pair_inc_proof`: a copy of the construction `HRS.MC.E214E.exists_coupled_pair_proof` (the pair
`η = V(·,0) Y₀ + Z∘π`, `ηs = V'(·,0) Ys₀ + Z'∘π` on `((ν ⊗ νs) ⊗ P_G)`), re-exposing the intermediate facts
(dual evolutions, global noises) to prove, for that pair,
`E (ξ_k(t)-ξ_k(s))² ≤ B |t-s|^{1/2} ⟨k⟩^{-r}` (`|t-s| ≤ 1`), `ξ_k = coord_k(η - ηs)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MC.E214G

open HRS HRS.Sec7 HRS.Uniform HRS.GF HRS.T25P HRS.AdjK HRS.MC.E213N HRS.MC.E214D HRS.MC.E214E

variable {d : ℕ}

set_option maxHeartbeats 4000000 in
theorem exists_coupled_pair_inc_proof (R : Regime d) (r : ℝ) (hr : r = 2 * (d : ℝ) + 6) :
    ∃ (Ω : Type) (_ : MeasurableSpace Ω) (P : Measure Ω) (_ : IsProbabilityMeasure P)
      (Y₀ Ys₀ : Ω → NegSobolev d r) (η ηs : ℝ → Ω → NegSobolev d r),
      IsCoupledPair R r P Y₀ Ys₀ η ηs ∧
      ∃ B : ℝ, 0 < B ∧ ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → |t - s| ≤ 1 → ∀ k : NonzeroLattice d,
        ∫ ω, (NegSobolev.coord (η t ω - ηs t ω) k - NegSobolev.coord (η s ω - ηs s ω) k) ^ 2 ∂P ≤
          B * |t - s| ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r) := by
  set S := HRS.MC.Sec7.FCPlan.s7fcPrep R with hS
  have htr : IsSmoothPositiveTrajectory d S.s S.β S.V S.ρ0 S.ρ :=
    HRS.MC.E213A.isSmoothPositiveTrajectory_of_prepared S
  have htr' := stationary_traj R
  have hdyn : htr.dyn = R.D := HRS.MC.Sec7.S7FCW4.S7FCW4_dyn R
  have hdyn' : htr'.dyn = R.D := stationary_traj_dyn R
  have hρS : ∀ s : ℝ, 0 ≤ s → S.ρ s = R.ρ s := fun s hs => HRS.MC.Sec7.S7FCW4.S7FCW4_rho_eq R hs
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hm : (d : ℝ) / 2 + 2 < r := by rw [hr]; linarith
  have hq : (0 : ℝ) ≤ R.β⁻¹ := inv_nonneg.2 R.hβ.le
  have hβ₀ : 0 ≤ R.β₀ := by
    rcases R.hβ₀ with h | ⟨-, h⟩
    · exact h.le
    · exact h.ge
  -- initial laws
  obtain ⟨ν, hνp, hνg⟩ := HRS.Main.preparedGaussian_exists_proof S R.β₀ hβ₀ r (by linarith)
  haveI := hνp
  have hνcov : IsCenteredGaussianWithCov r ν
      (susceptibilityCov (periodicRiesz d R.D.s) (withDensityReal R.ρ₀) R.β₀) := by
    refine ⟨hνg.1, fun φ ψ hφ hψ => ?_⟩
    rw [hνg.2 φ ψ hφ hψ]
    exact HRS.MC.E213L.e213l_preparedCov_eq_susceptibilityCov_density R.hρ₀ R.D.s R.β₀ hφ hψ
  obtain ⟨νs, hνsp, hνscov, -⟩ := HRS.ThermLin.Plan2.tl2_xi_law_proof S R.thermal.1 r (by linarith)
  haveI := hνsp
  -- the pair of noises
  obtain ⟨Ωg, mΩ, Pg, hPg, ℱ, Gp, hGc, hGz, hGp, hG1, hG2⟩ := e214d_pair_components R.hd htr htr' hm hq
  haveI := hPg
  obtain ⟨Cr, Vev, Zs, hCr, hdual, hplain, hKb, hN1⟩ := e214d_global_conv R.hd htr hm
    (G := fun τ ω => (Gp τ ω).fst)
    (fun ω => (WithLp.fstL 2 ℝ (NegSobolev d r) (NegSobolev d r)).continuous.comp (hGc ω))
    (fun ω => by simp [hGz ω]) (fun S' hS' => hG1 S' hS')
  obtain ⟨Cr', Vev', Zs', hCr', hdual', hplain', hKb', hN2⟩ := e214d_global_conv R.hd htr' hm
    (G := fun τ ω => (Gp τ ω).snd)
    (fun ω => (WithLp.sndL 2 ℝ (NegSobolev d r) (NegSobolev d r)).continuous.comp (hGc ω))
    (fun ω => by simp [hGz ω]) (fun S' hS' => hG2 S' hS')
  -- dual evolutions for `R`
  have hdualR : IsDualEvolution R.D R.ρ r Vev := by
    intro u t hu hut z φ hφ
    have := hdual u t hu hut z φ hφ
    rw [this, hdyn]
    congr 1
    exact HRS.MC.Sec7.S7FCW4.S7FCW4_propagator_congr R.D S.ρ R.ρ hρS u t φ
  have hdualR' : IsDualEvolution R.D (fun _ => R.ρβ) r Vev' := by
    intro u t hu hut z φ hφ
    have := hdual' u t hu hut z φ hφ
    rwa [hdyn'] at this
  -- the product space
  have hmap1 : ((ν.prod νs).prod Pg).map (fun ω => ω.1.1) = ν := by
    have : (fun ω : (NegSobolev d r × NegSobolev d r) × Ωg => ω.1.1) = Prod.fst ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map measurable_fst measurable_fst, Measure.map_fst_prod, measure_univ,
      one_smul, Measure.map_fst_prod, measure_univ, one_smul]
  have hmap2 : ((ν.prod νs).prod Pg).map (fun ω => ω.1.2) = νs := by
    have : (fun ω : (NegSobolev d r × NegSobolev d r) × Ωg => ω.1.2) = Prod.snd ∘ Prod.fst := rfl
    rw [this, ← Measure.map_map measurable_snd measurable_fst, Measure.map_fst_prod, measure_univ,
      one_smul, Measure.map_snd_prod, measure_univ, one_smul]
  have hmapπ1 : ((ν.prod νs).prod Pg).map (fun ω => (ω.1.1, ω.2)) = ν.prod Pg := by
    have : (fun ω : (NegSobolev d r × NegSobolev d r) × Ωg => (ω.1.1, ω.2)) = Prod.map Prod.fst id := rfl
    rw [this, ← Measure.map_prod_map _ _ measurable_fst measurable_id, Measure.map_fst_prod, measure_univ,
      one_smul, Measure.map_id]
  have hmapπ2 : ((ν.prod νs).prod Pg).map (fun ω => (ω.1.2, ω.2)) = νs.prod Pg := by
    have : (fun ω : (NegSobolev d r × NegSobolev d r) × Ωg => (ω.1.2, ω.2)) = Prod.map Prod.snd id := rfl
    rw [this, ← Measure.map_prod_map _ _ measurable_snd measurable_id, Measure.map_snd_prod, measure_univ,
      one_smul, Measure.map_id]
  have hpair : IsCoupledPair R r ((ν.prod νs).prod Pg) (fun ω => ω.1.1) (fun ω => ω.1.2)
      (fun t ω => Vev t 0 ω.1.1 + Zs t ω.2) (fun t ω => Vev' t 0 ω.1.2 + Zs' t ω.2) := by
    refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
    · rw [hmap1]; exact hνcov
    · rw [hmap2]; exact hνscov
    · have h := indepFun_prod (μ := ν) (ν := νs) (X := (id : NegSobolev d r → NegSobolev d r))
        (Y := (id : NegSobolev d r → NegSobolev d r)) measurable_id measurable_id
      have hm' : ((ν.prod νs).prod Pg).map Prod.fst = ν.prod νs := by
        rw [Measure.map_fst_prod, measure_univ, one_smul]
      exact indepFun_comp_of_map Prod.fst measurable_fst hm' (f := Prod.fst) (g := Prod.snd)
        measurable_fst.aemeasurable measurable_snd.aemeasurable h
    · intro T
      have h := e213n_linearSolution R.hd htr hm hCr hdual hplain hKb hN1 ν T
      rw [hdyn] at h
      have h' := e213n_linSol_congr R.D hρS R.hDβ.symm h
      exact linSol_comp (fun ω : (NegSobolev d r × NegSobolev d r) × Ωg => (ω.1.1, ω.2))
        ((measurable_fst.comp measurable_fst).prodMk measurable_snd) hmapπ1 measurable_fst
        (fun p ts φ hts hφ => noisePart_meas' hdualR hN1.meas p ts φ (fun a => (hts a).1) hφ) h'
    · intro T
      have h := e213n_linearSolution R.hd htr' hm hCr' hdual' hplain' hKb' hN2 νs T
      rw [hdyn', ← R.hDβ] at h
      exact linSol_comp (fun ω : (NegSobolev d r × NegSobolev d r) × Ωg => (ω.1.2, ω.2))
        ((measurable_snd.comp measurable_fst).prodMk measurable_snd) hmapπ2 measurable_fst
        (fun p ts φ hts hφ => noisePart_meas' hdualR' hN2.meas p ts φ (fun a => (hts a).1) hφ) h
    · intro p p' ts φ ts' ψ hts hts' hφ hψ
      intro G
      have hφmem : ∀ a, MemSobolev r (φ a) := fun a => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hφ a) r
      have hψmem : ∀ b, MemSobolev r (ψ b) := fun b => HRS.PDE.MFSemigroup.memSobolev_of_isSmooth (hψ b) r
      set Gz : Ωg → EuclideanSpace ℝ (Fin p ⊕ Fin p') := fun ω => WithLp.toLp 2 (Sum.elim
        (fun a => NegSobolev.eval (Zs (ts a) ω) (φ a)) (fun b => NegSobolev.eval (Zs' (ts' b) ω) (ψ b)))
        with hGz'
      have hGeq : G = fun ω => Gz ω.2 := by
        funext ω
        ext j
        rcases j with a | b
        · show NegSobolev.eval (Vev (ts a) 0 ω.1.1 + Zs (ts a) ω.2) (φ a) -
            NegSobolev.eval ω.1.1 (propagator R.D R.ρ 0 (ts a) (φ a)) = NegSobolev.eval (Zs (ts a) ω.2) (φ a)
          rw [HRS.A33.a33_eval_add_left _ _ (HRS.A33.a33_ws_smooth r (hφ a)),
            hdualR 0 (ts a) le_rfl (hts a) ω.1.1 (φ a) (hφ a)]
          ring
        · show NegSobolev.eval (Vev' (ts' b) 0 ω.1.2 + Zs' (ts' b) ω.2) (ψ b) -
            NegSobolev.eval ω.1.2 (propagator R.D (fun _ => R.ρβ) 0 (ts' b) (ψ b)) =
              NegSobolev.eval (Zs' (ts' b) ω.2) (ψ b)
          rw [HRS.A33.a33_eval_add_left _ _ (HRS.A33.a33_ws_smooth r (hψ b)),
            hdualR' 0 (ts' b) le_rfl (hts' b) ω.1.2 (ψ b) (hψ b)]
          ring
      have hGzm : Measurable Gz := by
        refine measurable_toLp_sum fun s => ?_
        rcases s with a | b
        · exact (HRS.Uniform.Q54c.continuous_eval_const (hφmem a)).measurable.comp (hN1.meas _)
        · exact (HRS.Uniform.Q54c.continuous_eval_const (hψmem b)).measurable.comp (hN2.meas _)
      refine ⟨?_, ?_⟩
      · rw [hGeq]
        exact indepFun_prod (μ := ν.prod νs) (ν := Pg) (X := id) (Y := Gz) measurable_id hGzm
      · have hlaw : law ((ν.prod νs).prod Pg) G = Pg.map Gz := by
          rw [hGeq]
          show ((ν.prod νs).prod Pg).map (Gz ∘ Prod.snd) = Pg.map Gz
          rw [← Measure.map_map hGzm measurable_snd, Measure.map_snd_prod, measure_univ, one_smul]
        rw [hlaw]
        have hCm : 0 ≤ max Cr Cr' := le_max_of_le_left hCr
        have hmain := pair_noise_gaussian R.hd htr htr' hm hq hdyn hdyn' hGc hGz hGp hCm hdual hdual'
          hplain hplain' (fun u t hu hut => (hKb u t hu hut).trans (le_max_left _ _))
          (fun u t hu hut => (hKb' u t hu hut).trans (le_max_right _ _)) hN1.meas hN2.meas
          (fun t ht => hN1.conv t ht) (fun t ht => hN2.conv t ht) ts φ ts' ψ hts hts' hφ hψ
        rw [hmain, R.hDβ]
        congr 1
        ext i j
        rcases i with a | a <;> rcases j with b | b <;> simp only [Matrix.of_apply]
        · exact crossNoiseCov_congr R.D _ hρS hρS _ _ _ _
        · exact crossNoiseCov_congr R.D _ hρS (fun _ _ => rfl) _ _ _ _
        · exact crossNoiseCov_congr R.D _ (fun _ _ => rfl) hρS _ _ _ _
  refine ⟨(NegSobolev d r × NegSobolev d r) × Ωg, inferInstance, (ν.prod νs).prod Pg, inferInstance,
    fun ω => ω.1.1, fun ω => ω.1.2, fun t ω => Vev t 0 ω.1.1 + Zs t ω.2,
    fun t ω => Vev' t 0 ω.1.2 + Zs' t ω.2, hpair, ?_⟩
  -- the increments
  have hsm : ∀ k : NonzeroLattice d, Torus.IsSmooth (Torus.realMode k) := fun k =>
    HRS.FieldSingAux.isSmooth_realMode k
  obtain ⟨Ca, Ha⟩ := HRS.MC.L2C6a.l2c6a_proof R r hr
  obtain ⟨Cb, Hb⟩ := HRS.MC.L2C6b.l2c6b_proof R r hr
  obtain ⟨hY, hYs, -, hη, hηs, -⟩ := hpair
  set Pf : Measure ((NegSobolev d r × NegSobolev d r) × Ωg) := (ν.prod νs).prod Pg with hPf
  have hmapsnd : Pf.map Prod.snd = Pg := by
    rw [hPf, Measure.map_snd_prod, measure_univ, one_smul]
  have hmη : ∀ t, Measurable (fun ω : (NegSobolev d r × NegSobolev d r) × Ωg => Vev t 0 ω.1.1 + Zs t ω.2) :=
    fun t => ((Vev t 0).continuous.measurable.comp (measurable_fst.comp measurable_fst)).add
      ((hN1.meas t).comp measurable_snd)
  have hmηs : ∀ t, Measurable (fun ω : (NegSobolev d r × NegSobolev d r) × Ωg => Vev' t 0 ω.1.2 + Zs' t ω.2) :=
    fun t => ((Vev' t 0).continuous.measurable.comp (measurable_snd.comp measurable_fst)).add
      ((hN2.meas t).comp measurable_snd)
  have hCa : 0 ≤ max Ca 0 := le_max_right _ _
  have hCb : 0 ≤ max Cb 0 := le_max_right _ _
  have hc1 : ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
      ∫⁻ ω, ENNReal.ofReal (NegSobolev.coord (Vev t 0 ω.1.1 + Zs t ω.2) k ^ 2) ∂Pf ≤
        ENNReal.ofReal (max Ca 0 * Lattice.jp k.1 ^ (-(2 * r))) := fun t ht k => by
    obtain ⟨hmem, hb⟩ := Ha Pf (fun ω => ω.1.1) (fun t ω => Vev t 0 ω.1.1 + Zs t ω.2) hY hη t ht
      (Torus.realMode k) (hsm k)
    rw [HRS.MC.E214F.l2NormSq_realMode, mul_one] at hb
    exact lint_coord_sq_le Pf _ k hmem (hb.trans (le_max_left _ _))
  have hc2 : ∀ t : ℝ, 0 ≤ t → ∀ k : NonzeroLattice d,
      ∫⁻ ω, ENNReal.ofReal (NegSobolev.coord (Vev' t 0 ω.1.2 + Zs' t ω.2) k ^ 2) ∂Pf ≤
        ENNReal.ofReal (max Cb 0 * Lattice.jp k.1 ^ (-(2 * r))) := fun t ht k => by
    obtain ⟨hmem, hb⟩ := Hb Pf (fun ω => ω.1.2) (fun t ω => Vev' t 0 ω.1.2 + Zs' t ω.2) hYs hηs t ht
      (Torus.realMode k) (hsm k)
    rw [HRS.MC.E214F.l2NormSq_realMode, mul_one] at hb
    exact lint_coord_sq_le Pf _ k hmem (hb.trans (le_max_left _ _))
  set j : ℕ := d + 2 with hjdef
  have hj : (d : ℝ) + 2 ≤ j := by simp [hjdef]
  have hjm : (j : ℝ) + 2 ≤ r := by
    rw [hr, hjdef]; push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hj2 : (d : ℝ) < 2 * (j : ℝ) := by
    rw [hjdef]; push_cast
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  set Sj : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * (j : ℝ))) with hSj
  have hSj0 : 0 ≤ Sj := tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
  obtain ⟨B₁, B₂, hB₁, hB₂, Hinc⟩ := field_increment R.hd htr j hj hjm
  obtain ⟨B₁', B₂', hB₁', hB₂', Hinc'⟩ := field_increment R.hd htr' j hj hjm
  have i1 := Hinc Vev hdual hplain Pg ℱ _ Zs hN1 Pf Prod.snd measurable_snd hmapsnd (fun ω => ω.1.1)
    (measurable_fst.comp measurable_fst) (max Ca 0 * Sj) (mul_nonneg hCa hSj0)
    (fun t ht => energy_of_coord hCa hj2 Pf _ (hmη t) (hc1 t ht))
  have i2 := Hinc' Vev' hdual' hplain' Pg ℱ _ Zs' hN2 Pf Prod.snd measurable_snd hmapsnd (fun ω => ω.1.2)
    (measurable_snd.comp measurable_fst) (max Cb 0 * Sj) (mul_nonneg hCb hSj0)
    (fun t ht => energy_of_coord hCb hj2 Pf _ (hmηs t) (hc2 t ht))
  have k1 := coord_incr_of_inputs hCa (add_nonneg (mul_nonneg hB₁ (mul_nonneg hCa hSj0)) hB₂) Pf _ hmη hc1 i1
  have k2 := coord_incr_of_inputs hCb (add_nonneg (mul_nonneg hB₁' (mul_nonneg hCb hSj0)) hB₂') Pf _ hmηs hc2 i2
  refine ⟨Real.sqrt ((B₁ * (max Ca 0 * Sj) + B₂) * (4 * max Ca 0)) * 2 +
      Real.sqrt ((B₁' * (max Cb 0 * Sj) + B₂') * (4 * max Cb 0)) * 2 + 1, by positivity, ?_⟩
  intro s t hs ht hst k
  have := pair_inc_of_fields (Real.sqrt_nonneg _) (Real.sqrt_nonneg _) Pf _ _ hmη hmηs k1 k2 s t hs ht hst k
  refine this.trans ?_
  have hw : 0 ≤ |t - s| ^ (1 / 2 : ℝ) * Lattice.jp k.1 ^ (-r) :=
    mul_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (Real.rpow_nonneg (Torus.jp_pos k.1).le _)
  rw [mul_assoc, mul_assoc]
  refine mul_le_mul_of_nonneg_right ?_ hw
  nlinarith [Real.sqrt_nonneg ((B₁ * (max Ca 0 * Sj) + B₂) * (4 * max Ca 0)),
    Real.sqrt_nonneg ((B₁' * (max Cb 0 * Sj) + B₂') * (4 * max Cb 0))]

end HRS.MC.E214G

end
