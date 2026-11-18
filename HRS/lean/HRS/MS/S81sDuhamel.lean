import HRS.MS.S81sRecent
import HRS.MS.CritForceIntegrability
import HRS.MS.WsStatAux35
import HRS.MS.WsStatAux22
import HRS.MS.WsStatAux13
import HRS.MS.GenPathAux33
import HRS.MS.GenPathAux22

/-!
# S8.1 (worker S81S): the physical Duhamel identity on the original space, at an arbitrary oscillator index

Namespace `HRS.Whole.S81S`, prefix `s81s_`.

`s81s_duhamel`: for a canonical realization `(P, X₀, W, X)` with its filtered form `(ℱ, W')`, a window start `u ≥ 0`, a horizon `T > 0` and
ANY `m ≥ wholeSpaceIndex d`, there is a measurable `B_m`-valued process `Fz` such that for `t ∈ [0,T]` and every coordinate `α`, almost surely
* `Fz(t)_α = ∫_0^{u+t} (√N/2) (c_α(u+t, r) - E c_α(u+t, r)) dr` (the centered forcing of `weighted_critical_forcing`);
* `ζ_N(u+t)_α = I_α + (∫_0^{u+t} √(2/(Nβ)) ∂_a U_{u+t-r}φ_α(X_i(r)) dW)_α - Fz(t)_α`, with `I_α = √N(μ_N(X₀)(U_{u+t}φ_α) - m_N(U_{u+t}φ_α))`
  (Duhamel: initial term, Itô integral, forcing).
It is the identity of S21 (`s56_mild_coord`, `s21_centered_coord`) transported to the index `m` by the re-based setup `s81s_setup`.
-/

set_option autoImplicit false
set_option maxRecDepth 4000
set_option synthInstance.maxHeartbeats 400000

noncomputable section

open MeasureTheory ProbabilityTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators
open HRS HRS.Whole HRS.MS.GenPath HRS.MS.S21 HRS.MS.S82BD

namespace HRS.Whole.S81S

variable {d : ℕ}

theorem s81s_memCb_at {C : WholeCoeff d} {t : ℝ} {φ : Euc d → ℝ} {u : ℝ → Euc d → ℝ}
    (hu : IsClassicalAdjointW C t φ u) {r : ℝ} (hr : r ∈ Set.Icc (0 : ℝ) t) : MemCb 2 (u r) := by
  refine ⟨hu.c2 r hr, fun j hj => ?_⟩
  obtain ⟨B, hB⟩ := hu.bdd j hj
  exact ⟨B, by rintro _ ⟨x, rfl⟩; exact hB r hr x⟩

/-- The coordinates of `s56k0` along the orbit family (any `m`). -/
theorem s81s_k0_coord {C : WholeCoeff d} {m T : ℝ} (hC : OscAdjointInput C m T) (σ : ℝ)
    (hmeas : ∀ a : Fin d, Measurable fun z : Euc d => gradFeature C m T a 0 z)
    {Bf : ℝ} (hBf : 0 ≤ Bf) (hbd : ∀ (a : Fin d) (z : Euc d), ‖gradFeature C m T a 0 z‖ ≤ Bf)
    (hcb : ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) T, MemCb 2 (propagatorW C 0 t (oscTestFun m α)))
    (ν μ' : Measure (Euc d)) [IsProbabilityMeasure ν] [IsProbabilityMeasure μ']
    (hν : Integrable (fun x : Euc d => ‖x‖) ν) (hμ : Integrable (fun x : Euc d => ‖x‖) μ')
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T) (α : MultiIndex d) :
    OscDual.coord ((s56k0 C m T σ ν μ').evalA t) α =
      σ * (HRS.Whole.pair ν (propagatorW C 0 t (oscTestFun m α)) -
        HRS.Whole.pair μ' (propagatorW C 0 t (oscTestFun m α))) := by
  have hT : 0 ≤ T := ht.1.trans ht.2
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) T := ⟨le_rfl, hT⟩
  obtain ⟨hcd, hbdd⟩ := hcb α t ht
  obtain ⟨B, hB⟩ := hbdd 0 (Nat.zero_le _)
  have hh : ContDiff ℝ 1 (propagatorW C 0 t (oscTestFun m α)) := hcd.of_le (by norm_num)
  rw [HRS.MS.S52.s52_coord_evalA ht.1 ht.2]
  rw [s56_k0_inner C m T σ Bf hBf hmeas hbd ν μ' hν hμ (HRS.MS.S52.s52y1 m T t α)
    (propagatorW C 0 t (oscTestFun m α)) hh B
    (fun z => by
      have h1 : ‖iteratedFDeriv ℝ 0 (propagatorW C 0 t (oscTestFun m α)) z‖ ≤ B := hB ⟨z, rfl⟩
      rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at h1)
    (fun a z => by
      rw [HRS.MS.S52.s52_pair_grad_y1 hC ht.2 a h0 z α]
      simp [ht.1])]
  rfl

theorem s81s_duhamel (hd : 2 ≤ d) {a β : ℝ} (ha : 0 < a) (hβ : 0 < β) (m : ℝ)
    (hm : (wholeSpaceIndex d : ℝ) ≤ m) (T : ℝ) (hT : 0 < T) {ρβ : Euc d → ℝ}
    (hρβ : IsThermalEquilibrium d ((d : ℝ) / 2) a β ρβ) {N : ℕ} (hN : 2 ≤ N)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    (X₀ : Ω → EucConfig d N) (W : ℝ≥0 → Ω → (Fin N → Euc d)) (X : ℝ≥0 → Ω → EucConfig d N)
    (hR : IsCanonicalRealization d ((d : ℝ) / 2) a β N P X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    {u : ℝ} (hu : 0 ≤ u) :
    ∃ Fz : ℝ → Ω → OscDual d m, (∀ t, Measurable (Fz t)) ∧
      ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ α : MultiIndex d,
        (∀ᵐ ζ ∂P, OscDual.coord (Fz t ζ) α = ∫ r in Set.Icc (0 : ℝ) (u + t),
            (Real.sqrt N / 2) * (commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m
                (HRS.Whole.withDensityReal ρβ) X α (u + t) r ζ -
              ∫ ζ', commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m
                (HRS.Whole.withDensityReal ρβ) X α (u + t) r ζ' ∂P)) ∧
        (∀ᵐ ζ ∂P, OscDual.coord (zetaB m (P.map (X (Real.toNNReal (u + t)))) (X (Real.toNNReal (u + t)) ζ)) α =
          Real.sqrt N * (HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ))
              (propagatorW (critCoeff d a β ρβ) 0 (u + t) (oscTestFun m α)) -
            ∫ x, propagatorW (critCoeff d a β ρβ) 0 (u + t) (oscTestFun m α) x
              ∂(HRS.Whole.firstMarginal (law P (X 0)))) +
          itoIntegral P ℱ W' (fun r z (ia : Fin N × Fin d) =>
            if r ∈ Set.Icc (0 : ℝ) (u + t) then Real.sqrt (2 / (N * β)) *
              gradComp ia.2 (propagatorW (critCoeff d a β ρβ) r (u + t) (oscTestFun m α))
                (X (Real.toNNReal r) z ia.1) else 0) (u + t) ζ -
          OscDual.coord (Fz t ζ) α) := by
  classical
  have hd2 : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
  have hsd : (d : ℝ) / 2 < d := by linarith
  have hN1 : 1 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hL : 0 < u + T := by linarith
  obtain ⟨θ, Λ, K, C₀, S, hbv, hSρ, hSinv, hSκ, hScoeff, hSdyn, hSadj⟩ :=
    s81s_setup hd ha hβ hρβ hm hL
  let b : WholeBounds d := s81s_bounds d a β m (u + T) θ Λ K C₀
  have hσ := s21_sigma_eq b S hβ hSinv hN1 (hSκ N hN1)
  have hσ2 : S.σ N = Real.sqrt N * Real.sqrt β := by
    rw [hσ.1, Real.sqrt_mul (Nat.cast_nonneg N)]
  have hq1 : S.q N = 1 := hσ.2
  have hX : IsWholeStrongSolution P (S.dyn N) b.T X₀ W X := by
    rw [hSdyn N]; exact hR.solution (u + T)
  have hXm : ∀ t, Measurable (X t) := hX.adapted
  have hlaw : ∀ t : ℝ≥0, P.map (X t) =
      HRS.Whole.canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β :=
    fun t => HRS.Whole.S79.s79_law_X_eq hR t
  have hstat : ∀ t ∈ Set.Icc (0 : ℝ) b.T, P.map (X (Real.toNNReal t)) = P.map (X 0) :=
    fun t _ => (hlaw _).trans (hlaw 0).symm
  have hstat0 : ∀ t ∈ Set.Icc (0 : ℝ) (u + T), law P (X (Real.toNNReal t)) = law P (X 0) :=
    fun t _ => (hlaw _).trans (hlaw 0).symm
  haveI hP0 : IsProbabilityMeasure (P.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).2 inferInstance
  set νb : Measure (Euc d) := HRS.Whole.meanEmpirical (P.map (X 0)) with hνb
  haveI hνbp : IsProbabilityMeasure νb := HRS.Whole.meanEmpirical_isProbabilityMeasure _ hN1
  obtain ⟨M₂, hM₂0, hM₂ρ, hM₂mom⟩ := s21_second_moment_stationary hd hs0 hsd ha hβ
  have hν1 : Integrable (fun x : Euc d => ‖x‖) νb :=
    s21_meanEmp_norm_integrable hNpos P (X 0) (hXm 0)
      (lt_of_le_of_lt (hM₂mom N hN P (X 0) (hXm 0) (hlaw 0)) ENNReal.ofReal_lt_top)
  have hρS : IsSchwartzDensity ρβ := by
    rw [HRS.MS.Mov0.mv0_rho_eq hd hs0 hsd ha hβ hρβ]
    exact s21_schwartz_thermal hd hs0 hsd ha hβ
  obtain ⟨CA, hCA⟩ := s21_var_hyp hd hs0 hsd ha hβ
  have hvar0 : ∀ f : Euc d → ℝ, MemCb 2 f →
      (N : ℝ≥0∞) * evariance (fun ζ => centeredPairFunctional
        (commutatorKernel d ((d : ℝ) / 2) (fun x => gradient f x)) (X 0 ζ)
        (HRS.Whole.withDensityReal ρβ)) P ≤
      ENNReal.ofReal (CA * deltaN d ((d : ℝ) / 2) N * (⨆ x, ‖iteratedFDeriv ℝ 2 f x‖) ^ 2) :=
    fun f hf => hCA N hN P (X 0) (hXm 0) (hlaw 0) ρβ hρβ f hf
  obtain ⟨bO, KO, G0, G1, G2, hOrb⟩ := s82_orbit hd a β hβ m hm (u + T) hL.le hρS
  have hint : ∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      IntegrableOn (fun r => commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρβ) X α t r ζ)
        (Set.Icc 0 t) := by
    have h1 := (s82_horizon hd a β hβ m hm (u + T) hL.le hρS CA hN P X₀ W X hR.brownian
      (hR.solution (u + T)) hstat0 hvar0).1
    rw [hScoeff N]
    exact h1
  have hfub : ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      IntegrableOn (fun r => ∫ ζ, commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρβ) X α t r ζ ∂P)
          (Set.Icc 0 t) ∧
        ∫ ζ, (∫ r in Set.Icc (0 : ℝ) t,
            commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρβ) X α t r ζ) ∂P =
          ∫ r in Set.Icc (0 : ℝ) t, ∫ ζ, commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρβ) X α t r ζ ∂P ∧
        Integrable (fun ζ => ∫ r in Set.Icc (0 : ℝ) t,
          commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρβ) X α t r ζ) P := by
    intro α t ht
    rw [hScoeff N]
    exact HRS.MS.S53.s21_fubini_comm hd hs0 hsd m (u + T) hL.le hρS
      (quadraticGradientDyn d ((d : ℝ) / 2) a β) (critCoeff d a β ρβ) hOrb CA hN P X₀ W X
      (hR.solution (u + T)) hstat0 hvar0 α ht
  have hW : IsCylindricalBrownian P ℱ W' := HRS.GF.gfb3_isCylindricalBrownian_of_filtration hF.brownian
  have hΦ : ∀ τ : ℝ, IsHSIntegrand P ℱ τ (s56Phi (S.coeff N) m (u + T) (S.q N) X) := fun τ =>
    s56_phi_isHS b hbv S N (hSadj N) (S.q N) P ℱ X hF.progressive τ
  obtain ⟨ML, hML⟩ := s81s_exists_hito hW hΦ
  have hMLm : ∀ τ, Measurable (ML τ) := fun τ => (hML.adapted τ).mono (ℱ.le τ) le_rfl
  -- the initial term
  obtain ⟨B, hB0, hfd⟩ := HRS.MS.FinNoise.s86_feat_data hd a β ha hβ m hm (u + T) hL
  obtain ⟨hfeat, hbound⟩ := hfd ρβ hρβ
  have hmeasG : ∀ i : Fin d, Measurable fun z : Euc d => gradFeature (S.coeff N) m (u + T) i 0 z := fun i => by
    rw [hScoeff N]; exact (hfeat.cont i 0 ⟨le_rfl, hL.le⟩).measurable
  have hbdG : ∀ (i : Fin d) (z : Euc d), ‖gradFeature (S.coeff N) m (u + T) i 0 z‖ ≤ B := fun i z => by
    rw [hScoeff N]; simpa using hbound i 0 z
  have hcb : ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) (u + T),
      MemCb 2 (propagatorW (S.coeff N) 0 t (oscTestFun m α)) := fun α t ht =>
    s81s_memCb_at (s56_osc_classical b hbv S N ht α) (r := 0) ⟨le_rfl, ht.1⟩
  have hmean : HRS.Whole.meanEmpirical (P.map (X 0)) = HRS.Whole.firstMarginal (law P (X 0)) := by
    obtain ⟨Cs, -, hS⟩ := S45.s45_static_all hd hs0 hsd ha hβ
    have hSN := hS N hN
    haveI := hSN.prob
    have h0 : P.map (X 0) = HRS.Whole.canonicalGibbs (rieszKernel d ((d : ℝ) / 2)) (confinement a) N β := hlaw 0
    show HRS.Whole.meanEmpirical (P.map (X 0)) = HRS.Whole.firstMarginal (P.map (X 0))
    rw [h0]
    exact HRS.Whole.meanEmpirical_eq_firstMarginal _ hSN.exch hN1
  -- the processes
  refine ⟨fun t ζ => -((Real.sqrt β)⁻¹ • s21Rt S X νb ML (u + t) ζ), fun t => ?_, fun t ht α => ?_⟩
  · exact (((s21_Rt_meas b hbv S hN1 (hSadj N) X hXm νb hν1 ML hMLm (u + t)).const_smul
      (Real.sqrt β)⁻¹).neg)
  have ht' : u + t ∈ Set.Icc (0 : ℝ) b.T := ⟨by linarith [ht.1], by show u + t ≤ u + T; linarith [ht.2]⟩
  have hc := s21_centered_coord b hbv S hN (hSadj N) rfl (hSρ N) P hX ℱ W' hF ML hML hstat hν1 hfub hint ht' α
  have hid := s56_ident (S.coeff N) m (u + T) (S.q N) N P ℱ W' X ML hN1 hW hΦ hML (hSadj N) (u + t) ht' α
  rw [hScoeff N] at hc
  have hcl := s56_osc_classical b hbv S N ht' α
  have hprog := HRS.MH.DualityRd.isProgressiveL2_truncGrad_proof (P := P) ht'.1 hcl.isC12TestRd hF.progressive
  set c0 : ℝ := Real.sqrt (2 * S.q N / N) with hc0
  set c1 : ℝ := Real.sqrt (2 / (N * β)) with hc1
  have hc01 : c1 = (Real.sqrt β)⁻¹ * c0 := by
    have hNp : (0 : ℝ) < N := by exact_mod_cast hNpos
    have e1 : 2 / ((N : ℝ) * β) = (2 / N) * β⁻¹ := by field_simp
    have e2 : c0 = Real.sqrt (2 / N) := by rw [hc0, hq1]; norm_num
    rw [hc1, e1, Real.sqrt_mul (by positivity), Real.sqrt_inv, e2]
    ring
  have hsm0 := HRS.itoIntegral_smul hF.brownian hprog c0
  have hsm1 := HRS.itoIntegral_smul hF.brownian hprog c1
  have hk0 : (fun (r : ℝ) (z : Ω) (ia : Fin N × Fin d) => if r ∈ Set.Icc (0 : ℝ) (u + t) then c0 *
      gradComp ia.2 (propagatorW (S.coeff N) r (u + t) (oscTestFun m α)) (X (Real.toNNReal r) z ia.1) else 0) =
      fun s z => c0 • HRS.MH.DualityRd.truncGradIntegrand (u + t)
        (fun r => propagatorW (S.coeff N) r (u + t) (oscTestFun m α)) X s z := by
    funext r z ia
    by_cases hr : r ∈ Set.Icc (0 : ℝ) (u + t) <;> simp [HRS.MH.DualityRd.truncGradIntegrand, hr]
  have hk1 : (fun (r : ℝ) (z : Ω) (ia : Fin N × Fin d) => if r ∈ Set.Icc (0 : ℝ) (u + t) then c1 *
      gradComp ia.2 (propagatorW (S.coeff N) r (u + t) (oscTestFun m α)) (X (Real.toNNReal r) z ia.1) else 0) =
      fun s z => c1 • HRS.MH.DualityRd.truncGradIntegrand (u + t)
        (fun r => propagatorW (S.coeff N) r (u + t) (oscTestFun m α)) X s z := by
    funext r z ia
    by_cases hr : r ∈ Set.Icc (0 : ℝ) (u + t) <;> simp [HRS.MH.DualityRd.truncGradIntegrand, hr]
  rw [hk0] at hid
  have hneg : ∀ x : OscDual d m, OscDual.coord (-x) α = - OscDual.coord x α := fun x => by
    rw [← neg_one_smul ℝ x, OscDual.coord_smul]; ring
  have hFz : ∀ᵐ ζ ∂P, OscDual.coord (-((Real.sqrt β)⁻¹ • s21Rt S X νb ML (u + t) ζ)) α =
      ∫ r in Set.Icc (0 : ℝ) (u + t), (Real.sqrt N / 2) * (commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m
          (HRS.Whole.withDensityReal ρβ) X α (u + t) r ζ -
        ∫ ζ', commForcing (critCoeff d a β ρβ) ((d : ℝ) / 2) m (HRS.Whole.withDensityReal ρβ) X α (u + t) r ζ' ∂P) := by
    filter_upwards [hc] with ζ h1
    rw [hneg, OscDual.coord_smul, h1, integral_const_mul, hσ2]
    have hb0 : Real.sqrt β ≠ 0 := (Real.sqrt_pos.2 hβ).ne'
    field_simp
    rfl
  refine ⟨hFz, ?_⟩
  rw [← hScoeff N, hk1]
  filter_upwards [hc, hid, hsm0, hsm1] with ζ h1 h2 h3 h4
  have hz : zetaB m (P.map (X (Real.toNNReal (u + t)))) (X (Real.toNNReal (u + t)) ζ) =
      (Real.sqrt β)⁻¹ • s21Xi S X νb (u + t) ζ := by
    unfold zetaB s21Xi
    rw [hstat (u + t) ht', hσ2, smul_smul]
    congr 1
    have hb0 : Real.sqrt β ≠ 0 := (Real.sqrt_pos.2 hβ).ne'
    field_simp
  have hXi : s21Xi S X νb (u + t) ζ = (s21K0c S X νb ζ).evalA (u + t) +
      reconstructPath m (u + T) ML ζ (u + t) + s21Rt S X νb ML (u + t) ζ := by
    have e : s21Rt S X νb ML (u + t) ζ = s21Xi S X νb (u + t) ζ - (s21K0c S X νb ζ).evalA (u + t) -
        reconstructPath m (u + T) ML ζ (u + t) := rfl
    rw [e]; abel
  haveI hemp : IsProbabilityMeasure (HRS.Whole.empirical (X 0 ζ)) := HRS.Whole.empirical_isProbabilityMeasure hNpos _
  have hνi : Integrable (fun z : Euc d => ‖z‖) (HRS.Whole.empirical (X 0 ζ)) :=
    HRS.Whole.Q09A.integrable_empirical hN1 (X 0 ζ) _
  have hk0c : OscDual.coord ((s21K0c S X νb ζ).evalA (u + t)) α = S.σ N *
      (HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ)) (propagatorW (S.coeff N) 0 (u + t) (oscTestFun m α)) -
        HRS.Whole.pair νb (propagatorW (S.coeff N) 0 (u + t) (oscTestFun m α))) :=
    s81s_k0_coord (hSadj N) (S.σ N) hmeasG hB0 hbdG hcb _ _ hνi hν1 ht' α
  have hpair : HRS.Whole.pair νb (propagatorW (S.coeff N) 0 (u + t) (oscTestFun m α)) =
      ∫ x, propagatorW (S.coeff N) 0 (u + t) (oscTestFun m α) x ∂(HRS.Whole.firstMarginal (law P (X 0))) := by
    rw [← hmean]; rfl
  have hJ0 := h3 (u + t)
  have hJ1 := h4 (u + t)
  have hrec : OscDual.coord (reconstructPath m (u + T) ML ζ (u + t)) α =
      c0 * itoIntegral P ℱ W' (HRS.MH.DualityRd.truncGradIntegrand (u + t)
        (fun r => propagatorW (S.coeff N) r (u + t) (oscTestFun m α)) X) (u + t) ζ := by
    rw [h2]; exact hJ0
  rw [hz, OscDual.coord_smul, hXi, OscDual.coord_add, OscDual.coord_add, hk0c, hrec, hpair, hJ1, hneg,
    OscDual.coord_smul, hc01, hσ2]
  have hb0 : Real.sqrt β ≠ 0 := (Real.sqrt_pos.2 hβ).ne'
  field_simp
  ring

end HRS.Whole.S81S
