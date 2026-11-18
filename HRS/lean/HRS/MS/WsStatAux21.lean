import HRS.MS.WsStatAux20

/-!
# S21 packet F3g: the coordinates of the centred remainder

`s21_centered_coord`: in the stationary setting (`S.rho N t = rho`, `P.map (X t) = P.map (X 0)` on `[0,T]`, `M = -1`), for every
`t in [0,T]` and `alpha`, almost surely

`coord (s21Rt S X nubar M t) alpha = -(sigma/2) int_0^t (c_alpha(r,.) - E c_alpha(r,.)) dr`,  `c_alpha = commForcing`.

Proof: the mild identity `s56_mild_coord`; the coordinates of the centred field and of `A(s21K0c)`; the expectation of the mild identity
(`s21_E_pair_emp`, `s21_E_recon`, Fubini `s21_fubini_comm`, which identifies the deterministic constant `sigma (m_N - rho)(phi - U phi)`
with `sigma int_0^t E F dr`); `F = -(1/2) c` (`s21_fluc_eq_neg_half_comm`).
-/

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal

namespace HRS.MS.S21

open HRS.Whole HRS.MS.GenPath HRS.MP.RdRem HRS.MH.DualityRd
open HRS (Euc)

variable {d : ℕ}

/-- The pathwise identity `∫ F = -(1/2) ∫ c` of the forcing integrals. -/
theorem s21_forcing_eq (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ}
    (hM : b.M = -1) {ρ : Euc d → ℝ} (hρ' : ∀ t, S.ρ N t = ρ) {Ω : Type*} (X : ℝ≥0 → Ω → EucConfig d N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) (α : MultiIndex d) (ζ : Ω) :
    ∫ r in Set.Icc (0 : ℝ) t, HRS.Whole.AppendixA.flucInteractionRd (S.dyn N)
        (propagatorW (S.coeff N) r t (oscTestFun b.m α)) (X (Real.toNNReal r) ζ) (S.ρ N r) =
      -(1 / 2 : ℝ) * ∫ r in Set.Icc (0 : ℝ) t,
        commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ := by
  rw [← integral_const_mul]
  refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
  have hr' : r ∈ Set.Icc (0 : ℝ) b.T := ⟨hr.1, hr.2.trans ht.2⟩
  have hρr : S.ρ N r = ρ := hρ' r
  have hcl := s56_osc_classical b hbv S N ht α
  have hψ : MemCb 2 (propagatorW (S.coeff N) r t (oscTestFun b.m α)) :=
    s56_propagator_memCb (S.coeff N) t _ hr
  have hreg : RegSliceRd ρ := hρr ▸ s56_regSlice b hbv S N hr'
  rw [hρr]
  exact s21_fluc_eq_neg_half_comm (S.dyn N) (s21_dm b hbv).1 hbv.hs0 hbv.hsd hM hreg hψ _

theorem s21_centered_coord (b : WholeBounds d) (hbv : b.Valid) (S : WholeSetup b) {N : ℕ} (hN : 2 ≤ N)
    (hC : OscAdjointInput (S.coeff N) b.m b.T) (hM1 : b.M = -1) {ρ : Euc d → ℝ}
    (hρ' : ∀ t, S.ρ N t = ρ)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P]
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (hX : IsWholeStrongSolution P (S.dyn N) b.T X₀ W X) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) (hF : IsWholeFilteredSolution P ℱ W' W X)
    (M : ℝ → Ω → KSpace d b.m b.T)
    (hM : IsHilbertItoIntegral P ℱ W' (s56Phi (S.coeff N) b.m b.T (S.q N) X) M)
    (hstat : ∀ t ∈ Set.Icc (0 : ℝ) b.T, P.map (X (Real.toNNReal t)) = P.map (X 0))
    (hν1 : Integrable (fun x : Euc d => ‖x‖) (HRS.Whole.meanEmpirical (P.map (X 0))))
    (hfub : ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      IntegrableOn (fun r => ∫ ζ, commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P)
          (Set.Icc 0 t) ∧
        ∫ ζ, (∫ r in Set.Icc (0 : ℝ) t,
            commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ) ∂P =
          ∫ r in Set.Icc (0 : ℝ) t, ∫ ζ, commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P ∧
        Integrable (fun ζ => ∫ r in Set.Icc (0 : ℝ) t,
          commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ) P)
    (hint : ∀ᵐ ζ ∂P, ∀ α : MultiIndex d, ∀ t ∈ Set.Icc (0 : ℝ) b.T,
      IntegrableOn (fun r => commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ)
        (Set.Icc 0 t))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) (α : MultiIndex d) :
    ∀ᵐ ζ ∂P, OscDual.coord (s21Rt S X (HRS.Whole.meanEmpirical (P.map (X 0))) M t ζ) α =
      -(S.σ N / 2) * ∫ r in Set.Icc (0 : ℝ) t,
        (commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ -
          ∫ ζ', commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P) := by
  classical
  have hT0 : 0 ≤ b.T := hbv.hT.le
  have hN1 : 1 ≤ N := by omega
  have hNpos : 0 < N := by omega
  have hXm : ∀ t, Measurable (X t) := hX.adapted
  haveI hP0 : IsProbabilityMeasure (P.map (X 0)) :=
    (Measure.isProbabilityMeasure_map_iff (hXm 0).aemeasurable).2 inferInstance
  haveI hPt : IsProbabilityMeasure (P.map (X (Real.toNNReal t))) :=
    (Measure.isProbabilityMeasure_map_iff (hXm _).aemeasurable).2 inferInstance
  set νb : Measure (Euc d) := HRS.Whole.meanEmpirical (P.map (X 0)) with hνb
  haveI : IsProbabilityMeasure νb := HRS.Whole.meanEmpirical_isProbabilityMeasure _ hN1
  have hσ : 0 < S.σ N := s56_sigma_pos b S N hN1
  have hm : (d : ℝ) < b.m := (s21_dm b hbv).2
  have h0 : (0 : ℝ) ∈ Set.Icc (0 : ℝ) b.T := ⟨le_rfl, hT0⟩
  -- the test functions
  set φ : Euc d → ℝ := oscTestFun b.m α with hφ
  set U : Euc d → ℝ := propagatorW (S.coeff N) 0 t φ with hU
  obtain ⟨Cφ, -, hCφ⟩ := s56_oscTestFun_bound (d := d) b.m
  have hφb : ∀ x, |φ x| ≤ Cφ * oscEigenvalue d α ^ (-(b.m / 2)) := hCφ α
  have hφm : Measurable φ := (s56_oscTestFun_cont b.m α).measurable
  have hcl := s56_osc_classical b hbv S N ht α
  obtain ⟨BU, hBU⟩ := hcl.bdd 0 (Nat.zero_le _)
  have hUb : ∀ x, |U x| ≤ BU := fun x => by
    have := hBU 0 ⟨le_rfl, ht.1⟩ x
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hUm : Measurable U := ((hcl.c2 0 ⟨le_rfl, ht.1⟩).continuous).measurable
  -- instances
  have hemp : ∀ x : EucConfig d N, IsProbabilityMeasure (HRS.Whole.empirical x) := fun x =>
    HRS.Whole.empirical_isProbabilityMeasure hNpos x
  have hρprob : IsProbabilityMeasure (HRS.Whole.withDensityReal (S.ρ N 0)) :=
    HRS.MS.Thm.cb_withDensityReal_isProb ((S.mf N).density 0 h0)
  have hρt : IsProbabilityMeasure (HRS.Whole.withDensityReal (S.ρ N t)) :=
    HRS.MS.Thm.cb_withDensityReal_isProb ((S.mf N).density t ht)
  -- the mild identity
  have hmild := s56_mild_coord b hbv S hN1 hC P X₀ W X hX ℱ W' hF M hM ht α
  set Fi : Ω → ℝ := fun ζ => ∫ r in Set.Icc (0 : ℝ) t, HRS.Whole.AppendixA.flucInteractionRd (S.dyn N)
    (propagatorW (S.coeff N) r t φ) (X (Real.toNNReal r) ζ) (S.ρ N r) with hFi
  set Ci : Ω → ℝ := fun ζ => ∫ r in Set.Icc (0 : ℝ) t,
    commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ with hCi
  have hFiC : ∀ ζ, Fi ζ = -(1 / 2 : ℝ) * Ci ζ := fun ζ => s21_forcing_eq b hbv S hM1 hρ' X ht α ζ
  set A : Ω → ℝ := fun ζ => HRS.Whole.pair (HRS.Whole.empirical (X (Real.toNNReal t) ζ)) φ with hA
  set A0 : Ω → ℝ := fun ζ => HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ)) U with hA0
  set Rc : Ω → ℝ := fun ζ => OscDual.coord (reconstructPath b.m b.T M ζ t) α with hRc
  set pρφ : ℝ := HRS.Whole.pair (HRS.Whole.withDensityReal ρ) φ with hpρφ
  set pρU : ℝ := HRS.Whole.pair (HRS.Whole.withDensityReal ρ) U with hpρU
  set pνφ : ℝ := HRS.Whole.pair νb φ with hpνφ
  set pνU : ℝ := HRS.Whole.pair νb U with hpνU
  have hmild' : ∀ᵐ ζ ∂P, S.σ N * (A ζ - pρφ) = S.σ N * (A0 ζ - pρU) + Rc ζ + S.σ N * Fi ζ := by
    filter_upwards [hmild] with ζ h
    haveI := hemp (X (Real.toNNReal t) ζ)
    rw [OscDual.coord_smul, s56_coord_ofMeasureDiff hm, hρ' t] at h
    have e1 : ∫ x, oscTestFun b.m α x ∂(HRS.Whole.empirical (X (Real.toNNReal t) ζ)) = A ζ := rfl
    have e2 : ∫ x, oscTestFun b.m α x ∂(HRS.Whole.withDensityReal ρ) = pρφ := rfl
    rw [e1, e2, hρ' 0] at h
    exact h
  -- expectations
  have hEA : ∫ ζ, A ζ ∂P = pνφ := by
    have := s21_E_pair_emp hN1 P (X (Real.toNNReal t)) (hXm _) (P.map (X (Real.toNNReal t))) rfl hφm hφb
    rw [hstat t ht] at this
    exact this
  have hEA0 : ∫ ζ, A0 ζ ∂P = pνU := by
    exact s21_E_pair_emp hN1 P (X 0) (hXm 0) (P.map (X 0)) rfl hUm hUb
  have hERc : ∫ ζ, Rc ζ ∂P = 0 := s21_E_recon (X₀ := X₀) b hbv S hN1 hC P ℱ W' hF M hM ht α
  obtain ⟨hfub1, hfub2, hfub3⟩ := hfub α t ht
  have hIA : Integrable A P := s21_pair_emp_integrable hNpos P _ (hXm _) hφm hφb
  have hIA0 : Integrable A0 P := s21_pair_emp_integrable hNpos P _ (hXm 0) hUm hUb
  have hIC : Integrable Ci P := hfub3
  have hIFi : Integrable Fi P := by
    have : Fi = fun ζ => -(1 / 2 : ℝ) * Ci ζ := funext hFiC
    rw [this]; exact hIC.const_mul _
  have hRcae : Rc =ᵐ[P] fun ζ => S.σ N * (A ζ - pρφ) - S.σ N * (A0 ζ - pρU) - S.σ N * Fi ζ := by
    filter_upwards [hmild'] with ζ h
    linarith
  have hIRc : Integrable Rc P := by
    refine Integrable.congr ?_ hRcae.symm
    exact (((hIA.sub (integrable_const _)).const_mul _).sub ((hIA0.sub (integrable_const _)).const_mul _)).sub
      (hIFi.const_mul _)
  have hEFi : ∫ ζ, Fi ζ ∂P = -(1 / 2 : ℝ) * ∫ r in Set.Icc (0 : ℝ) t,
      ∫ ζ, commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ ∂P := by
    have : Fi = fun ζ => -(1 / 2 : ℝ) * Ci ζ := funext hFiC
    rw [this, integral_const_mul]
    exact congrArg _ hfub2
  -- the constant
  have hK : (pνφ - pρφ) - (pνU - pρU) = ∫ ζ, Fi ζ ∂P := by
    have h1 : ∫ ζ, Rc ζ ∂P = ∫ ζ, (S.σ N * (A ζ - pρφ) - S.σ N * (A0 ζ - pρU) - S.σ N * Fi ζ) ∂P :=
      integral_congr_ae hRcae
    have hi1 : Integrable (fun ζ => S.σ N * (A ζ - pρφ)) P := (hIA.sub (integrable_const _)).const_mul _
    have hi2 : Integrable (fun ζ => S.σ N * (A0 ζ - pρU)) P := (hIA0.sub (integrable_const _)).const_mul _
    have hi3 : Integrable (fun ζ => S.σ N * Fi ζ) P := hIFi.const_mul _
    have e1 : ∫ ζ, (S.σ N * (A ζ - pρφ) - S.σ N * (A0 ζ - pρU) - S.σ N * Fi ζ) ∂P =
        (∫ ζ, S.σ N * (A ζ - pρφ) ∂P) - (∫ ζ, S.σ N * (A0 ζ - pρU) ∂P) - ∫ ζ, S.σ N * Fi ζ ∂P := by
      rw [integral_sub (f := fun ζ => S.σ N * (A ζ - pρφ) - S.σ N * (A0 ζ - pρU))
        (g := fun ζ => S.σ N * Fi ζ) (hi1.sub hi2) hi3,
        integral_sub (f := fun ζ => S.σ N * (A ζ - pρφ)) (g := fun ζ => S.σ N * (A0 ζ - pρU)) hi1 hi2]
    have e2 : ∫ ζ, S.σ N * (A ζ - pρφ) ∂P = S.σ N * (pνφ - pρφ) := by
      rw [integral_const_mul, integral_sub hIA (integrable_const _), hEA]
      simp
    have e3 : ∫ ζ, S.σ N * (A0 ζ - pρU) ∂P = S.σ N * (pνU - pρU) := by
      rw [integral_const_mul, integral_sub hIA0 (integrable_const _), hEA0]
      simp
    have e4 : ∫ ζ, S.σ N * Fi ζ ∂P = S.σ N * ∫ ζ, Fi ζ ∂P := integral_const_mul _ _
    rw [e1, e2, e3, e4] at h1
    rw [hERc] at h1
    have h2 : S.σ N * ((pνφ - pρφ) - (pνU - pρU) - ∫ ζ, Fi ζ ∂P) = 0 := by linarith
    rcases mul_eq_zero.1 h2 with h | h
    · exact absurd h hσ.ne'
    · linarith
  -- the pointwise coordinate formula
  have hk0 : ∀ ζ, OscDual.coord ((s21K0c S X νb ζ).evalA t) α = S.σ N * (A0 ζ - pνU) := fun ζ => by
    haveI := hemp (X 0 ζ)
    exact s21_k0_eval_gen2 b hbv S N hC (S.σ N) (HRS.Whole.empirical (X 0 ζ)) νb
      (HRS.Whole.Q09A.integrable_empirical hNpos _ _) hν1 ht α
  have hXi : ∀ ζ, OscDual.coord (s21Xi S X νb t ζ) α = S.σ N * (A ζ - pνφ) := fun ζ => by
    haveI := hemp (X (Real.toNNReal t) ζ)
    unfold s21Xi
    rw [OscDual.coord_smul, s56_coord_ofMeasureDiff hm]
    rfl
  have hint_t : ∀ᵐ ζ ∂P, IntegrableOn
      (fun r => commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ) (Set.Icc 0 t) := by
    filter_upwards [hint] with ζ h using h α t ht
  filter_upwards [hmild', hint_t] with ζ h hi
  unfold s21Rt
  rw [s56_coord_sub, s56_coord_sub, hXi ζ, hk0 ζ]
  have hdiff : ∫ r in Set.Icc (0 : ℝ) t,
      (commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ -
        ∫ ζ', commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P) =
      Ci ζ - ∫ r in Set.Icc (0 : ℝ) t,
        ∫ ζ', commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P :=
    integral_sub hi hfub1
  rw [hdiff]
  have hFiζ := hFiC ζ
  have hEFi' := hEFi
  have hRζ : Rc ζ = S.σ N * (A ζ - pρφ) - S.σ N * (A0 ζ - pρU) - S.σ N * Fi ζ := by linarith
  show S.σ N * (A ζ - pνφ) - S.σ N * (A0 ζ - pνU) - Rc ζ = _
  rw [hRζ]
  have : ∫ r in Set.Icc (0 : ℝ) t, ∫ ζ', commForcing (S.coeff N) b.s b.m (HRS.Whole.withDensityReal ρ) X α t r ζ' ∂P
      = -2 * (pνφ - pρφ - (pνU - pρU)) := by
    have := hEFi'
    rw [← hK] at this
    linarith
  rw [this]
  have hFi2 : Fi ζ = -(1 / 2 : ℝ) * Ci ζ := hFiζ
  rw [hFi2]
  ring

end HRS.MS.S21
