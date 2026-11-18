import HRS.MS.PathFidiAux6
import HRS.Main.A9Aux32
import HRS.MP.FidiF1
import HRS.MP.FidiLaw

/-!
# SA26 packet P6: B5, null contact, the covariance bound, Levy, identification, measurability
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.PathFidi

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

section Misc

theorem sa26_B5 (s : ℝ) (fd : FieldDensityRd d s) (ν₀ MB Λ ΛV G₀ Kad : ℝ) (hd : 1 ≤ d) (hs0 : 0 ≤ s)
    (hsd : s < d) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∀ (S : WholeMainData d), S.s = s → fd.Holds S ν₀ →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ) (m20 : ℝ) (r mV : ℕ),
        RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈 → FieldAdjointInputRd fd S Kad →
        ∃ K' : ℝ, 0 ≤ K' ∧ SelectedCommutatorInput S (fd.Gamma : ℝ) S.T K' C₀ Λ fd.eN := by
  by_cases hsc : (d : ℝ) - 2 ≤ s
  · exact sa26_B5_super s fd ν₀ MB Λ ΛV G₀ Kad hd hs0 hsd hsc
  · have hsub : s < (d : ℝ) - 2 := not_le.1 hsc
    cases fd with
    | nd Rg =>
      refine ⟨0, fun C₀ _ S hSs hHolds => ?_⟩
      exfalso
      have h1 : max 0 ((d : ℝ) - 2) ≤ S.s := (hHolds 1 le_rfl).1
      rw [hSs] at h1
      linarith [le_max_right 0 ((d : ℝ) - 2)]
    | decSub c => exact sa26_B5_sub s c ν₀ MB Λ ΛV G₀ Kad hd hs0 hsub
    | decSuperIso m p =>
      refine ⟨0, fun C₀ _ S hSs hHolds => ?_⟩
      exfalso
      have h1 : (d : ℝ) - 2 < S.s := (hHolds 1 le_rfl).1
      rw [hSs] at h1
      linarith
    | decSuperHilb m =>
      refine ⟨0, fun C₀ _ S hSs hHolds => ?_⟩
      exfalso
      have h1 : (d : ℝ) - 2 < S.s := (hHolds 1 le_rfl).1
      rw [hSs] at h1
      linarith

theorem sa26_grad_meas (V : Euc d → ℝ) : Measurable (gradient V) := by
  unfold gradient
  exact (InnerProductSpace.toDual ℝ (Euc d)).symm.continuous.measurable.comp (measurable_fderiv ℝ V)

end Misc


/-! ### Null contact occupation of a whole-space contact strong solution in `d = 1` -/

section Null

theorem sa26_nullContact_d1 {N : ℕ} {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {D : WholeDyn 1} {T : ℝ} (hT0 : 0 ≤ T) {X₀ : Ω → EucConfig 1 N}
    {W : ℝ≥0 → Ω → (Fin N → Euc 1)} {X : ℝ≥0 → Ω → EucConfig 1 N}
    (hX : IsWholeContactStrongSolution P D T X₀ W X) {ℱ : Filtration ℝ mΩ}
    {W' : ℝ≥0 → Ω → (Fin N × Fin 1) → ℝ} (hF : IsWholeFilteredSolution P ℱ W' W X)
    (hβ : 0 < D.invβ) (hVm : Measurable (gradient D.V)) :
    ∀ᵐ ζ ∂P, volume {s : ℝ | s ∈ Set.Icc 0 T ∧ X (Real.toNNReal s) ζ ∈ eucCollisionSet 1 N} = 0 := by
  classical
  have hcoord : Measurable fun v : Euc 1 => v 0 := by fun_prop
  have hdr : Measurable fun x : EucConfig 1 N => fun i => particleDriftW D x i :=
    HRS.Whole.Q09B.q09b_measurable_driftVec D hVm
  have hzero : ∀ i j : Fin N, i ≠ j → ∀ᵐ ζ ∂P, volume {s : ℝ | s ∈ Set.Icc 0 T ∧
      X (Real.toNNReal s) ζ i 0 - X (Real.toNNReal s) ζ j 0 = 0} = 0 := by
    intro i j hij
    set s0 : ℝ := Real.sqrt (2 * D.invβ) with hs0
    have hs0pos : 0 < s0 := Real.sqrt_pos.2 (by positivity)
    set σ : Fin N × Fin 1 → ℝ := fun k => if k = (i, 0) then s0 else if k = (j, 0) then -s0 else 0 with hσ
    have hne : ((i, (0 : Fin 1)) : Fin N × Fin 1) ≠ (j, 0) := fun h => hij (Prod.mk.inj h).1
    refine HRS.Main.A8P.a8p_zero_null (ι := Fin N × Fin 1) hF.brownian hT0 σ ?_
      (fun t ζ => X t ζ i 0 - X t ζ j 0) ?_
      (fun t ζ => particleDriftW D (X t ζ) i 0 - particleDriftW D (X t ζ) j 0) ?_ ?_ ?_
    · refine lt_of_lt_of_le (pow_pos hs0pos 2) ?_
      have := Finset.single_le_sum (f := fun k => σ k ^ 2) (fun _ _ => sq_nonneg _)
        (Finset.mem_univ ((i, (0 : Fin 1)) : Fin N × Fin 1))
      simpa [hσ] using this
    · intro t
      have h0 := HRS.Whole.Q09B.q09b_measurable_init hF t
      exact ((hcoord.comp ((measurable_pi_apply i).comp h0)).sub
        (hcoord.comp ((measurable_pi_apply j).comp h0)))
    · intro r
      have hf : Measurable fun x : EucConfig 1 N => particleDriftW D x i 0 - particleDriftW D x j 0 :=
        (hcoord.comp ((measurable_pi_apply i).comp hdr)).sub (hcoord.comp ((measurable_pi_apply j).comp hdr))
      exact hf.comp (hF.progressive r)
    · filter_upwards [hX.eqn] with ζ hζ
      have := (hζ (Real.toNNReal T) (by rw [Real.coe_toNNReal _ hT0])).1
      rw [Real.coe_toNNReal _ hT0] at this
      have hI : IntegrableOn (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ) i 0 -
          particleDriftW D (X (Real.toNNReal s) ζ) j 0) (Set.Icc 0 T) := by
        have h1 := ((EuclideanSpace.proj (0 : Fin 1) : Euc 1 →L[ℝ] ℝ).integrable_comp (this i))
        have h2 := ((EuclideanSpace.proj (0 : Fin 1) : Euc 1 →L[ℝ] ℝ).integrable_comp (this j))
        exact h1.sub h2
      exact hI
    · filter_upwards [hX.eqn, hF.coords] with ζ he hc t ht
      obtain ⟨hI, hE⟩ := he t ht
      have hIi : ∀ k, Integrable (fun s : ℝ => particleDriftW D (X (Real.toNNReal s) ζ) k 0)
          (volume.restrict (Set.Icc (0 : ℝ) t)) := fun k =>
        (EuclideanSpace.proj (0 : Fin 1) : Euc 1 →L[ℝ] ℝ).integrable_comp (hI k)
      have hA : ∀ k, (∫ s in Set.Icc (0 : ℝ) t, particleDriftW D (X (Real.toNNReal s) ζ) k) 0 =
          ∫ s in Set.Icc (0 : ℝ) t, particleDriftW D (X (Real.toNNReal s) ζ) k 0 := fun k =>
        ((EuclideanSpace.proj (0 : Fin 1) : Euc 1 →L[ℝ] ℝ).integral_comp_comm (hI k)).symm
      have hEi := fun k => congrArg (fun v : Euc 1 => v 0) (hE k)
      simp only [PiLp.add_apply, PiLp.smul_apply, PiLp.sub_apply, smul_eq_mul] at hEi
      simp only [hA] at hEi
      have hsum : ∑ k, (W' t ζ k - W' 0 ζ k) • σ k =
          s0 * (W t ζ i 0 - W 0 ζ i 0) - s0 * (W t ζ j 0 - W 0 ζ j 0) := by
        rw [Fintype.sum_eq_add (i, (0 : Fin 1)) (j, 0) hne (fun k hk => by simp [hσ, hk.1, hk.2])]
        simp only [hσ, if_true, hne.symm, if_false, hc t, hc 0, smul_eq_mul]
        ring
      rw [hsum, integral_sub (hIi i) (hIi j), hEi i, hEi j, hs0]
      ring
  have hall : ∀ᵐ ζ ∂P, ∀ i j : Fin N, i ≠ j → volume {s : ℝ | s ∈ Set.Icc 0 T ∧
      X (Real.toNNReal s) ζ i 0 - X (Real.toNNReal s) ζ j 0 = 0} = 0 :=
    ae_all_iff.2 fun i => ae_all_iff.2 fun j => by
      by_cases hij : i = j
      · exact Eventually.of_forall fun ζ h => absurd hij h
      · exact (hzero i j hij).mono fun ζ h _ => h
  filter_upwards [hall] with ζ hζ
  refine measure_mono_null ?_ (measure_iUnion_null fun i => measure_iUnion_null fun j =>
    measure_iUnion_null fun hij : i ≠ j => hζ i j hij)
  intro s hs
  obtain ⟨hs1, i, j, hij, hXij⟩ := hs
  refine Set.mem_iUnion.2 ⟨i, Set.mem_iUnion.2 ⟨j, Set.mem_iUnion.2 ⟨hij, hs1, ?_⟩⟩⟩
  rw [hXij]
  ring

end Null


section FlowAll

theorem sa26_flow_inj_all {Ω : Type*} [mΩ : MeasurableSpace Ω] {N : ℕ} {P : Measure Ω}
    [IsProbabilityMeasure P] {D : WholeDyn d} {T : ℝ} (hT0 : 0 ≤ T) {X₀ : Ω → EucConfig d N}
    {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (h : SelectedFlowRd P D T X₀ W X) {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution P ℱ W' W X) :
    ∀ᵐ ζ ∂P, ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Function.Injective (X (Real.toNNReal r) ζ) := by
  rcases h.flow with ⟨h1, -⟩ | ⟨-, -, -, -, h2⟩ | ⟨hd1, -, hβ, -, h3⟩
  · filter_upwards [h1.no_collision] with ζ hζ
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
    intro i j hij
    by_contra hne
    exact hζ (Real.toNNReal r) (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2) ⟨i, j, hne, hij⟩
  · filter_upwards [h2.occupation] with ζ hζ
    have h3 := measure_eq_zero_iff_ae_notMem.1 hζ
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [h3] with r hr hrm
    intro i j hij
    by_contra hne
    exact hr ⟨hrm, ⟨i, j, hne, hij⟩⟩
  · subst hd1
    have hocc := sa26_nullContact_d1 hT0 h3 hF hβ (sa26_grad_meas D.V)
    filter_upwards [hocc] with ζ hζ
    have h4 := measure_eq_zero_iff_ae_notMem.1 hζ
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [h4] with r hr hrm
    intro i j hij
    by_contra hne
    exact hr ⟨hrm, ⟨i, j, hne, hij⟩⟩

end FlowAll


section CovFinal

theorem sa26_cov_bound (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (χ : Euc d → ℝ)
    (hχ : IsUlocCutoff χ) (Λ : ℝ) :
    ∃ C₁ CT : ℝ, 0 ≤ CT ∧ ∀ C₀ : ℝ, C₁ ≤ C₀ → ∀ (S : WholeMainData d), S.s = s →
      ∀ (R : ∀ N, RealizationRd d N) (𝔈 : ℕ → ℝ) (MB ΛV G₀ m20 : ℝ) (r mV : ℕ),
        RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈 →
      ∀ m₂ : ℝ, 0 ≤ m₂ → PropagatedSecondMoment S R m₂ →
      ∀ N : ℕ, 2 ≤ N → ∀ {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ),
        (∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) →
      ∀ Bd : Fin p → ℝ, (∀ a, 0 ≤ Bd a) →
      (∀ a, ∀ r' ∈ Set.Icc (0 : ℝ) (ts a),
        ContDiff ℝ ((mStar d : ℕ) : WithTop ℕ∞) (propagatorW (S.coeff N) r' (ts a) (φ a)) ∧
          ∀ l ≤ mStar d, ∀ x, ‖iteratedFDeriv ℝ l (propagatorW (S.coeff N) r' (ts a) (φ a)) x‖ ≤ Bd a) →
      (∀ a, ∃ f, IsClassicalAdjointW (S.coeff N) (ts a) (φ a) f) →
      ∀ {ℱ : Filtration ℝ (R N).mΩ}, IsProgressive ℱ (ofNNRealTime (R N).X) →
      (∀ᵐ ζ ∂(R N).P, ∀ᵐ r' ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
        Function.Injective ((R N).X (Real.toNNReal r') ζ)) →
      Measurable (Function.uncurry (killedCovMatrix (fun a => sa26_K S N ts φ (R N).X a) ts)) →
        covDiscrepancyMatrix (R N).P S.T (killedCovMatrix (fun a => sa26_K S N ts φ (R N).X a) ts)
          (sa26SigBar ts (sa26_G S N ts φ) (fun r' => S.ρ N (HRS.MP.RdRem.mrrClamp S.T r'))
            (2 * S.qN N)) ≤
          CT * S.T * (∑ a, Bd a) ^ 2 * (S.qN N * wN d N (𝔈 N) m₂) := by
  classical
  obtain ⟨C₀', C₁c, hC₀', hpair⟩ := HRS.MH.CoercTest.p_assembly d hd s hs0 hsd
  obtain ⟨Cp, hCp⟩ := test_cutoff_pathwise hd s hs0 hsd χ hχ C₁c
  obtain ⟨Cn, hCn0, hCn⟩ := sa26_cNorm_inner hd χ hχ
  obtain ⟨C₂, hC₂⟩ := sa26_oN_comp d hd s hs0 Λ C₀'
  refine ⟨C₂, 2 * max Cp 0 * Cn, mul_nonneg (mul_nonneg (by norm_num) (le_max_right _ _)) hCn0, ?_⟩
  intro C₀ hC₀ S hSs R 𝔈 MB ΛV G₀ m20 r mV hS m₂ hm₂ hm2 N hN p ts φ hts Bd hBd0 hBd hex ℱ hprog hinj hsig
  have hΛ := sa26_Lam_pos hS
  have hN1 : 1 ≤ N := by omega
  have hN0 : 0 < N := by omega
  have hT : 0 < S.T := S.hT
  set Λ' : ℝ := max Λ 1 with hΛ'
  have hΛ'1 : 1 ≤ Λ' := le_max_right _ _
  have hcomp : oNΛ d S.s C₀' Λ' N ≤ oNΛ d S.s C₀ Λ N := by
    rw [hSs]; exact hC₂ hΛ C₀ hC₀ N hN1
  have hΛ'0 : 0 ≤ smearScale d N Λ' := by
    unfold smearScale
    exact Real.rpow_nonneg (by positivity) _
  have hsm : smearScale d N Λ' ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := by
    unfold smearScale
    refine Real.rpow_le_rpow_of_nonpos (by positivity) ?_ ?_
    · have : (1 : ℝ) ≤ Λ' := hΛ'1
      have : (0 : ℝ) < N := by exact_mod_cast hN0
      nlinarith
    · have : (0 : ℝ) ≤ 1 / (d : ℝ) := by positivity
      rw [neg_div]; linarith
  set cc : Fin p → Fin p → ℝ := fun a b => max Cp 0 * (Cn * (Bd a * Bd b)) with hcc
  have hcc0 : ∀ a b, 0 ≤ cc a b := fun a b =>
    mul_nonneg (le_max_right _ _) (mul_nonneg hCn0 (mul_nonneg (hBd0 a) (hBd0 b)))
  have hW0 : 0 ≤ wN d N (𝔈 N) m₂ := sa26_wN_nonneg d N (hS.energy.pos N hN1).le hm₂
  have hEnn : ∀ r' ∈ Set.Icc (0 : ℝ) S.T, ∀ X : EucConfig d N, Function.Injective X →
      0 ≤ rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N r')) + oNΛ d S.s C₀' Λ' N := by
    intro r' hr' X hX
    have hprob := (hS.mean_field.solution N hN1).density r' hr'
    have hρΛ : ∀ x, S.ρ N r' x ≤ Λ' := fun x => (sa26_rho_le hS hN1 hr' x).trans (le_max_left _ _)
    rw [hSs]
    exact (hpair C₀' le_rfl).1.2 Λ' hΛ'1 N hN (S.ρ N r') hprob hρΛ
      (fun _ => sa26_log_int hS hN1 hr') X (fun ⟨i, j, hij, h⟩ => hij (hX h))
  have hpairs : ∀ a b, ∫⁻ q, ENNReal.ofReal |sa26_Lab S R N ts φ a b q| ∂((R N).P.prod (sa26_μT S.T)) ≤
      ENNReal.ofReal (cc a b * wN d N (𝔈 N) m₂) := by
    intro a b
    refine sa26_pair_int hS hm₂ hm2 hN ts φ hts hex hprog hinj a b (cc := cc a b)
      (o' := oNΛ d S.s C₀' Λ' N) (Λ' := Λ') (hcc0 a b) ?_ hEnn hcomp hsm hΛ'0
    intro r' hr' X hX R' hR'
    have hprob := (hS.mean_field.solution N hN1).density r' hr'
    have hρΛ : ∀ x, S.ρ N r' x ≤ Λ' := fun x => (sa26_rho_le hS hN1 hr' x).trans (le_max_left _ _)
    have hmom := (hS.mean_field.solution N hN1).second_moment r' hr'
    have hGU : ∀ c x, sa26_G S N ts φ c r' x = gradient (sa26_Uh S N ts φ c r') x := fun c x =>
      sa26_G_eq ts φ c r' x
    have hcN : cNormE χ (sa26_hab S N ts φ a b r') ≤ ENNReal.ofReal (Cn * (Bd a * Bd b)) := by
      have hUa := sa26_Uh_props (S := S) (N := N) ts φ a (hBd0 a) (hBd a) r'
      have hUb := sa26_Uh_props (S := S) (N := N) ts φ b (hBd0 b) (hBd b) r'
      have := hCn (sa26_Uh S N ts φ a r') (sa26_Uh S N ts φ b r') (Bd a) (Bd b) hUa.1 hUb.1 hUa.2 hUb.2
      have e : sa26_hab S N ts φ a b r' = fun x => inner ℝ (gradient (sa26_Uh S N ts φ a r') x)
          (gradient (sa26_Uh S N ts φ b r') x) := by
        funext x
        simp only [sa26_hab, hGU]
      rw [e]
      exact this
    have hcn0 : 0 ≤ Cn * (Bd a * Bd b) := mul_nonneg hCn0 (mul_nonneg (hBd0 a) (hBd0 b))
    have hfin : cNormE χ (sa26_hab S N ts φ a b r') < ⊤ := lt_of_le_of_lt hcN ENNReal.ofReal_lt_top
    have hcn : (cNormE χ (sa26_hab S N ts φ a b r')).toReal ≤ Cn * (Bd a * Bd b) :=
      ENNReal.toReal_le_of_le_ofReal hcn0 hcN
    have key := hCp C₀' (hpair C₀' le_rfl) Λ' hΛ'1 N hN (S.ρ N r') hprob hρΛ hmom X hX
      (sa26_hab S N ts φ a b r') hfin R' hR'
    rw [← hSs] at key
    have hbr : 0 ≤ R' ^ ((d : ℝ) / 2) * (smearScale d N Λ' + Real.sqrt (rieszModulatedEnergy d S.s X
        (HRS.Whole.withDensityReal (S.ρ N r')) + oNΛ d S.s C₀' Λ' N)) +
        (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal (S.ρ N r'))) /
          R' ^ 2 := by
      have h1 : 0 ≤ R' ^ ((d : ℝ) / 2) := Real.rpow_nonneg (by linarith) _
      have h2 := Q09A.secondMomentOf_nonneg (HRS.Whole.empirical X)
      have h3 := Q09A.secondMomentOf_nonneg (HRS.Whole.withDensityReal (S.ρ N r'))
      exact add_nonneg (mul_nonneg h1 (add_nonneg hΛ'0 (Real.sqrt_nonneg _)))
        (div_nonneg (add_nonneg h2 h3) (by positivity))
    refine key.trans ?_
    refine mul_le_mul_of_nonneg_right ?_ hbr
    exact mul_le_mul (le_max_left _ _) hcn ENNReal.toReal_nonneg (le_max_right _ _)
  have hcd := sa26_covDisc_le hS hN ts φ hts hex hprog hsig hcc0 hW0 hpairs
  refine hcd.trans (le_of_eq ?_)
  have hsum : ∑ a, ∑ b, cc a b * wN d N (𝔈 N) m₂ =
      max Cp 0 * Cn * (∑ a, Bd a) ^ 2 * wN d N (𝔈 N) m₂ := by
    simp only [hcc, ← Finset.sum_mul, sq, Finset.sum_mul_sum]
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun a _ => ?_
    rw [Finset.mul_sum, Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_congr rfl fun b _ => ?_
    ring
  rw [hsum]
  ring

end CovFinal


section Levy

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

theorem sa26_levy {p : ℕ} (μ : ℕ → Measure (ℝ^p)) (μ₀ : Measure (ℝ^p))
    [∀ n, IsProbabilityMeasure (μ n)] [IsProbabilityMeasure μ₀]
    (hμ : HRS.Main.ConvergesInLaw μ μ₀) (Sn : ℕ → Matrix (Fin p) (Fin p) ℝ)
    (S0 : Matrix (Fin p) (Fin p) ℝ) (hpn : ∀ n, (Sn n).PosSemidef) (hp0 : S0.PosSemidef)
    (hS : Tendsto Sn atTop (𝓝 S0)) :
    HRS.Main.ConvergesInLaw (fun n => μ n ∗ multivariateGaussian 0 (Sn n))
      (μ₀ ∗ multivariateGaussian 0 S0) := by
  have hT0 : Tendsto (fun n => (μ n).toProbabilityMeasure) atTop (𝓝 μ₀.toProbabilityMeasure) :=
    ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.2 (fun f => by simpa using hμ f)
  have hc0 := ProbabilityMeasure.tendsto_iff_tendsto_charFun.1 hT0
  have key : ∀ t : ℝ^p, Tendsto (fun n => charFun (μ n ∗ multivariateGaussian 0 (Sn n)) t) atTop
      (𝓝 (charFun (μ₀ ∗ multivariateGaussian 0 S0) t)) := by
    intro t
    have e : ∀ n, charFun (μ n ∗ multivariateGaussian 0 (Sn n)) t = charFun (μ n) t *
        Complex.exp (-(((dotProduct t.ofLp ((Sn n).mulVec t.ofLp) : ℝ) : ℂ) / 2)) := fun n => by
      rw [charFun_conv, HRS.MP.FidiLaw.fl_charFun_gauss (hpn n) t]
    simp_rw [e]
    rw [charFun_conv, HRS.MP.FidiLaw.fl_charFun_gauss hp0 t]
    refine Tendsto.mul (hc0 t) ?_
    have hc : Continuous (fun M : Matrix (Fin p) (Fin p) ℝ =>
        Complex.exp (-(((dotProduct t.ofLp (M.mulVec t.ofLp) : ℝ) : ℂ) / 2))) := by
      simp only [Matrix.mulVec, dotProduct]
      fun_prop
    exact (hc.tendsto _).comp hS
  have hT : Tendsto (fun n => Measure.toProbabilityMeasure (μ n ∗ multivariateGaussian 0 (Sn n)))
      atTop (𝓝 (Measure.toProbabilityMeasure (μ₀ ∗ multivariateGaussian 0 S0))) :=
    ProbabilityMeasure.tendsto_iff_tendsto_charFun.2 key
  intro f
  simpa using ProbabilityMeasure.tendsto_iff_forall_integral_tendsto.1 hT f

theorem sa26_identify {Ω' : Type*} [MeasurableSpace Ω'] (P' : Measure Ω') [IsProbabilityMeasure P']
    {p : ℕ} (U G Z : Ω' → ℝ^p) (hU : AEMeasurable U P') (hG : AEMeasurable G P')
    (hind : IndepFun U G P') (hZ : ∀ ζ, Z ζ = U ζ + G ζ) :
    law P' Z = law P' U ∗ law P' G := by
  have : Z = U + G := funext hZ
  rw [this]
  exact hind.map_add_eq_map_conv_map₀ hU hG

theorem sa26_integral_le_lintegral {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} {g : Ω → ℝ}
    (hg0 : ∀ z, 0 ≤ g z) (hgm : AEStronglyMeasurable g P) {B : ℝ} (hB : 0 ≤ B)
    (h : ∫⁻ z, ENNReal.ofReal (g z) ∂P ≤ ENNReal.ofReal B) : ∫ z, g z ∂P ≤ B := by
  rw [integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall hg0) hgm]
  exact ENNReal.toReal_le_of_le_ofReal hB h

end Levy


section Aux7

theorem sa26_norm_le_sum_abs {q : ℕ} (v : EuclideanSpace ℝ (Fin q)) : ‖v‖ ≤ ∑ a, |v a| := by
  rw [EuclideanSpace.norm_eq]
  refine Real.sqrt_le_iff.2 ⟨Finset.sum_nonneg fun a _ => abs_nonneg _, ?_⟩
  refine le_trans (le_of_eq ?_) (Finset.sum_sq_le_sq_sum_of_nonneg (fun a _ => abs_nonneg (v a)))
  refine Finset.sum_congr rfl fun a _ => ?_
  rw [Real.norm_eq_abs, sq_abs]

theorem sa26_pair_emp_meas {Ω : Type*} {m : MeasurableSpace Ω} {N : ℕ} (hN : 0 < N)
    {X : Ω → EucConfig d N} (hX : Measurable[m] X) {ψ : Euc d → ℝ} (hψ : Continuous ψ) :
    Measurable[m] fun ζ => HRS.Whole.pair (HRS.Whole.empirical (X ζ)) ψ := by
  have e : (fun ζ => HRS.Whole.pair (HRS.Whole.empirical (X ζ)) ψ) = fun ζ => (N : ℝ)⁻¹ * ∑ i, ψ (X ζ i) := by
    funext ζ
    exact HRS.Whole.pair_empirical hN _ _
  rw [e]
  exact measurable_const.mul (Finset.measurable_sum _ fun i _ =>
    hψ.measurable.comp ((measurable_pi_apply i).comp hX))

theorem sa26_Iemp_meas {Ω : Type*} {m : MeasurableSpace Ω} {N : ℕ} (hN : 0 < N) (S : WholeMainData d)
    {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) {X : ℝ≥0 → Ω → EucConfig d N}
    (hX0 : Measurable[m] (X 0)) (hc : ∀ a, Continuous (propagatorW (S.coeff N) 0 (ts a) (φ a))) :
    Measurable[m] (sa26_Iemp S N ts φ X) := by
  unfold sa26_Iemp
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a => ?_)
  exact (((sa26_pair_emp_meas hN hX0 (hc a)).sub measurable_const)).const_mul _

theorem sa26_fluct_meas {Ω : Type*} {m : MeasurableSpace Ω} {N : ℕ} (hN : 0 < N) (σ : ℝ)
    {X : ℝ≥0 → Ω → EucConfig d N} (hX : ∀ t, Measurable[m] (X t)) (ρ : ℝ → Euc d → ℝ) {p : ℕ}
    (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (hc : ∀ a, Continuous (φ a)) :
    Measurable[m] (fluctStatRd σ X ρ ts φ) := by
  unfold fluctStatRd
  refine (WithLp.measurable_toLp 2 _).comp (measurable_pi_iff.2 fun a => ?_)
  exact (((sa26_pair_emp_meas hN (hX _) (hc a)).sub measurable_const)).const_mul _


theorem sa26_disc_parts (S : WholeMainData d) (L : LimitCoeffsRd d) (m N : ℕ)
    (h : coeffDiscrepancyRd S L m N ≠ ⊤) :
    |2 * S.qN N - 2 * L.invβstar| ≤ (coeffDiscrepancyRd S L m N).toReal ∧
      ∀ r ∈ Set.Icc (0 : ℝ) S.T, ∀ x, jbracket x ^ ((d : ℝ) + 3) * |S.ρ N r x - L.ρ r x| ≤
        (coeffDiscrepancyRd S L m N).toReal := by
  set Δ := coeffDiscrepancyRd S L m N with hΔ
  have hΔ' : Δ = ENNReal.ofReal (|S.invβ N - L.invβ| + |2 * S.qN N - 2 * L.invβstar| + |S.AN N - L.A|) +
      ⨆ r : Set.Icc (0 : ℝ) S.T, coeffNormE d S.s m (S.ρ N r - L.ρ r) := rfl
  have hnn : 0 ≤ |S.invβ N - L.invβ| + |2 * S.qN N - 2 * L.invβstar| + |S.AN N - L.A| := by positivity
  refine ⟨?_, fun r hr x => ?_⟩
  · have h1 : ENNReal.ofReal (|S.invβ N - L.invβ| + |2 * S.qN N - 2 * L.invβstar| + |S.AN N - L.A|) ≤ Δ := by
      rw [hΔ']; exact le_self_add
    have h2 := ENNReal.toReal_mono h h1
    rw [ENNReal.toReal_ofReal hnn] at h2
    have := abs_nonneg (S.invβ N - L.invβ)
    have := abs_nonneg (S.AN N - L.A)
    linarith
  · have h1 : coeffNormE d S.s m (S.ρ N r - L.ρ r) ≤ Δ := by
      refine le_trans ?_ (le_trans (le_iSup (fun r : Set.Icc (0 : ℝ) S.T =>
        coeffNormE d S.s m (S.ρ N r - L.ρ r)) ⟨r, hr⟩) ?_)
      · exact le_rfl
      · rw [hΔ']; exact le_add_self
    have h2 : weightedSupE (m + 2) ((d : ℝ) + 3) (S.ρ N r - L.ρ r) ≤ Δ := by
      refine le_trans ?_ h1
      unfold coeffNormE
      exact le_trans le_add_self le_self_add
    have h3 : weightedSupE (m + 2) ((d : ℝ) + 3) (S.ρ N r - L.ρ r) ≤ ENNReal.ofReal Δ.toReal :=
      h2.trans (ENNReal.ofReal_toReal h).ge
    have := HRS.MS.SuppU15.u15_weighted_zero h3 x
    rw [max_eq_left ENNReal.toReal_nonneg] at this
    simpa using this

theorem sa26_iter_one_le_cbNorm {f : Euc d → ℝ} {j : ℕ} (hj : 1 ≤ j) (hf : MemCb j f) (x : Euc d) :
    ‖iteratedFDeriv ℝ 1 f x‖ ≤ cbNorm j f := by
  have h0 : ‖iteratedFDeriv ℝ 1 f x‖ ≤ ⨆ w : Euc d, ‖iteratedFDeriv ℝ 1 f w‖ :=
    le_ciSup (hf.2 1 hj) x
  refine h0.trans ?_
  unfold cbNorm
  exact Finset.single_le_sum (f := fun l => ⨆ w : Euc d, ‖iteratedFDeriv ℝ l f w‖)
    (fun l _ => Real.iSup_nonneg fun w => norm_nonneg _) (Finset.mem_range.2 (by omega))

end Aux7

end HRS.MS.PathFidi
