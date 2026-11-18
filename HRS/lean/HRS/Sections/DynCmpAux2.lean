import HRS.Sections.DynCmpAux1

/-!
# DYNCMP: Theorem 5.4 `dynamic_comparison`, step (2): the commutator identification and the remainder bound

* `dyncmp_fluc_eq`: for gradient dynamics (`D.M = -1`), `flucInteraction D ψ X ρ = - F_N^{h_{∇ψ}}(X, μ)` with
  `h_v = commKernel (∇g) v` (`N:eq:commutator`), pointwise in the configuration `X`.
* `dyncmp_pair_moment`, `dyncmp_fluc_moment`: the `r`-uniform pair-entropy bound `N:eq:pair-entropy` for the
  commutator kernel of an `L`-Lipschitz field: `E_ν[N |F_N^{h_v}|] ≤ C (H(ν|Q^r) + Nδ_N)`.
-/

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS

variable {d N : ℕ}

theorem dyncmp_interKernel_eq_neg_comm {D : DynData d} (hM : D.M = -1) (ψ : Torus d → ℝ) (x y : Torus d) :
    interKernel D ψ x y = -commKernel (periodicRieszGrad d D.s) (Torus.grad ψ) x y := by
  unfold interKernel commKernel
  by_cases hxy : x = y
  · simp [hxy]
  · simp only [hxy, if_false, hM, mova_matVec_neg_one, inner_neg_right]

theorem dyncmp_commKernel_symm {D : DynData d} (hM : D.M = -1) (ψ : Torus d → ℝ) (x y : Torus d) :
    commKernel (periodicRieszGrad d D.s) (Torus.grad ψ) y x =
      commKernel (periodicRieszGrad d D.s) (Torus.grad ψ) x y := by
  have h1 := dyncmp_interKernel_eq_neg_comm hM ψ y x
  have h2 := dyncmp_interKernel_eq_neg_comm hM ψ x y
  have h3 := interKernel_symm D ψ x y
  linarith


theorem dyncmp_fluc_eq (hd : 1 ≤ d) {D : DynData d} (hM : D.M = -1) {ψ : Torus d → ℝ}
    (hψ : Torus.IsCk 2 ψ) {ρ : Torus d → ℝ} {B : ℝ} (hB : ∀ x, ρ x ≤ B) (hN : 0 < N)
    (X : Config d N) :
    flucInteraction D ψ X ρ =
      -modulatedEnergy (commKernel (periodicRieszGrad d D.s) (Torus.grad ψ)) X (withDensityReal ρ) := by
  set K := commKernel (periodicRieszGrad d D.s) (Torus.grad ψ) with hK
  have hKi : ∀ x y, interKernel D ψ x y = -K x y := dyncmp_interKernel_eq_neg_comm hM ψ
  have hKs : ∀ x y, K y x = K x y := dyncmp_commKernel_symm hM ψ
  have hKd : ∀ x, K x x = 0 := fun x => by simp [hK, commKernel]
  have hint : ∀ x, Integrable (fun y => interKernel D ψ x y) (withDensityReal ρ) := fun x =>
    integrable_interKernel hd hψ hB x
  have e1 : interactionPairing D ψ (empirical X) (empirical X) =
      -((1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, (N : ℝ)⁻¹ * ∑ j, K (X i) (X j))) := by
    rw [interactionPairing_empirical hN X]
    simp only [hKi, Finset.sum_neg_distrib, mul_neg]
  have e2 : interactionPairing D ψ (empirical X) (withDensityReal ρ) =
      -((1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, ∫ y, K (X i) y ∂(withDensityReal ρ))) := by
    show (1 / 2 : ℝ) * ∫ x, ∫ y, interKernel D ψ x y ∂(withDensityReal ρ) ∂(empirical X) = _
    have := pair_empirical hN X (fun x => ∫ y, interKernel D ψ x y ∂(withDensityReal ρ))
    unfold pair at this
    rw [this]
    simp only [hKi, integral_neg, Finset.sum_neg_distrib, mul_neg]
  have e3 : interactionPairing D ψ (withDensityReal ρ) (empirical X) =
      -((1 / 2 : ℝ) * ((N : ℝ)⁻¹ * ∑ i, ∫ y, K (X i) y ∂(withDensityReal ρ))) := by
    show (1 / 2 : ℝ) * ∫ x, ∫ y, interKernel D ψ x y ∂(empirical X) ∂(withDensityReal ρ) = _
    have h1 : ∀ x, ∫ y, interKernel D ψ x y ∂(empirical X) = (N : ℝ)⁻¹ * ∑ j, interKernel D ψ x (X j) :=
      fun x => pair_empirical hN X _
    simp only [h1]
    rw [integral_const_mul, integral_finset_sum]
    · simp only [hKi, integral_neg, Finset.sum_neg_distrib, mul_neg]
      congr 3
      refine Finset.sum_congr rfl fun i _ => ?_
      refine integral_congr_ae (Filter.Eventually.of_forall fun y => ?_)
      exact hKs _ _
    · intro j _
      exact (hint (X j)).congr (Filter.Eventually.of_forall fun x => (interKernel_symm D ψ (X j) x).symm)
  have e4 : interactionPairing D ψ (withDensityReal ρ) (withDensityReal ρ) =
      -((1 / 2 : ℝ) * ∫ x, ∫ y, K x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)) := by
    show (1 / 2 : ℝ) * ∫ x, ∫ y, interKernel D ψ x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) = _
    simp only [hKi, integral_neg, mul_neg]
  have hS : ∀ i, ∑ j, K (X i) (X j) = ∑ j ∈ Finset.univ.erase i, K (X i) (X j) := by
    intro i
    rw [← Finset.add_sum_erase _ _ (Finset.mem_univ i), hKd, zero_add]
  unfold flucInteraction modulatedEnergy
  rw [e1, e2, e3, e4]
  simp only [hS, ← Finset.mul_sum]
  have hN0 : (N : ℝ) ≠ 0 := by exact_mod_cast hN.ne'
  field_simp
  ring


theorem dyncmp_commKernel_symm_gen {s : ℝ} (hsd : s < d) (v : Torus d → Euc d) (x y : Torus d) :
    commKernel (periodicRieszGrad d s) v x y = commKernel (periodicRieszGrad d s) v y x := by
  unfold commKernel
  by_cases hxy : x = y
  · simp [hxy]
  · have hyx : ¬ y = x := fun h => hxy h.symm
    simp only [hxy, hyx, if_false]
    rw [← neg_sub x y, ← neg_sub (v x) (v y), KernelGrad.periodicRieszGrad_neg_of_lt hsd, inner_neg_neg]

theorem dyncmp_commKernel_measurable {G v : Torus d → Euc d} (hG : Measurable G) (hv : Measurable v) :
    Measurable (Function.uncurry (commKernel G v)) := by
  unfold commKernel
  refine Measurable.ite (measurableSet_eq_fun measurable_fst measurable_snd) measurable_const ?_
  exact ((hv.comp measurable_fst).sub (hv.comp measurable_snd)).inner
    (hG.comp (measurable_fst.sub measurable_snd))

/-- The pair-entropy bound `N:eq:pair-entropy` for the commutator kernel of a Lipschitz field, uniformly in `r ∈ [0,T]`. -/
theorem dyncmp_pair_moment (hd : 1 ≤ d) {D : DynData d} {T c₀ Λ₂ : ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : MovTraj D T ρ) (hc₀ : 0 < c₀) (hlow : ∀ r ∈ Set.Icc 0 T, ∀ x, c₀ ≤ ρ r x)
    (hΛ : ∀ r ∈ Set.Icc 0 T, Torus.cbNorm 2 (ρ r) ≤ Λ₂) {L : ℝ} (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ r ∈ Set.Icc 0 T, ∀ v : Torus d → Euc d, IsLipschitzVF L v →
      Measurable (fun X : Config d N => modulatedEnergy (commKernel (periodicRieszGrad d D.s) v) X
        (withDensityReal (ρ r))) ∧
      ∀ ν : Measure (Config d N), IsProbabilityMeasure ν →
        relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ r) ≠ ⊤ →
        ∫⁻ X, ENNReal.ofReal ((N : ℝ) * |modulatedEnergy (commKernel (periodicRieszGrad d D.s) v) X
            (withDensityReal (ρ r))|) ∂ν ≤ ENNReal.ofReal C *
          (relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ r) + ENNReal.ofReal (N * deltaN d D.s N)) ∧
        ∫ X, (N : ℝ) * |modulatedEnergy (commKernel (periodicRieszGrad d D.s) v) X
            (withDensityReal (ρ r))| ∂ν ≤
          C * ((relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ r)).toReal +
            N * deltaN d D.s N) := by
  have hβ : 0 < D.invβ⁻¹ := inv_pos.2 htr.pos_temp
  obtain ⟨cstar, A, hA0, hw, hg0, hdom⟩ := movsx_hdom hd D.hs0 D.hsd
  obtain ⟨θ₀, C, hθ₀, hC, hP⟩ := movT_pressure_two_sided_C2_proof hd D.s D.hs0 D.hsd cstar hw D.invβ⁻¹
    D.invβ⁻¹ hβ c₀ hc₀ Λ₂ (A * L)
  set Cp : ℝ := (D.invβ⁻¹ * θ₀)⁻¹ * (2 * C + 1) with hCp
  have hCp0 : 0 ≤ Cp := by rw [hCp]; positivity
  refine ⟨Cp, hCp0, ?_⟩
  intro N hN r hr v hv
  have hρ := htr.mf.density r hr
  haveI := isProb_withDensityReal hρ
  have hcont : Continuous (ρ r) := b15_continuous_of_isCk (htr.ck r hr)
  obtain ⟨Mρ, hMρ0, hMρ⟩ := exists_abs_bound hcont
  have hρΛ : ∀ x, ρ r x ≤ Mρ := fun x => (le_abs_self _).trans (hMρ x)
  have hgm : Measurable (periodicRiesz d D.s) := CoercAux.measurable_periodicRiesz_one hd D.hs0 D.hsd
  have hvc : Continuous v := Commutator.IsLipschitzVF.continuous hL hv
  have hhm : Measurable (Function.uncurry (commKernel (periodicRieszGrad d D.s) v)) :=
    dyncmp_commKernel_measurable (KernelGrad.measurable_periodicRieszGrad (by exact_mod_cast D.hsd)) hvc.measurable
  have hdomv : ∀ x y, |commKernel (periodicRieszGrad d D.s) v x y| ≤
      (A * L) * (periodicRiesz d D.s (x - y) + cstar) := fun x y => hdom L v hL hv x y
  obtain ⟨hgR, hhR⟩ := rowOK_g_h hd D.s D.hs0 D.hsd cstar hw (A * L) hMρ0 hρΛ hhm hdomv
  have hsymm : ∀ x y, commKernel (periodicRieszGrad d D.s) v x y = commKernel (periodicRieszGrad d D.s) v y x :=
    fun x y => dyncmp_commKernel_symm_gen D.hsd v x y
  refine ⟨measurable_modulatedEnergy hhR, fun ν hν hHfin => ?_⟩
  have hPt : ∀ θ : ℝ, |θ| ≤ θ₀ →
      ENNReal.ofReal (Real.exp (-(C * N * deltaN d D.s N))) ≤
          ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
            modulatedEnergy (fun x y => periodicRiesz d D.s (x - y) -
              θ * commKernel (periodicRieszGrad d D.s) v x y) X (withDensityReal (ρ r)))) ∂(Measure.pi fun _ : Fin N => withDensityReal (ρ r)) ∧
        ∫⁻ X : Config d N, ENNReal.ofReal (Real.exp (-D.invβ⁻¹ * N *
            modulatedEnergy (fun x y => periodicRiesz d D.s (x - y) -
              θ * commKernel (periodicRieszGrad d D.s) v x y) X (withDensityReal (ρ r)))) ∂(Measure.pi fun _ : Fin N => withDensityReal (ρ r)) ≤
          ENNReal.ofReal (Real.exp (C * N * deltaN d D.s N)) := fun θ hθ =>
    hP (ρ r) hρ (htr.ck r hr) (hlow r hr) (hΛ r hr) (commKernel (periodicRieszGrad d D.s) v) hhm hsymm hdomv
      N hN D.invβ⁻¹ ⟨le_rfl, le_rfl⟩ θ hθ
  have hδ : 1 ≤ (N : ℝ) * deltaN d D.s N := one_le_mul_deltaN D.hs0 N (by omega)
  have hmom := moments_of_pressure (N := N) hgR hhR hδ hC hθ₀ hβ (le_refl _) hPt
  have hQeq : movT_Q (periodicRiesz d D.s) D N ρ r =
      modulatedGibbs (periodicRiesz d D.s) N D.invβ⁻¹ (withDensityReal (ρ r)) := rfl
  rw [hQeq] at hHfin ⊢
  have hm := hmom.2 ν hν (lt_top_iff_ne_top.2 hHfin)
  refine ⟨hm, ?_⟩
  set Fm : Config d N → ℝ := fun X => modulatedEnergy (commKernel (periodicRieszGrad d D.s) v) X
    (withDensityReal (ρ r)) with hFm
  have hFmeas : Measurable Fm := measurable_modulatedEnergy hhR
  have hnn : 0 ≤ᵐ[ν] fun X => (N : ℝ) * |Fm X| := Eventually.of_forall fun X => by positivity
  have hae : AEStronglyMeasurable (fun X => (N : ℝ) * |Fm X|) ν :=
    (measurable_const.mul (hFmeas.norm)).aestronglyMeasurable
  rw [integral_eq_lintegral_of_nonneg_ae hnn hae]
  have hle := ENNReal.toReal_mono (by
    refine ENNReal.mul_ne_top ENNReal.ofReal_ne_top (ENNReal.add_ne_top.2 ⟨hHfin, ENNReal.ofReal_ne_top⟩))
    hm
  refine hle.trans (le_of_eq ?_)
  have hNδ : 0 ≤ (N : ℝ) * deltaN d D.s N := by linarith
  rw [ENNReal.toReal_mul, ENNReal.toReal_ofReal hCp0, ENNReal.toReal_add hHfin ENNReal.ofReal_ne_top,
    ENNReal.toReal_ofReal hNδ]


theorem dyncmp_lip_grad {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) :
    IsLipschitzVF (d * Torus.cbNorm 2 ψ) (Torus.grad ψ) := by
  intro x y
  have hsum : ‖Torus.grad ψ x - Torus.grad ψ y‖ ≤ ∑ j : Fin d, Torus.cbNorm 2 ψ * KernelGrad.tdist x y := by
    refine (mova_norm_le_sum _).trans (Finset.sum_le_sum fun j _ => ?_)
    rw [PiLp.sub_apply, mova_grad_apply, mova_grad_apply]
    exact mova_isLipschitz_partialDeriv hψ j x y
  rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul] at hsum
  calc _ ≤ _ := hsum
    _ = _ := by ring

theorem dyncmp_norm_grad_le {ψ : Torus d → ℝ} (hψ : Torus.IsCk 2 ψ) (x : Torus d) :
    ‖Torus.grad ψ x‖ ≤ d * Torus.cbNorm 2 ψ := by
  refine (mova_norm_le_sum _).trans ?_
  calc ∑ j : Fin d, |(Torus.grad ψ x).ofLp j| ≤ ∑ _j : Fin d, Torus.cbNorm 2 ψ :=
        Finset.sum_le_sum fun j _ => by rw [mova_grad_apply]; exact mova_abs_partialDeriv_le hψ j x
    _ = d * Torus.cbNorm 2 ψ := by simp

/-- The remainder bound: `E_ν[N |flucInteraction|] ≤ C (H(ν|Q^r) + Nδ_N)`, uniformly in `r ∈ [0,T]` and in the
tests with `∇ψ` `L`-Lipschitz. -/
theorem dyncmp_fluc_moment (hd : 1 ≤ d) {D : DynData d} {T c₀ Λ₂ : ℝ} {ρ : ℝ → Torus d → ℝ}
    (htr : MovTraj D T ρ) (hc₀ : 0 < c₀) (hlow : ∀ r ∈ Set.Icc 0 T, ∀ x, c₀ ≤ ρ r x)
    (hΛ : ∀ r ∈ Set.Icc 0 T, Torus.cbNorm 2 (ρ r) ≤ Λ₂) {L : ℝ} (hL : 0 ≤ L) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ N : ℕ, 2 ≤ N → ∀ r ∈ Set.Icc 0 T, ∀ ψ : Torus d → ℝ, Torus.IsCk 2 ψ →
      IsLipschitzVF L (Torus.grad ψ) →
      ∀ ν : Measure (Config d N), IsProbabilityMeasure ν →
        relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ r) ≠ ⊤ →
        ∫⁻ X, ENNReal.ofReal ((N : ℝ) * |flucInteraction D ψ X (ρ r)|) ∂ν ≤ ENNReal.ofReal C *
          (relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ r) + ENNReal.ofReal (N * deltaN d D.s N)) ∧
        ∫ X, (N : ℝ) * |flucInteraction D ψ X (ρ r)| ∂ν ≤
          C * ((relEntropy ν (movT_Q (periodicRiesz d D.s) D N ρ r)).toReal + N * deltaN d D.s N) := by
  obtain ⟨C, hC0, hC⟩ := dyncmp_pair_moment hd htr hc₀ hlow hΛ hL
  refine ⟨C, hC0, fun N hN r hr ψ hψ hlip ν hν hH => ?_⟩
  have hcont : Continuous (ρ r) := b15_continuous_of_isCk (htr.ck r hr)
  obtain ⟨Mρ, -, hMρ⟩ := exists_abs_bound hcont
  have hρΛ : ∀ x, ρ r x ≤ Mρ := fun x => (le_abs_self _).trans (hMρ x)
  obtain ⟨-, hCν⟩ := hC N hN r hr (Torus.grad ψ) hlip
  obtain ⟨h1, h2⟩ := hCν ν hν hH
  have hpt : ∀ X : Config d N, |flucInteraction D ψ X (ρ r)| = |modulatedEnergy
      (commKernel (periodicRieszGrad d D.s) (Torus.grad ψ)) X (withDensityReal (ρ r))| := fun X => by
    rw [dyncmp_fluc_eq hd htr.gradient hψ hρΛ (by omega) X, abs_neg]
  simp only [hpt]
  exact ⟨h1, h2⟩

end HRS

end
