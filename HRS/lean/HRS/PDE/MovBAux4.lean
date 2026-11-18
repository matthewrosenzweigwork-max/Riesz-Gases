import HRS.PDE.MovBAux3

/-!
# MOVB, part 4: analysis of the regularised source `S^M_r(X)`

Joint continuity on `[0,T] × Config`, boundedness, continuity of `r ↦ ∫ S_r d(law_r)`, and (`movb_srcReg_withV_diff`) the
uniform estimate `|S[V_k] - S[V]| ≤ C ε_k` for the replacement of `V` by `V_k`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set InformationTheory
open scoped ENNReal NNReal BigOperators

namespace HRS

variable {d N : ℕ}

theorem movb_partition_toReal (invβ : ℝ) {U : Config d N → ℝ} (hU : Continuous U) :
    (b15c_gibbsPartitionGen invβ U).toReal = ∫ X, b15c_gibbsWeightGen invβ U X := by
  unfold b15c_gibbsPartitionGen
  exact (integral_eq_lintegral_of_nonneg_ae (Eventually.of_forall fun X => (Real.exp_pos _).le)
    (b15e_weight_continuous invβ hU).aestronglyMeasurable).symm

theorem movb_integral_gibbsRef (invβ : ℝ) {U : Config d N → ℝ} (hU : Continuous U)
    (f : Config d N → ℝ) :
    ∫ X, f X ∂(b15c_gibbsRefGen invβ U) =
      (∫ X, b15c_gibbsWeightGen invβ U X * f X) / ∫ X, b15c_gibbsWeightGen invβ U X := by
  have hw := b15e_weight_continuous invβ hU
  have hZ := movb_partition_toReal invβ hU
  unfold b15c_gibbsRefGen
  rw [integral_smul_measure, mova_integral_withDensity_real _ hw.measurable
    (fun X => (Real.exp_pos _).le), ENNReal.toReal_inv, hZ]
  simp [div_eq_inv_mul]

theorem movb_cont_gibbs_integral {ι : Type*} [TopologicalSpace ι] [FirstCountableTopology ι]
    [LocallyCompactSpace ι] (invβ : ℝ) {U : ι → Config d N → ℝ}
    (hU : Continuous fun p : ι × Config d N => U p.1 p.2) {f : ι → Config d N → ℝ}
    (hf : Continuous fun p : ι × Config d N => f p.1 p.2) :
    Continuous fun i => ∫ X, f i X ∂(b15c_gibbsRefGen invβ (U i)) := by
  have hUi : ∀ i, Continuous (U i) := fun i => hU.comp (continuous_const.prodMk continuous_id)
  have hW : Continuous fun p : ι × Config d N => b15c_gibbsWeightGen invβ (U p.1) p.2 := by
    unfold b15c_gibbsWeightGen
    exact Real.continuous_exp.comp (continuous_const.mul hU)
  have e : (fun i => ∫ X, f i X ∂(b15c_gibbsRefGen invβ (U i))) = fun i =>
      (∫ X, b15c_gibbsWeightGen invβ (U i) X * f i X) / ∫ X, b15c_gibbsWeightGen invβ (U i) X :=
    funext fun i => movb_integral_gibbsRef invβ (hUi i) _
  rw [e]
  have h1 : Continuous fun i => ∫ X, b15c_gibbsWeightGen invβ (U i) X * f i X := by
    have := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Config d N)))
      (f := fun i X => b15c_gibbsWeightGen invβ (U i) X * f i X) (hW.mul hf) isCompact_univ
    simpa using this
  have h2 : Continuous fun i => ∫ X, b15c_gibbsWeightGen invβ (U i) X := by
    have := continuous_parametric_integral_of_continuous (μ := (volume : Measure (Config d N)))
      (f := fun i X => b15c_gibbsWeightGen invβ (U i) X) hW isCompact_univ
    simpa using this
  refine h1.div h2 fun i => ?_
  have hZ := movb_partition_toReal invβ (hUi i)
  rw [← hZ]
  exact (b15e_partition_toReal_pos invβ (hUi i)).ne'


theorem movb_cont_laplacian {T : ℝ} {f ft : ℝ → Torus d → ℝ} (hf : IsC12Test T f ft) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => Torus.laplacian (f p.1) p.2 := by
  apply d1_continuous_prod_of_lift (h := fun p : Set.Icc (0 : ℝ) T × Torus d => Torus.laplacian (f p.1) p.2)
  refine hf.continuous_laplacian_lift.congr fun p => ?_
  simp only [laplacian_mk]

theorem movb_cont_drift (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (hV2 : Torus.IsCk 2 D.V) (M : ℝ) (i : Fin N) :
    Continuous fun X : Config d N => b15d_configDriftReg (N := N) D M X i := by
  have hg := mova_continuous_gradGReg D M
  have hV := mova_continuous_grad (mova_isCk_one_of_two hV2)
  unfold b15d_configDriftReg
  simp only [hM, mova_matVec_neg_one]
  have hs : Continuous fun X : Config d N =>
      ∑ j ∈ Finset.univ.erase i, -Torus.grad (b15c_gReg d D.s M) (X i - X j) :=
    continuous_finsetSum _ fun j _ => (hg.comp ((continuous_apply i).sub (continuous_apply j))).neg
  exact (hs.const_smul (1 / (N : ℝ))).sub (hV.comp (continuous_apply i))

theorem movb_srcReg_formula (D : DynData d) (M : ℝ) {ρ ρt : ℝ → Torus d → ℝ} {r : ℝ}
    (hφ2 : Torus.IsCk 2 (movT_phi D M ρ r)) (X : Config d N) :
    movT_srcReg D N M ρ ρt r X =
      D.invβ * ∑ i, Torus.laplacian (movT_phi D M ρ r) (X i) +
        ∑ i, inner ℝ (Torus.grad (movT_phi D M ρ r) (X i)) (b15d_configDriftReg D M X i) +
        D.invβ * ∑ i, ‖Torus.grad (movT_phi D M ρ r) (X i)‖ ^ 2 -
        ∑ i, movT_phit D M ρ ρt r (X i) +
        ∫ Y, movT_psit D M ρ ρt r Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) := by
  have := mova_gen_sum D.invβ (b15d_configDriftReg (N := N) D M) hφ2 X
  unfold movT_srcReg movT_psi movT_psit
  rw [this]

theorem movb_cont_c (hN : 0 < N) (D : DynData d) (hκ : 0 < D.invβ) (hV2 : Torus.IsCk 2 D.V) (M : ℝ)
    {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ} (hρt : IsC12Test T ρ ρt)
    (hdens : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r))
    (hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ r x) :
    Continuous fun r : Set.Icc (0 : ℝ) T =>
      ∫ Y, movT_psit D M ρ ρt r Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) := by
  have hφ := movb_phi_isC12Test D hV2 M hρt hpos
  have hVc := mova_continuous_of_isCk hV2
  have hUc : Continuous (b15c_potentialReg (N := N) D M) := b15c_potentialReg_continuous D hVc M
  have hφjc : ∀ i : Fin N, Continuous fun p : Set.Icc (0 : ℝ) T × Config d N =>
      movT_phi D M ρ p.1 (p.2 i) := fun i =>
    hφ.continuous_f.comp (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))
  have hφtjc : ∀ i : Fin N, Continuous fun p : Set.Icc (0 : ℝ) T × Config d N =>
      movT_phit D M ρ ρt p.1 (p.2 i) := fun i =>
    hφ.cont_time_deriv.comp (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))
  have hcont := movb_cont_gibbs_integral (ι := Set.Icc (0 : ℝ) T) D.invβ
    (U := fun r X => b15c_potentialReg D M X - D.invβ * ∑ i, movT_phi D M ρ r (X i))
    (f := fun r X => ∑ i, movT_phit D M ρ ρt r (X i))
    ((hUc.comp continuous_snd).sub (continuous_const.mul (continuous_finsetSum _ fun i _ => hφjc i)))
    (continuous_finsetSum _ fun i _ => hφtjc i)
  refine hcont.congr fun r => ?_
  have hr := r.2
  have hρ2 := hρt.c2 r hr
  have hQ := movb_Q_eq_gibbs hN D hκ hV2 M (hdens r hr) (mova_continuous_of_isCk hρ2) (hpos r hr)
    (mova_continuous_of_isCk (mova_phi_isCk_two D M hρ2 (hpos r hr) hV2)) (fun x => rfl)
  show _ = ∫ Y, movT_psit D M ρ ρt r Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)
  unfold movT_Q
  rw [hQ]
  rfl

theorem movb_srcReg_cont (hN : 0 < N) (D : DynData d) (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ))
    (hκ : 0 < D.invβ) (hV2 : Torus.IsCk 2 D.V) (M : ℝ) {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ}
    (hρt : IsC12Test T ρ ρt) (hdens : ∀ r ∈ Set.Icc (0 : ℝ) T, IsProbDensity (ρ r))
    (hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ r x) :
    Continuous fun p : Set.Icc (0 : ℝ) T × Config d N => movT_srcReg D N M ρ ρt p.1 p.2 := by
  have hφ := movb_phi_isC12Test D hV2 M hρt hpos
  have hφ2 : ∀ r ∈ Set.Icc (0 : ℝ) T, Torus.IsCk 2 (movT_phi D M ρ r) := hφ.c2
  have hc := movb_cont_c hN D hκ hV2 M hρt hdens hpos
  have hcomp : ∀ (G : Set.Icc (0 : ℝ) T × Torus d → ℝ), Continuous G →
      Continuous fun p : Set.Icc (0 : ℝ) T × Config d N => ∑ i, G (p.1, p.2 i) := fun G hG =>
    continuous_finsetSum _ fun i _ =>
      hG.comp (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))
  have hL := hcomp _ (movb_cont_laplacian hφ)
  have hgrad := d3a_continuous_grad hφ
  have hG2 : Continuous fun p : Set.Icc (0 : ℝ) T × Torus d => ‖Torus.grad (movT_phi D M ρ p.1) p.2‖ ^ 2 :=
    hgrad.norm.pow 2
  have hG2' := hcomp _ hG2
  have hT := hcomp _ hφ.cont_time_deriv
  have hI : Continuous fun p : Set.Icc (0 : ℝ) T × Config d N =>
      ∑ i, inner ℝ (Torus.grad (movT_phi D M ρ p.1) (p.2 i)) (b15d_configDriftReg D M p.2 i) :=
    continuous_finsetSum _ fun i _ =>
      (hgrad.comp (continuous_fst.prodMk ((continuous_apply i).comp continuous_snd))).inner
        ((movb_cont_drift D hM hV2 M i).comp continuous_snd)
  have h1 := (continuous_const (y := D.invβ)).mul hL
  have h3 := (continuous_const (y := D.invβ)).mul hG2'
  have := (((h1.add hI).add h3).sub hT).add (hc.comp continuous_fst)
  refine this.congr fun p => ?_
  exact (movb_srcReg_formula D M (hφ2 p.1 p.1.2) p.2).symm


theorem movb_regProcess_apply {Ω : Type*} (Y : ℝ → Ω → (Fin N → Euc d)) (t : ℝ≥0) (ω : Ω) :
    b15c_regProcess Y t ω = fun i => Torus.mk (Y (t : ℝ) ω i) := rfl

/-- Continuity in `r ∈ [0,T]` of `∫ S_r d(law_r)` for a jointly continuous `S` and a process with continuous paths. -/
theorem movb_cont_integral {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω}
    [IsProbabilityMeasure P] {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    {b : ℝ → (Fin N → Euc d) → (Fin N → Euc d)} {σ : (Fin N × Fin d) → (Fin N → Euc d)}
    {Y₀ : Ω → Fin N → Euc d} {Y : ℝ → Ω → (Fin N → Euc d)}
    (hY : IsAdditiveSDESolution P ℱ W' b σ Y₀ (fun _ => ⊤) Y) {T : ℝ} (hT : 0 ≤ T)
    {S : ℝ → Config d N → ℝ} (hS : Continuous fun p : Set.Icc (0 : ℝ) T × Config d N => S p.1 p.2) :
    Continuous fun r : Set.Icc (0 : ℝ) T => ∫ Z, S r Z ∂(selectedLaw P (b15c_regProcess Y) r) := by
  obtain ⟨B, hB⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) T × Config d N)).exists_bound_of_continuousOn
    hS.continuousOn
  have hSi : ∀ r : Set.Icc (0 : ℝ) T, Continuous (S r) := fun r =>
    hS.comp (continuous_const.prodMk continuous_id)
  have hmeas : ∀ s : ℝ≥0, Measurable (b15c_regProcess Y s) := fun s => b15c_regProcess_measurable hY s
  have e : ∀ r : Set.Icc (0 : ℝ) T, ∫ Z, S r Z ∂(selectedLaw P (b15c_regProcess Y) r) =
      ∫ ω, S r (fun i => Torus.mk (Y (r : ℝ) ω i)) ∂P := by
    intro r
    unfold selectedLaw
    rw [show law P (b15c_regProcess Y (Real.toNNReal (r : ℝ))) =
      P.map (b15c_regProcess Y (Real.toNNReal (r : ℝ))) from rfl,
      integral_map (hmeas _).aemeasurable (hSi r).aestronglyMeasurable]
    refine integral_congr_ae (Eventually.of_forall fun ω => ?_)
    simp only [movb_regProcess_apply, Real.coe_toNNReal _ r.2.1]
  simp_rw [e]
  have hmk : ∀ ω, Continuous fun r : Set.Icc (0 : ℝ) T => (fun i => Torus.mk (Y (r : ℝ) ω i) : Config d N) :=
    fun ω => continuous_pi fun i => Torus.continuous_mk.comp
      (((continuous_apply i).comp_continuousOn (hY.cont ω T hT (WithTop.coe_lt_top T))).comp_continuous
        continuous_subtype_val (fun r => r.2))
  refine continuous_of_dominated (bound := fun _ => max B 0) (fun r => ?_) (fun r => ?_)
    (integrable_const _) (Eventually.of_forall fun ω => ?_)
  · have : Measurable fun ω => (fun i => Torus.mk (Y (r : ℝ) ω i) : Config d N) := by
      have h := hmeas (Real.toNNReal (r : ℝ))
      have e2 : b15c_regProcess Y (Real.toNNReal (r : ℝ)) =
          fun ω i => Torus.mk (Y (r : ℝ) ω i) := by
        funext ω; rw [movb_regProcess_apply, Real.coe_toNNReal _ r.2.1]
      rwa [e2] at h
    exact ((hSi r).measurable.comp this).aestronglyMeasurable
  · refine Eventually.of_forall fun ω => ?_
    have := hB (r, fun i => Torus.mk (Y (r : ℝ) ω i)) (Set.mem_univ _)
    rw [Real.norm_eq_abs] at this ⊢
    exact this.trans (le_max_left _ _)
  · exact hS.comp (continuous_id.prodMk (hmk ω))


theorem movb_particle_identity (g δ b : Euc d) {κ β : ℝ} (h : κ * β = 1) :
    inner ℝ (g + β • δ) (b - δ) - inner ℝ g b + κ * (‖g + β • δ‖ ^ 2 - ‖g‖ ^ 2) =
      inner ℝ g δ + β * inner ℝ δ b := by
  have e1 : ‖g + β • δ‖ ^ 2 = ‖g‖ ^ 2 + 2 * β * inner ℝ g δ + β ^ 2 * ‖δ‖ ^ 2 := by
    rw [norm_add_sq_real, inner_smul_right, norm_smul, mul_pow, Real.norm_eq_abs, sq_abs]; ring
  have e2 : inner ℝ (g + β • δ) (b - δ) = inner ℝ g b - inner ℝ g δ + β * inner ℝ δ b -
      β * ‖δ‖ ^ 2 := by
    rw [inner_add_left, inner_sub_right, inner_sub_right, inner_smul_left, inner_smul_left,
      real_inner_self_eq_norm_sq]
    simp; ring
  rw [e1, e2]
  have : κ * (2 * β * inner ℝ g δ + β ^ 2 * ‖δ‖ ^ 2) = 2 * inner ℝ g δ + β * ‖δ‖ ^ 2 := by
    have h2 : κ * β ^ 2 = β := by rw [pow_two, ← mul_assoc, h, one_mul]
    linear_combination (2 * inner ℝ g δ) * h + ‖δ‖ ^ 2 * h2
  linear_combination this

theorem movb_lap_add_smul {A B : Torus d → ℝ} (hA : Torus.IsCk 2 A) (hB : Torus.IsCk 2 B) (c : ℝ)
    (x : Torus d) :
    Torus.laplacian (fun y => A y + c * B y) x = Torus.laplacian A x + c * Torus.laplacian B x := by
  have hAB := mova_isCk_add hA (mova_isCk_const_mul c hB)
  rw [mova_laplacian_eq_sum hAB, mova_laplacian_eq_sum hA, mova_laplacian_eq_sum hB, Finset.mul_sum,
    ← Finset.sum_add_distrib]
  refine Finset.sum_congr rfl fun j _ => ?_
  have h1 : Torus.partialDeriv j (fun y => A y + c * B y) =
      fun y => Torus.partialDeriv j A y + c * Torus.partialDeriv j B y := by
    funext y
    rw [mova_partialDeriv_add j (mova_isCk_one_of_two hA) (mova_isCk_one_of_two (mova_isCk_const_mul c hB)),
      mova_partialDeriv_const_mul j (mova_isCk_one_of_two hB)]
  rw [h1, mova_partialDeriv_add j (mova_isCk_partialDeriv hA j)
    (mova_isCk_const_mul c (mova_isCk_partialDeriv hB j)) x,
    mova_partialDeriv_const_mul j (mova_isCk_partialDeriv hB j)]

theorem movb_grad_add_smul {A B : Torus d → ℝ} (hA : Torus.IsCk 1 A) (hB : Torus.IsCk 1 B) (c : ℝ)
    (x : Torus d) :
    Torus.grad (fun y => A y + c * B y) x = Torus.grad A x + c • Torus.grad B x := by
  ext j
  rw [mova_grad_apply, mova_partialDeriv_add j hA (mova_isCk_const_mul c hB),
    mova_partialDeriv_const_mul j hB]
  simp [mova_grad_apply]


theorem movb_srcReg_withV_diff (hN : 0 < N) (D : DynData d)
    (hM : D.M = -(1 : Matrix (Fin d) (Fin d) ℝ)) (hκ : 0 < D.invβ) (hV2 : Torus.IsCk 2 D.V) (M : ℝ)
    {T : ℝ} {ρ ρt : ℝ → Torus d → ℝ} (hρt : IsC12Test T ρ ρt)
    (hpos : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ x, 0 < ρ r x) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (V' : Torus d → ℝ), Torus.IsCk 2 V' → ∀ ε : ℝ, 0 ≤ ε →
      (∀ x, ‖Torus.grad V' x - Torus.grad D.V x‖ ≤ ε) →
      (∀ x, |Torus.laplacian V' x - Torus.laplacian D.V x| ≤ ε) →
      ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ X : Config d N,
        |movT_srcReg (b15e_withV D V') N M ρ ρt r X - movT_srcReg D N M ρ ρt r X| ≤ C * ε := by
  have hφ := movb_phi_isC12Test D hV2 M hρt hpos
  obtain ⟨Bg, hBg⟩ := (isCompact_univ (X := Set.Icc (0 : ℝ) T × Torus d)).exists_bound_of_continuousOn
    (d3a_continuous_grad hφ).continuousOn
  have hbc : Continuous fun X : Config d N => b15d_configDriftReg (N := N) D M X :=
    continuous_pi fun i => movb_cont_drift D hM hV2 M i
  obtain ⟨Bb, hBb⟩ := (isCompact_univ (X := Config d N)).exists_bound_of_continuousOn hbc.continuousOn
  set β := D.invβ⁻¹ with hβ
  have hβpos : 0 < β := inv_pos.2 hκ
  have hκβ : D.invβ * β = 1 := mul_inv_cancel₀ hκ.ne'
  refine ⟨N * (1 + max Bg 0 + β * max Bb 0), by positivity, fun V' hV' ε hε hgrad hlap r hr X => ?_⟩
  set D' := b15e_withV D V' with hD'
  set B : Torus d → ℝ := fun y => V' y + (-1) * D.V y with hB
  have hB2 : Torus.IsCk 2 B := mova_isCk_add hV' (mova_isCk_const_mul (-1) hV2)
  have hφ2 : Torus.IsCk 2 (movT_phi D M ρ r) := hφ.c2 r hr
  have hφ'eq : movT_phi D' M ρ r = fun y => movT_phi D M ρ r y + β * B y := by
    funext y; simp only [movT_phi, hD', b15e_withV, hB, hβ]; ring
  have hφ'2 : Torus.IsCk 2 (movT_phi D' M ρ r) := by
    rw [hφ'eq]; exact mova_isCk_add hφ2 (mova_isCk_const_mul _ hB2)
  rw [movb_srcReg_formula D' M hφ'2 X, movb_srcReg_formula D M hφ2 X]
  have hphit : ∀ i, movT_phit D' M ρ ρt r (X i) = movT_phit D M ρ ρt r (X i) := fun i => rfl
  have hc : (∫ Y, movT_psit D' M ρ ρt r Y ∂(movT_Q (b15c_gReg d D'.s M) D' N ρ r)) =
      ∫ Y, movT_psit D M ρ ρt r Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r) := rfl
  simp only [hphit, hc]
  have hD'κ : D'.invβ = D.invβ := rfl
  simp only [hD'κ]
  set g : Fin N → Euc d := fun i => Torus.grad (movT_phi D M ρ r) (X i) with hg
  set δ : Fin N → Euc d := fun i => Torus.grad V' (X i) - Torus.grad D.V (X i) with hδ
  set b : Fin N → Euc d := fun i => b15d_configDriftReg D M X i with hb
  have hgradB : ∀ y, Torus.grad B y = Torus.grad V' y - Torus.grad D.V y := by
    intro y
    rw [hB, movb_grad_add_smul (mova_isCk_one_of_two hV') (mova_isCk_one_of_two hV2)]
    simp [sub_eq_add_neg]
  have hlapB : ∀ y, Torus.laplacian B y = Torus.laplacian V' y - Torus.laplacian D.V y := by
    intro y
    rw [hB, movb_lap_add_smul hV' hV2]; ring
  have hb' : ∀ i, b15d_configDriftReg D' M X i = b i - δ i := by
    intro i
    simp only [hb, hδ, b15d_configDriftReg, hD', b15e_withV]
    abel
  have hgr' : ∀ i, Torus.grad (movT_phi D' M ρ r) (X i) = g i + β • δ i := by
    intro i
    rw [hφ'eq, movb_grad_add_smul (mova_isCk_one_of_two hφ2) (mova_isCk_one_of_two hB2), hgradB]
  have hlap' : ∀ i, Torus.laplacian (movT_phi D' M ρ r) (X i) =
      Torus.laplacian (movT_phi D M ρ r) (X i) +
        β * (Torus.laplacian V' (X i) - Torus.laplacian D.V (X i)) := by
    intro i
    rw [hφ'eq, movb_lap_add_smul hφ2 hB2, hlapB]
  have hterm : ∀ i, (D.invβ * Torus.laplacian (movT_phi D' M ρ r) (X i) +
        inner ℝ (Torus.grad (movT_phi D' M ρ r) (X i)) (b15d_configDriftReg D' M X i) +
        D.invβ * ‖Torus.grad (movT_phi D' M ρ r) (X i)‖ ^ 2) -
      (D.invβ * Torus.laplacian (movT_phi D M ρ r) (X i) +
        inner ℝ (Torus.grad (movT_phi D M ρ r) (X i)) (b15d_configDriftReg D M X i) +
        D.invβ * ‖Torus.grad (movT_phi D M ρ r) (X i)‖ ^ 2) =
      (Torus.laplacian V' (X i) - Torus.laplacian D.V (X i)) + inner ℝ (g i) (δ i) +
        β * inner ℝ (δ i) (b i) := by
    intro i
    rw [hlap' i, hgr' i, hb' i]
    have := movb_particle_identity (g i) (δ i) (b i) hκβ
    have e : D.invβ * β = 1 := hκβ
    simp only [hg, hb] at this ⊢
    linear_combination this + (Torus.laplacian V' (X i) - Torus.laplacian D.V (X i)) * e
  have hsum : (D.invβ * ∑ i, Torus.laplacian (movT_phi D' M ρ r) (X i) +
        ∑ i, inner ℝ (Torus.grad (movT_phi D' M ρ r) (X i)) (b15d_configDriftReg D' M X i) +
        D.invβ * ∑ i, ‖Torus.grad (movT_phi D' M ρ r) (X i)‖ ^ 2 -
        ∑ i, movT_phit D M ρ ρt r (X i) +
        ∫ Y, movT_psit D M ρ ρt r Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)) -
      (D.invβ * ∑ i, Torus.laplacian (movT_phi D M ρ r) (X i) +
        ∑ i, inner ℝ (Torus.grad (movT_phi D M ρ r) (X i)) (b15d_configDriftReg D M X i) +
        D.invβ * ∑ i, ‖Torus.grad (movT_phi D M ρ r) (X i)‖ ^ 2 -
        ∑ i, movT_phit D M ρ ρt r (X i) +
        ∫ Y, movT_psit D M ρ ρt r Y ∂(movT_Q (b15c_gReg d D.s M) D N ρ r)) =
      ∑ i, ((Torus.laplacian V' (X i) - Torus.laplacian D.V (X i)) + inner ℝ (g i) (δ i) +
        β * inner ℝ (δ i) (b i)) := by
    rw [← Finset.sum_congr rfl fun i _ => hterm i]
    simp only [Finset.sum_add_distrib, Finset.sum_sub_distrib, ← Finset.mul_sum]
    ring
  rw [hsum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  have hbound : ∀ i ∈ (Finset.univ : Finset (Fin N)), |(Torus.laplacian V' (X i) - Torus.laplacian D.V (X i)) +
      inner ℝ (g i) (δ i) + β * inner ℝ (δ i) (b i)| ≤ (1 + max Bg 0 + β * max Bb 0) * ε := by
    intro i _
    have h1 := hlap (X i)
    have h2 : |inner ℝ (g i) (δ i)| ≤ max Bg 0 * ε := by
      refine (abs_real_inner_le_norm _ _).trans ?_
      have hg1 : ‖g i‖ ≤ max Bg 0 := by
        exact (hBg (⟨r, hr⟩, X i) (Set.mem_univ _)).trans (le_max_left _ _)
      exact mul_le_mul hg1 (hgrad (X i)) (norm_nonneg _) (le_max_right _ _)
    have h3 : |β * inner ℝ (δ i) (b i)| ≤ β * (max Bb 0 * ε) := by
      rw [abs_mul, abs_of_pos hβpos]
      refine mul_le_mul_of_nonneg_left ((abs_real_inner_le_norm _ _).trans ?_) hβpos.le
      have hb1 : ‖b i‖ ≤ max Bb 0 := by
        exact ((norm_le_pi_norm (b15d_configDriftReg (N := N) D M X) i).trans
          (hBb X (Set.mem_univ _))).trans (le_max_left _ _)
      calc ‖δ i‖ * ‖b i‖ ≤ ε * max Bb 0 := mul_le_mul (hgrad (X i)) hb1 (norm_nonneg _) hε
        _ = max Bb 0 * ε := by ring
    calc _ ≤ |Torus.laplacian V' (X i) - Torus.laplacian D.V (X i)| + |inner ℝ (g i) (δ i)| +
          |β * inner ℝ (δ i) (b i)| := (abs_add_three _ _ _)
      _ ≤ ε + max Bg 0 * ε + β * (max Bb 0 * ε) := by linarith
      _ = _ := by ring
  refine (Finset.sum_le_sum hbound).trans ?_
  simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
  nlinarith [hε]

end HRS
