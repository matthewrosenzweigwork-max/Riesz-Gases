import HRS.MS.Fp81S21InitGauss
import HRS.MS.Fp81S21InitialIid
import HRS.MS.Fp81S21RespIid3

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

namespace HRS.Fp81.S21

open S45
open HRS.Whole
open HRS (Euc MemCb cbNorm)
open HRS.MS.R26T3
open HRS.MS.S21

private theorem fp81s21_initGaussIid_hasSum_coords
    {p : Parameters} (σ : ℕ ≃ ℕ × MultiIndex p.d) (q : ℕ → Euc p.d → ℝ)
    (hT : 0 < p.T) (u : Set.Icc (0 : ℝ) p.T)
    (α : MultiIndex p.d) (x : Euc p.d) {ψ : ℝ}
    (hrec : HasSum (fun n => r26t3_cosine p.T n u * s21f_w n *
      q (σ.symm (n, α)) x) ψ) :
    HasSum (fun j => SeqL2.coord (s21gVec σ hT (u : ℝ) α) j * q j x) ψ := by
  classical
  let P : Set ℕ := {j | (σ j).2 = α}
  let emb : ℕ → P := fun n => ⟨σ.symm (n, α), by
    change (σ (σ.symm (n, α))).2 = α
    simp⟩
  have hemb : Function.Bijective emb := by
    constructor
    · intro n m h
      have hval : σ.symm (n, α) = σ.symm (m, α) := congrArg Subtype.val h
      have hp : (n, α) = (m, α) := σ.symm.injective hval
      exact congrArg Prod.fst hp
    · intro j
      refine ⟨(σ j.1).1, ?_⟩
      apply Subtype.ext
      change σ.symm ((σ j.1).1, α) = j.1
      apply σ.injective
      have hj : (σ j.1).2 = α := j.2
      have hp : ((σ j.1).1, α) = σ j.1 := Prod.ext rfl hj.symm
      simpa using hp
  let e : ℕ ≃ P := Equiv.ofBijective emb hemb
  let f : ℕ → ℝ := fun j => SeqL2.coord (s21gVec σ hT (u : ℝ) α) j * q j x
  have hsrec : HasSum (fun n => f (e n).val) ψ := by
    convert hrec using 1
    funext n
    have hσ : σ (e n).val = (n, α) := by
      change σ (σ.symm (n, α)) = (n, α)
      simp
    have hidx : (e n).val = σ.symm (n, α) := by
      simpa using congrArg σ.symm hσ
    have hcoord : SeqL2.coord (s21gVec σ hT (u : ℝ) α) (e n).val =
        s11p_kap n * r2CosBasis p.T n (u : ℝ) := by
      rw [s21gVec_coord, hσ]
      simp
    change SeqL2.coord (s21gVec σ hT (u : ℝ) α) (e n).val * q (e n).val x = _
    rw [hcoord, hidx]
    have hw : s11p_kap n = s21f_w n := by
      unfold HRS.Whole.s11p_kap HRS.MS.R26T3.s21f_w
      congr 1
      norm_num
    have hc : r26t3_cosine p.T n (u : ℝ) = r2CosBasis p.T n (u : ℝ) := by
      unfold r26t3_cosine r2CosBasis
      split_ifs <;> simp [one_div]
    rw [hw, ← hc]
    ring
  have hsP : HasSum (fun j : P => f j.val) ψ := e.hasSum_iff.mp hsrec
  have hzero : ∀ j, j ∉ P → f j = 0 := by
    intro j hj
    have hnot : (σ j).2 ≠ α := fun heq => hj heq
    change SeqL2.coord (s21gVec σ hT (u : ℝ) α) j * q j x = 0
    rw [s21gVec_coord]
    simp [hnot]
  have hsup : Function.support f ⊆ P := by
    intro j hj
    by_contra hnot
    exact hj (hzero j hnot)
  exact (hasSum_subtype_iff_of_support_subset hsup).mp hsP

/-- For the centered iid Gaussian, synthesis transfers covariance from sequence
coordinates to any two bounded tests represented by the shifted cosine series. -/
private theorem fp81s21_initGaussIid_synthesis_cov
    {d J : ℕ} {μ : Measure (Euc d)} [IsProbabilityMeasure μ]
    {q : ℕ → Euc d → ℝ} (hq : IsSummableFeatureFamily J q)
    {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussian G)
    (hcov : ∀ x y, covarianceBilin G x y =
      covarianceBilin (μ.map (s21h2_Y q μ)) x y)
    (a b : SeqL2) {ψ ψ' : Euc d → ℝ}
    (hψ : MemLp ψ 2 μ) (hψ' : MemLp ψ' 2 μ)
    (hs : ∀ x, HasSum (fun j => SeqL2.coord a j * q j x) (ψ x))
    (hs' : ∀ x, HasSum (fun j => SeqL2.coord b j * q j x) (ψ' x)) :
    Integrable (fun z : SeqL2 => inner ℝ a z * inner ℝ b z) G ∧
      (∫ z, inner ℝ a z * inner ℝ b z ∂G) =
        inner ℝ (S45.s45_U ψ hψ) (S45.s45_U ψ' hψ') := by
  haveI : IsGaussian G := hG.1
  have hφm : ∀ i, MemLp (q i) 2 μ := fun i =>
    HRS.MS.Tc5.tc5_memLp_of_cb (hq.1 i)
  have hw : ∀ i x, |q i x| ≤ cbNorm J (q i) := by
    intro i x
    have h := HRS.MS.Tc5.tc5_cb_sup_le (hq.1 i) x
    rwa [Real.norm_eq_abs] at h
  have hU : Summable fun i => ‖S45.s45_U (q i) (hφm i)‖ := by
    refine Summable.of_nonneg_of_le (fun i => norm_nonneg _) (fun i => ?_)
      (hq.2.mul_left 2)
    exact S45.s45_U_norm_le (hφm i)
      (fun x => HRS.MS.Tc5.tc5_cb_sup_le (hq.1 i) x)
  let T : SeqL2 →L[ℝ] Lp ℝ 2 μ := S45.s45_T S45.s45_seqBasis hU
  have hTa : T a = S45.s45_U ψ hψ :=
    HRS.MS.S21.s21g_T_eq hφm hq.2 hw hU a hψ hs
  have hTb : T b = S45.s45_U ψ' hψ' :=
    HRS.MS.S21.s21g_T_eq hφm hq.2 hw hU b hψ' hs'
  have hmem : MemLp id 2 G := ProbabilityTheory.IsGaussian.memLp_two_id
  have hn : Integrable (fun z : SeqL2 => ‖z‖ ^ 2) G := by
    have h := hmem.integrable_norm_pow (p := 2) (by norm_num)
    simpa using h
  have hint : Integrable (fun z : SeqL2 => inner ℝ a z * inner ℝ b z) G := by
    refine (hn.const_mul (‖a‖ * ‖b‖)).mono' ?_ (Filter.Eventually.of_forall fun z => ?_)
    · exact ((continuous_const.inner continuous_id).mul
        (continuous_const.inner continuous_id)).aestronglyMeasurable
    · rw [norm_mul]
      calc ‖inner ℝ a z‖ * ‖inner ℝ b z‖ ≤ (‖a‖ * ‖z‖) * (‖b‖ * ‖z‖) :=
            mul_le_mul (norm_inner_le_norm _ _) (norm_inner_le_norm _ _)
              (norm_nonneg _) (by positivity)
        _ = ‖a‖ * ‖b‖ * ‖z‖ ^ 2 := by ring
  have hmean : ∫ z, id z ∂G = 0 := HRS.HilbertCLTAux.gaussian_mean_zero hG
  have hcovApply (x y : SeqL2) :
      (∫ z, inner ℝ x z * inner ℝ y z ∂G) = covarianceBilin G x y := by
    rw [covarianceBilin_apply hmem, hmean]
    simp
  have h1 := hcovApply a b
  have hGseq := HRS.MS.R26T3.s21h2_gauss_seq hq μ
    (fun _ : Euc d => 0) G hG hcov
  have hB : covarianceBilin G =
      (innerSL ℝ : Lp ℝ 2 μ →L[ℝ] Lp ℝ 2 μ →L[ℝ] ℝ).bilinearComp T T := by
    refine HRS.MS.S21.s21g_clm_ext ?_
    intro i j
    have hcoord : covarianceBilin G (S45.s45_seqBasis i) (S45.s45_seqBasis j) =
        HRS.Whole.susceptibilityCov (fun _ : Euc d => 0) μ 0 (q i) (q j) := by
      have hcint : covarianceBilin G (S45.s45_seqBasis i) (S45.s45_seqBasis j) =
          ∫ z, SeqL2.coord z i * SeqL2.coord z j ∂G := by
        have hc := hcovApply (S45.s45_seqBasis i) (S45.s45_seqBasis j)
        simpa only [S45.s45_inner_seqBasis] using hc.symm
      exact hcint.trans (hGseq.2 i j).2
    have hcent : HRS.Whole.susceptibilityCov (fun _ : Euc d => 0) μ 0 (q i) (q j) =
        ∫ x, (q i x - HRS.Whole.pair μ (q i)) *
          (q j x - HRS.Whole.pair μ (q j)) ∂μ :=
      HRS.MS.R26T3.s21h2_susc hq μ (fun _ : Euc d => 0) i j
    have hleft : (fun x => q i x - HRS.Whole.pair μ (q i)) =ᵐ[μ]
        (S45.s45_U (q i) (hφm i) : Euc d → ℝ) := by
      filter_upwards [S45.s45_U_ae (hφm i)] with x hx
      simpa [HRS.Whole.projMean] using hx.symm
    have hright : (fun x => q j x - HRS.Whole.pair μ (q j)) =ᵐ[μ]
        (S45.s45_U (q j) (hφm j) : Euc d → ℝ) := by
      filter_upwards [S45.s45_U_ae (hφm j)] with x hx
      simpa [HRS.Whole.projMean] using hx.symm
    have hinner : (∫ x, (q i x - HRS.Whole.pair μ (q i)) *
          (q j x - HRS.Whole.pair μ (q j)) ∂μ) =
        inner ℝ (S45.s45_U (q i) (hφm i)) (S45.s45_U (q j) (hφm j)) := by
      exact HRS.Whole.Q34.l2Inner_eq hleft hright
    change covarianceBilin G (S45.s45_seqBasis i) (S45.s45_seqBasis j) =
      inner ℝ (T (S45.s45_seqBasis i)) (T (S45.s45_seqBasis j))
    rw [S45.s45_T_basis S45.s45_seqBasis hU i,
      S45.s45_T_basis S45.s45_seqBasis hU j]
    exact hcoord.trans (hcent.trans hinner)
  refine ⟨hint, ?_⟩
  rw [h1, hB]
  change inner ℝ (T a) (T b) = _
  rw [hTa, hTb]

/-- At zero coupling, the initial Gaussian on cosine coordinates has the iid
centered covariance, and its synthesized finite-horizon window has the required
evaluation-product covariance. The radius is fixed before the trajectory,
shift, and window coordinates. -/
theorem fp81s21_initGaussIid_endpoint (p : Parameters) :
    ∃ δ26 : ℝ, 0 < δ26 ∧ δ26 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ26 → ∀ R : Trajectory p δ,
        p.γ = 0 → ∀ a : ℝ, 0 ≤ a →
          ∃ G : Measure SeqL2, IsProbabilityMeasure G ∧
            IsCenteredGaussianSeq G (fun j k =>
              HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                (r26t3_qwin R a j) (r26t3_qwin R a k)) ∧
            ∀ u v : Set.Icc (0 : ℝ) p.T, ∀ α β : MultiIndex p.d,
              Integrable
                (fun y : Window p =>
                  fp81s21_windowCoordCLM p u α y * fp81s21_windowCoordCLM p v β y)
                (Measure.map (fp81s21_initGauss_synthesis p) G) ∧
              (∫ y, fp81s21_windowCoordCLM p u α y *
                    fp81s21_windowCoordCLM p v β y
                  ∂(Measure.map (fp81s21_initGauss_synthesis p) G)) =
                HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                  (r26t3_U R 0 (a + (u : ℝ)) (oscTestFun (wholeSpaceIndex p.d) α))
                  (r26t3_U R 0 (a + (v : ℝ)) (oscTestFun (wholeSpaceIndex p.d) β)) := by
  obtain ⟨δc, hδc, hδch, hcos⟩ := fp81s21_cosRecon_radius p
  obtain ⟨δo, hδo, hδoh, horbit⟩ := fp81s21_respRecon_orbit_bounds p
  let δ26 := min δc δo
  have hδ26 : 0 < δ26 := by dsimp [δ26]; exact lt_min hδc hδo
  have hδ26h : δ26 ≤ 1 / 2 := by
    dsimp [δ26]
    exact (min_le_left _ _).trans hδch
  refine ⟨δ26, hδ26, hδ26h, fun δ hδ hδle R hγ a ha => ?_⟩
  have hδc' : δ ≤ δc := hδle.trans
    (show δ26 ≤ δc by dsimp [δ26]; exact min_le_left _ _)
  have hδo' : δ ≤ δo := hδle.trans
    (show δ26 ≤ δo by dsimp [δ26]; exact min_le_right _ _)
  obtain ⟨Cobs, hCobs, hcosR⟩ := hcos δ hδ hδc' R
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ26h
  have hq := (hcosR a ha).1
  haveI : IsProbabilityMeasure (r26t3_mu R 0) := s21h2_s09_prob hδ hδhalf R
  obtain ⟨G, hGp, hG, hcov⟩ := s21h2_exists_gaussian hq (r26t3_mu R 0)
  letI : IsProbabilityMeasure G := hGp
  have hGseq := s21h2_gauss_seq hq (r26t3_mu R 0)
    (rieszKernel p.d p.s) G hG hcov
  have hGseq' : IsCenteredGaussianSeq G (fun j k =>
      HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
        (r26t3_qwin R a j) (r26t3_qwin R a k)) := by
    simpa [hγ] using hGseq
  refine ⟨G, hGp, hGseq', ?_⟩
  intro u v α β
  obtain ⟨Bα, hBα, hregα, hcontα⟩ := horbit δ hδ hδo' R a ha α
  obtain ⟨Bβ, hBβ, hregβ, hcontβ⟩ := horbit δ hδ hδo' R a ha β
  have hψmem : MemLp
      (r26t3_U R 0 (a + (u : ℝ)) (oscTestFun (wholeSpaceIndex p.d) α))
      2 (r26t3_mu R 0) :=
    HRS.MS.Tc5.tc5_memLp_of_cb (hregα u.1 u.2).1
  have hψ'mem : MemLp
      (r26t3_U R 0 (a + (v : ℝ)) (oscTestFun (wholeSpaceIndex p.d) β))
      2 (r26t3_mu R 0) :=
    HRS.MS.Tc5.tc5_memLp_of_cb (hregβ v.1 v.2).1
  let σ := r26t3_feature_enum p.d
  let S := fp81s21_initGauss_synthesis p
  let ev := fun (t : Set.Icc (0 : ℝ) p.T) (η : MultiIndex p.d) =>
    fp81s21_windowCoordCLM p t η
  let au : SeqL2 := s21gVec σ p.hT (u : ℝ) α
  let av : SeqL2 := s21gVec σ p.hT (v : ℝ) β
  have hsu := hcosR a ha
  have hsψ : ∀ x, HasSum (fun j => SeqL2.coord au j * r26t3_qwin R a j x)
      (r26t3_U R 0 (a + (u : ℝ)) (oscTestFun (wholeSpaceIndex p.d) α) x) := by
    intro x
    exact fp81s21_initGaussIid_hasSum_coords σ (r26t3_qwin R a)
      p.hT u α x (hsu.2.2.2 u α x)
  have hsψ' : ∀ x, HasSum (fun j => SeqL2.coord av j * r26t3_qwin R a j x)
      (r26t3_U R 0 (a + (v : ℝ)) (oscTestFun (wholeSpaceIndex p.d) β) x) := by
    intro x
    exact fp81s21_initGaussIid_hasSum_coords σ (r26t3_qwin R a)
      p.hT v β x (hsu.2.2.2 v β x)
  have hscov := fp81s21_initGaussIid_synthesis_cov hq hG hcov au av
    hψmem hψ'mem hsψ hsψ'
  let Γinit : Measure (Window p) := Measure.map S G
  have hSmeas : Measurable S := S.continuous.measurable
  have hev : ∀ z, ev u α (S z) = inner ℝ au z := by
    intro z
    dsimp [ev, au, S, fp81s21_initGauss_synthesis]
    rw [fp81s21_windowCoordCLM_apply]
    exact HRS.MS.S21.s21gPhi_coord_inner σ p.hT
      ((wholeSpaceIndex p.d : ℕ) : ℝ) z u α
  have hev' : ∀ z, ev v β (S z) = inner ℝ av z := by
    intro z
    dsimp [ev, av, S, fp81s21_initGauss_synthesis]
    rw [fp81s21_windowCoordCLM_apply]
    exact HRS.MS.S21.s21gPhi_coord_inner σ p.hT
      ((wholeSpaceIndex p.d : ℕ) : ℝ) z v β
  have hcomp : Integrable (fun z => ev u α (S z) * ev v β (S z)) G := by
    simpa only [hev, hev'] using hscov.1
  have hfun : AEStronglyMeasurable
      (fun y : Window p => ev u α y * ev v β y) Γinit :=
    ((ev u α).continuous.mul (ev v β).continuous).aestronglyMeasurable
  have hint : Integrable (fun y : Window p => ev u α y * ev v β y) Γinit :=
    (integrable_map_measure hfun hSmeas.aemeasurable).2 hcomp
  have htarget : (∫ z, ev u α (S z) * ev v β (S z) ∂G) =
      HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
        (r26t3_U R 0 (a + (u : ℝ)) (oscTestFun (wholeSpaceIndex p.d) α))
        (r26t3_U R 0 (a + (v : ℝ)) (oscTestFun (wholeSpaceIndex p.d) β)) := by
    rw [show (fun z => ev u α (S z) * ev v β (S z)) =
      (fun z => inner ℝ au z * inner ℝ av z) from funext fun z => by rw [hev, hev']]
    calc
      (∫ z, inner ℝ au z * inner ℝ av z ∂G) =
          inner ℝ (S45.s45_U
            (r26t3_U R 0 (a + (u : ℝ)) (oscTestFun (wholeSpaceIndex p.d) α)) hψmem)
            (S45.s45_U
              (r26t3_U R 0 (a + (v : ℝ)) (oscTestFun (wholeSpaceIndex p.d) β)) hψ'mem) := hscov.2
      _ = ∫ x,
          (r26t3_U R 0 (a + (u : ℝ)) (oscTestFun (wholeSpaceIndex p.d) α) x -
            HRS.Whole.pair (r26t3_mu R 0)
              (r26t3_U R 0 (a + (u : ℝ)) (oscTestFun (wholeSpaceIndex p.d) α))) *
          (r26t3_U R 0 (a + (v : ℝ)) (oscTestFun (wholeSpaceIndex p.d) β) x -
            HRS.Whole.pair (r26t3_mu R 0)
              (r26t3_U R 0 (a + (v : ℝ)) (oscTestFun (wholeSpaceIndex p.d) β)))
          ∂(r26t3_mu R 0) := by
            symm
            exact HRS.Whole.Q34.l2Inner_eq
              (by
                filter_upwards [S45.s45_U_ae hψmem] with x hx
                simpa [HRS.Whole.projMean] using hx.symm)
              (by
                filter_upwards [S45.s45_U_ae hψ'mem] with x hx
                simpa [HRS.Whole.projMean] using hx.symm)
      _ = HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
            (r26t3_U R 0 (a + (u : ℝ)) (oscTestFun (wholeSpaceIndex p.d) α))
            (r26t3_U R 0 (a + (v : ℝ)) (oscTestFun (wholeSpaceIndex p.d) β)) := by
              symm
              exact fp81s21_initial_iid_cov hδ hδhalf R hγ
                ((hregβ v.1 v.2).1).1.continuous
                (Cg := cbNorm (r26t3_J p.d)
                  (r26t3_U R 0 (a + (v : ℝ)) (oscTestFun (wholeSpaceIndex p.d) β)))
                (fun x => by
                  have hx := HRS.MS.Tc5.tc5_cb_sup_le (hregβ v.1 v.2).1 x
                  rwa [Real.norm_eq_abs] at hx)
  refine ⟨?_, ?_⟩
  · simpa [Γinit, ev] using hint
  · rw [show (∫ y, ev u α y * ev v β y ∂Γinit) =
      ∫ z, ev u α (S z) * ev v β (S z) ∂G from
        integral_map hSmeas.aemeasurable hfun]
    simpa [Γinit, ev] using htarget

/-- The positive and zero coupling Gaussian handoffs share a single radius,
chosen before the trajectory and all shifts. -/
theorem fp81s21_initGaussIid_common (p : Parameters) :
    ∃ δ26 : ℝ, 0 < δ26 ∧ δ26 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ26 → ∀ R : Trajectory p δ,
        (0 < p.γ ∨ p.γ = 0) → ∀ a : ℝ, 0 ≤ a →
          ∃ G : Measure SeqL2, IsProbabilityMeasure G ∧
            IsCenteredGaussianSeq G (fun j k =>
              HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                (r26t3_qwin R a j) (r26t3_qwin R a k)) ∧
            ∀ u v : Set.Icc (0 : ℝ) p.T, ∀ α β : MultiIndex p.d,
              Integrable
                (fun y : Window p =>
                  fp81s21_windowCoordCLM p u α y * fp81s21_windowCoordCLM p v β y)
                (Measure.map (fp81s21_initGauss_synthesis p) G) ∧
              (∫ y, fp81s21_windowCoordCLM p u α y *
                    fp81s21_windowCoordCLM p v β y
                  ∂(Measure.map (fp81s21_initGauss_synthesis p) G)) =
                HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
                  (r26t3_U R 0 (a + (u : ℝ)) (oscTestFun (wholeSpaceIndex p.d) α))
                  (r26t3_U R 0 (a + (v : ℝ)) (oscTestFun (wholeSpaceIndex p.d) β)) := by
  obtain ⟨δp, hδp, hδph, hpos⟩ := fp81s21_initGauss_positive p
  obtain ⟨δ0, hδ0, hδ0h, hiid⟩ := fp81s21_initGaussIid_endpoint p
  let δ26 := min δp δ0
  have hδ26 : 0 < δ26 := by dsimp [δ26]; exact lt_min hδp hδ0
  have hδ26h : δ26 ≤ 1 / 2 := by
    dsimp [δ26]
    exact (min_le_left _ _).trans hδph
  refine ⟨δ26, hδ26, hδ26h, ?_⟩
  intro δ hδ hδle R hγ a ha
  have hδp' : δ ≤ δp := hδle.trans (show δ26 ≤ δp by dsimp [δ26]; exact min_le_left _ _)
  have hδ0' : δ ≤ δ0 := hδle.trans (show δ26 ≤ δ0 by dsimp [δ26]; exact min_le_right _ _)
  rcases hγ with hpos' | hzero
  · exact hpos δ hδ hδp' R hpos' a ha
  · exact hiid δ hδ hδ0' R hzero a ha

#print axioms fp81s21_initGaussIid_endpoint
#print axioms fp81s21_initGaussIid_common

end HRS.Fp81.S21

end
