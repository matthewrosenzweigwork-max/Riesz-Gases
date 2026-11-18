import HRS.MS.Fp81S21CosRecon
import HRS.MS.Fp81S21RespRecon9
import HRS.MS.Fp81S21InitialStein
import HRS.MS.Fp81S21InitialKappa
import HRS.MS.WsInitGAux9

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

/-- The explicit synthesis map used to turn cosine coordinates into an oscillator window. -/
def fp81s21_initGauss_synthesis (p : Parameters) : SeqL2 →L[ℝ] Window p :=
  s21gPhi (r26t3_feature_enum p.d) p.hT ((wholeSpaceIndex p.d : ℕ) : ℝ)

private theorem fp81s21_initGauss_hasSum_coords
    {p : Parameters} (σ : ℕ ≃ ℕ × MultiIndex p.d) (q : ℕ → Euc p.d → ℝ)
    (hT : 0 < p.T) (a : ℝ) (ha : 0 ≤ a) (u : Set.Icc (0 : ℝ) p.T)
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

private theorem fp81s21_initGauss_kdata
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (E : InitialSteinEnv R)
    [IsProbabilityMeasure (r26t3_mu R 0)] :
    ∃ K : Lp ℝ 2 (r26t3_mu R 0) →L[ℝ] Lp ℝ 2 (r26t3_mu R 0),
      IsKData (r26t3_mu R 0) (rieszKernel p.d p.s) K := by
  have hd1 : 1 ≤ p.d := by have := p.hd; omega
  have hsd : p.s < (p.d : ℝ) := by
    have hd0 : (0 : ℝ) ≤ (p.d : ℝ) / 2 := by positivity
    linarith [p.hs]
  obtain ⟨L, hL⟩ := S47.s47_logmoment2 E.reference
  have hM : ∀ x, R.ρ 0 x ≤ E.C := fun x => by
    refine (le_abs_self _).trans ((E.reference.h0 x).trans ?_)
    have he : Real.exp (-E.c * ‖x‖ ^ 2) ≤ 1 :=
      Real.exp_le_one_iff.2 (by nlinarith [sq_nonneg ‖x‖, E.reference.hc])
    nlinarith [E.reference.C0]
  exact S45.s45_kdata hd1 p.hs0 hsd E.reference.prob hM (L := L)
    (fun _ => by simpa [r26t3_mu] using hL)

private theorem fp81s21_initGauss_exists
    {p : Parameters} {δ : ℝ} (hδ : 0 < δ) (hδh : δ ≤ 1 / 2)
    (R : Trajectory p δ) (hγ : 0 < p.γ) (E : InitialSteinEnv R)
    {a : ℝ} (hq : IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a)) :
    ∃ G : Measure SeqL2, IsProbabilityMeasure G ∧
      IsCenteredGaussianSeq G (fun j k =>
        HRS.Whole.susceptibilityCov (rieszKernel p.d p.s) (r26t3_mu R 0) p.γ
          (r26t3_qwin R a j) (r26t3_qwin R a k)) := by
  haveI : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
  obtain ⟨K, hK⟩ := fp81s21_initGauss_kdata hδ hδh R E
  have hqmem : ∀ j, MemLp (r26t3_qwin R a j) 2 (r26t3_mu R 0) := fun j =>
    HRS.MS.Tc5.tc5_memLp_of_cb (hq.1 j)
  have hU : Summable fun j => ‖S45.s45_U (r26t3_qwin R a j) (hqmem j)‖ := by
    refine Summable.of_nonneg_of_le (fun j => norm_nonneg _) (fun j => ?_)
      (hq.2.mul_left 2)
    exact S45.s45_U_norm_le (hqmem j)
      (fun x => HRS.MS.Tc5.tc5_cb_sup_le (hq.1 j) x)
  obtain ⟨G, hGp, hG, hcov⟩ := S45.s45_exists_gaussian hK p.hγ
    S45.s45_seqBasis hU
  refine ⟨G, hGp, ⟨hG, fun j k => ?_⟩⟩
  obtain ⟨hint, hval⟩ := hcov j k
  simp only [S45.s45_inner_seqBasis] at hint hval
  exact ⟨hint, hval.trans
    (S45.s45_susceptibilityCov_eq hK hγ (hqmem j) (hqmem k)).symm⟩

/-- For positive coupling, one finite-horizon Gaussian on the initial cosine coordinates
has the actual one-response susceptibility covariance, and its synthesized window has the
claimed time-coordinate covariance. The radius is chosen before the trajectory, shift, and
window coordinates. -/
theorem fp81s21_initGauss_positive (p : Parameters) :
    ∃ δ26 : ℝ, 0 < δ26 ∧ δ26 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ26 → ∀ R : Trajectory p δ, 0 < p.γ →
        ∀ a : ℝ, 0 ≤ a →
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
  have hδc' : δ ≤ δc := hδle.trans (show δ26 ≤ δc by dsimp [δ26]; exact min_le_left _ _)
  have hδo' : δ ≤ δo := hδle.trans (show δ26 ≤ δo by dsimp [δ26]; exact min_le_right _ _)
  obtain ⟨Cobs, hCobs, hcosR⟩ := hcos δ hδ hδc' R
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ26h
  obtain ⟨E⟩ := initialSteinEnv_exists hδ hδhalf R hγ
  obtain ⟨G, hGp, hG⟩ := fp81s21_initGauss_exists hδ hδhalf R hγ E
    (hcosR a ha).1
  refine ⟨G, hGp, hG, ?_⟩
  intro u v α β
  obtain ⟨Bα, hBα, hregα, hcontα⟩ := horbit δ hδ hδo' R a ha α
  obtain ⟨Bβ, hBβ, hregβ, hcontβ⟩ := horbit δ hδ hδo' R a ha β
  haveI : IsProbabilityMeasure (r26t3_mu R 0) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu E.reference.prob
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
    exact fp81s21_initGauss_hasSum_coords σ (r26t3_qwin R a)
      p.hT a ha u α x (hsu.2.2.2 u α x)
  have hsψ' : ∀ x, HasSum (fun j => SeqL2.coord av j * r26t3_qwin R a j x)
      (r26t3_U R 0 (a + (v : ℝ)) (oscTestFun (wholeSpaceIndex p.d) β) x) := by
    intro x
    exact fp81s21_initGauss_hasSum_coords σ (r26t3_qwin R a)
      p.hT a ha v β x (hsu.2.2.2 v β x)
  obtain ⟨K, hK⟩ := fp81s21_initGauss_kdata hδ hδhalf R E
  have hcov := HRS.MS.S21.s21g_cov hK
    hγ (hcosR a ha).1 hG au av hψmem hψ'mem hsψ hsψ'
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
    simpa only [hev, hev'] using hcov.1
  have hfun : AEStronglyMeasurable
      (fun y : Window p => ev u α y * ev v β y) Γinit :=
    ((ev u α).continuous.mul (ev v β).continuous).aestronglyMeasurable
  have hint : Integrable (fun y : Window p => ev u α y * ev v β y) Γinit :=
    (integrable_map_measure hfun hSmeas.aemeasurable).2 hcomp
  refine ⟨?_, ?_⟩
  · simpa [Γinit, ev] using hint
  · rw [show (∫ y, ev u α y * ev v β y ∂Γinit) =
      ∫ z, ev u α (S z) * ev v β (S z) ∂G from
        integral_map hSmeas.aemeasurable hfun]
    rw [show (fun z => ev u α (S z) * ev v β (S z)) =
      (fun z => inner ℝ au z * inner ℝ av z) from funext fun z => by rw [hev, hev']]
    simpa [Γinit, ev] using hcov.2

#print axioms fp81s21_initGauss_synthesis
#print axioms fp81s21_initGauss_positive

end HRS.Fp81.S21

end
