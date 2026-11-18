import HRS.MS.DecStatAux2

/-!
# SA4, packet 3: the sub-Coulomb commutator along the adjoint orbit of a `wClass` test

* `sa4_two_le_p`, `sa4_errorRate_nonneg`: facts on the admissible density `𝔠`;
* `sa4_orbit_facts`: the `C_b^{m_*}` bound and the weak jet of `U^{r,t}φ` from `AdjointInputRd (wClass) (wWeakClass) m_*`;
* `Sa4CommSub`, `sa4_commSub_exists`: the conclusion of S.B.5 (ii),(iii) in the form used below (the bound only);
* `sa4_rem_pt`: the pointwise bound `|½ Comm_N(Mᵀ∇U^{rr,t}φ)| ≤ ½ Cs Kb (F + o + Cs e_N^𝔠)` in `ofReal` form.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.MainRdStat HRS.MS.ZeroTemp
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.DecStat

variable {d : ℕ}

theorem sa4_two_le_p {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (c : DecayingDensity d s) :
    2 ≤ c.integrability := by
  have hd2 : (2 : ℝ) < d := by linarith
  cases c with
  | sharp a ha =>
    obtain ⟨h1, h2⟩ := ha
    have h3 := (lt_min_iff.1 h2).1
    simp only [DecayingDensity.integrability]
    have hpos : 0 < a - 2 := by linarith
    rw [le_div_iff₀ hpos]
    linarith
  | lower hs =>
    simp only [DecayingDensity.integrability]
    have hpos : 0 < (d : ℝ) - s - 2 := by linarith
    rw [le_div_iff₀ hpos]
    linarith

theorem sa4_errorRate_nonneg {s : ℝ} (hs0 : 0 ≤ s) (c : DecayingDensity d s) (N : ℕ) : 0 ≤ c.errorRate N := by
  cases c with
  | sharp a ha => simp [DecayingDensity.errorRate]
  | lower hs =>
    simp only [DecayingDensity.errorRate]
    have h1 : 0 ≤ (1 + if s = 0 then Real.log N else 0) := by
      split_ifs
      · have := Real.log_natCast_nonneg N
        linarith
      · norm_num
    exact mul_nonneg h1 (Real.rpow_nonneg (Nat.cast_nonneg N) _)

section Orbit

variable {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- Facts about `f = U^{r,t}φ` from the adjoint input, for a general `wClass` test. -/
theorem sa4_orbit_facts {C : WholeCoeff d} {T K : ℝ} {r t : ℝ}
    (hA : AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) C T K) (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T)
    {φ : Euc d → ℝ} (hφ2 : ContDiff ℝ 2 φ) (hφ : (wClass m p).mem φ) :
    MemCb (mStar d) (propagatorW C r t φ) ∧
    cbNorm (mStar d) (propagatorW C r t φ) ≤ K * (wClass m p).norm φ ∧
    ContDiff ℝ ((mStar d : ℕ) : WithTop ℕ∞) (propagatorW C r t φ) ∧
    (∀ z, ‖iteratedFDeriv ℝ 2 (propagatorW C r t φ) z‖ ≤ K * (wClass m p).norm φ) ∧
    ∃ G : WmpSpace d m p, (∀ᵐ x ∂(volume : Measure (Euc d)),
        ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = propagatorW C r t φ x) ∧
      ‖G‖ ≤ K * (wClass m p).norm φ := by
  obtain ⟨-, hmem, hnorm, hcb, hcbn⟩ := hA r t hr hrt htT φ hφ2 hφ
  refine ⟨hcb, hcbn, hcb.1, fun z => ?_, ?_⟩
  · exact (sa11_iter_le_cbNorm hcb (by unfold mStar; omega) z).trans hcbn
  · obtain ⟨G, hG⟩ := sa11_exists_weakJet hmem
    exact ⟨G, hG, by rw [← sa11_wWeak_norm_eq hG]; exact hnorm⟩

end Orbit

/-- The conclusion of S.B.5 (ii),(iii) for the admissible density `c`, at the log moment `Lm` and constants `(C₀ᶜ, Cs)`. -/
def Sa4CommSub (d : ℕ) (s Lm C₀c Cs : ℝ) (c : DecayingDensity d s) : Prop :=
  ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ') →
    (s = 0 → HasLogMoment (HRS.Whole.withDensityReal ρ) Lm) →
    ∀ X : EucConfig d N, Function.Injective X → ∀ (v : Euc d → Euc d) (K : ℝ),
      HasFracTransportBound c.regularity c.integrability v K →
      |commN d s v X (HRS.Whole.withDensityReal ρ)| ≤
        Cs * K * (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + oNΛ d s C₀c Λ' N +
          Cs * c.errorRate N)

theorem sa4_commSub_exists {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (c : DecayingDensity d s) (Lm : ℝ) :
    ∃ C₀c Cs : ℝ, 0 ≤ C₀c ∧ 0 < Cs ∧ Sa4CommSub d s Lm C₀c Cs c := by
  cases c with
  | sharp a ha =>
    obtain ⟨C₀', Cs, hC₀', hCs, H⟩ := HRS.Commutator.Whole.whole_commutator_sub_sharp_of_subcoulomb hs0 hsd a
      ⟨ha.1, lt_of_lt_of_le ha.2 (min_le_left _ _)⟩ Lm
    refine ⟨C₀', Cs, hC₀', hCs, fun Λ' hΛ' N hN ρ hρ hρle hlog X hX v K hv => ?_⟩
    have := (H Λ' hΛ' N hN ρ hρ hρle hlog X hX v K hv).2
    simpa [DecayingDensity.errorRate] using this
  | lower hs' =>
    obtain ⟨C₀', Cs, hC₀', hCs, H⟩ := HRS.Commutator.Whole.whole_commutator_sub_lower_of_subcoulomb hs0 hsd Lm
    refine ⟨C₀', Cs, hC₀', hCs, fun Λ' hΛ' N hN ρ hρ hρle hlog X hX v K hv => ?_⟩
    exact (H Λ' hΛ' N hN ρ hρ hρle hlog X hX v K hv).2

section RemPt

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ} {𝔈 : ℕ → ℝ}

/-- the per-test constant of the orbit commutator -/
def sa4Kb (d : ℕ) (MB Ctr Kad wn : ℝ) : ℝ := (d : ℝ) ^ 2 * max MB 0 * (1 + Ctr) * (max Kad 0 * wn)

/-- the transport hypothesis (the output of `sa11_transport` for `𝔠`) -/
def Sa4Transport (d : ℕ) {s : ℝ} (c : DecayingDensity d s) [Fact (2 ≤ c.integrability)] (Ctr : ℝ) : Prop :=
  ∀ (Nm : Matrix (Fin d) (Fin d) ℝ) (G : WmpSpace d c.sobolevIndex c.integrability) (f : Euc d → ℝ) (σ : ℝ),
    ContDiff ℝ ((mStar d : ℕ) : WithTop ℕ∞) f →
    (∀ᵐ x ∂(volume : Measure (Euc d)),
      ((G : WLp d c.sobolevIndex c.integrability) : Euc d → (WIndex d c.sobolevIndex → ℝ)) x (wZero d c.sobolevIndex) = f x) →
    (∀ z, ‖iteratedFDeriv ℝ 2 f z‖ ≤ σ) →
    HasFracTransportBound c.regularity c.integrability (fun x => Torus.matVec Nm (gradient f x))
      (HRS.MS.SuppU15.u15_cM Nm * (σ + Ctr * ‖G‖))

theorem sa4_transport_exists (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (c : DecayingDensity d s)
    [Fact (2 ≤ c.integrability)] :
    ∃ Ctr : ℝ, 0 ≤ Ctr ∧ Sa4Transport d c Ctr := by
  obtain ⟨hα, hℓ⟩ := sa11_regularity_facts hs0 hsd c
  have hmm : mStar d ≤ c.sobolevIndex := by unfold DecayingDensity.sobolevIndex; omega
  obtain ⟨Ctr, hCtr0, hTr⟩ := sa11_transport (m := c.sobolevIndex) (p := c.integrability) hd hα hℓ hmm
  exact ⟨Ctr, hCtr0, fun Nm G f σ hf hG hσ => hTr Nm G f σ hf hG hσ⟩

/-- the commutator bound for one test at one `r`, in `ofReal` form -/
theorem sa4_rem_pt (c : DecayingDensity d S.s) [Fact (2 ≤ c.integrability)]
    (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hr3 : 3 ≤ r) (hd : 1 ≤ d)
    {N : ℕ} (hN : 2 ≤ N) {Lm C₀c Cs Ctr Kad : ℝ} (hCs : 0 ≤ Cs) (hCtr : 0 ≤ Ctr) (hTr : Sa4Transport d c Ctr)
    (hLm : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) S.T → HasLogMoment (HRS.Whole.withDensityReal (S.ρ N t)) Lm)
    (hcomm : Sa4CommSub d S.s Lm C₀c Cs c)
    (hA : AdjointInputRd (wClass c.sobolevIndex c.integrability) (wWeakClass c.sobolevIndex c.integrability)
      (mStar d) (S.coeff N) S.T Kad)
    {t : ℝ} {φ : Euc d → ℝ} (hφ2 : ContDiff ℝ 2 φ) (hφ : (wClass c.sobolevIndex c.integrability).mem φ)
    {rr : ℝ} (hrr : rr ∈ Set.Icc (0 : ℝ) t) (htT : t ≤ S.T)
    (X : EucConfig d N) (hX : Function.Injective X) :
    ENNReal.ofReal |flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) rr t φ) X (S.ρ N rr)| ≤
      ENNReal.ofReal (1 / 2 * (Cs * sa4Kb d MB Ctr Kad ((wClass c.sobolevIndex c.integrability).norm φ))) *
        (ENNReal.ofReal (rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N rr)) +
          oNΛ d S.s C₀c (max Λ 1) N) + ENNReal.ofReal (Cs * c.errorRate N)) := by
  have hrT : rr ∈ Set.Icc (0 : ℝ) S.T := ⟨hrr.1, hrr.2.trans htT⟩
  have hN1 : 1 ≤ N := by omega
  obtain ⟨hcb, hcbn, hcd, hD2, G, hG, hGn⟩ := sa4_orbit_facts hA hrr.1 hrr.2 htT hφ2 hφ
  have hmem2 : MemCb 2 (propagatorW (S.coeff N) rr t φ) := sa2_memCb_mono sa2_two_le_mStar hcb
  have hbr := HRS.MS.GenPath.s56_fluc_eq_comm (S.dyn N) hd S.hs0 S.hsd (sa2_regSlice hS hr3 hN1 hrT) hmem2 X
  have hprob := (hS.mean_field.solution N hN1).density rr hrT
  have hρΛ : ∀ x, S.ρ N rr x ≤ max Λ 1 := fun x => (sa2_rho_le hS hN1 hrT x).trans (le_max_left _ _)
  set wn : ℝ := (wClass c.sobolevIndex c.integrability).norm φ with hwn
  have hwn0 : 0 ≤ wn := ENNReal.toReal_nonneg
  have hσ0 : 0 ≤ Kad * wn := (norm_nonneg _).trans (hD2 0)
  have hcMB : HRS.MS.SuppU15.u15_cM S.M.transpose ≤ (d : ℝ) ^ 2 * max MB 0 :=
    sa11_cM_le (B := max MB 0) _ (fun i j => by
      have := hS.matrix_bound j i
      rw [Matrix.transpose_apply]
      exact this.trans (le_max_left _ _))
  have hcMnn := HRS.MS.SuppU15.u15_cM_nonneg S.M.transpose
  set Kb : ℝ := sa4Kb d MB Ctr Kad wn with hKb
  have htr := hTr S.M.transpose G _ (Kad * wn) hcd hG hD2
  have hKle : HRS.MS.SuppU15.u15_cM S.M.transpose * (Kad * wn + Ctr * ‖G‖) ≤ Kb := by
    have h1 : Kad * wn + Ctr * ‖G‖ ≤ (1 + Ctr) * (max Kad 0 * wn) := by
      have := mul_le_mul_of_nonneg_left hGn hCtr
      have h2 : Kad * wn ≤ max Kad 0 * wn := mul_le_mul_of_nonneg_right (le_max_left _ _) hwn0
      have h3 : Ctr * (Kad * wn) ≤ Ctr * (max Kad 0 * wn) := mul_le_mul_of_nonneg_left h2 hCtr
      nlinarith
    calc HRS.MS.SuppU15.u15_cM S.M.transpose * (Kad * wn + Ctr * ‖G‖)
        ≤ ((d : ℝ) ^ 2 * max MB 0) * ((1 + Ctr) * (max Kad 0 * wn)) :=
          mul_le_mul hcMB h1 (by nlinarith [norm_nonneg G]) (by positivity)
      _ = Kb := by rw [hKb, sa4Kb]; ring
  have hv := HRS.MS.SuppU15.u15_hasFrac_mono htr hKle
  have hK0 : 0 ≤ Kb := by
    have := mul_nonneg hcMnn (add_nonneg hσ0 (mul_nonneg hCtr (norm_nonneg G)))
    exact this.trans hKle
  have hb := hcomm (max Λ 1) (le_max_right _ _) N hN _ hprob hρΛ (fun _ => hLm hrT) X hX _ Kb hv
  have hcomm' : |commN d S.s (fun x => Torus.matVec S.M.transpose
      (gradient (propagatorW (S.coeff N) rr t φ) x)) X (HRS.Whole.withDensityReal (S.ρ N rr))| ≤
      Cs * Kb * (rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N rr)) +
        oNΛ d S.s C₀c (max Λ 1) N + Cs * c.errorRate N) := hb
  have hunfold : commN d S.s (fun x => Torus.matVec S.M.transpose
      (gradient (propagatorW (S.coeff N) rr t φ) x)) X (HRS.Whole.withDensityReal (S.ρ N rr)) =
      centeredPairFunctional (commutatorKernel d (S.dyn N).s (fun x => Torus.matVec (S.dyn N).M.transpose
        (gradient (propagatorW (S.coeff N) rr t φ) x))) X (HRS.Whole.withDensityReal (S.ρ N rr)) := rfl
  rw [hunfold] at hcomm'
  rw [hbr, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hCK : 0 ≤ Cs * Kb := mul_nonneg hCs hK0
  set A : ℝ := rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N rr)) +
    oNΛ d S.s C₀c (max Λ 1) N with hA'
  calc ENNReal.ofReal (1 / 2 * |centeredPairFunctional (commutatorKernel d (S.dyn N).s
        (fun x => Torus.matVec (S.dyn N).M.transpose (gradient (propagatorW (S.coeff N) rr t φ) x))) X
        (HRS.Whole.withDensityReal (S.ρ N rr))|)
      ≤ ENNReal.ofReal (1 / 2 * (Cs * Kb * (A + Cs * c.errorRate N))) :=
        ENNReal.ofReal_le_ofReal (by gcongr)
    _ = ENNReal.ofReal (1 / 2 * (Cs * Kb)) * ENNReal.ofReal (A + Cs * c.errorRate N) := by
        rw [← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring
    _ ≤ ENNReal.ofReal (1 / 2 * (Cs * Kb)) * (ENNReal.ofReal A + ENNReal.ofReal (Cs * c.errorRate N)) := by
        gcongr
        exact ENNReal.ofReal_add_le

end RemPt

end HRS.MS.DecStat
