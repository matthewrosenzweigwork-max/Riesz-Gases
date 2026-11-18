import HRS.MS.ZeroTempAux8

/-!
# SA11, packet C1c: the pathwise commutator bound along the adjoint orbit (S.B.5 with the adjoint input)

For `φ ∈ C_c^∞`, `N ≥ 2`, injective `X`, `0 ≤ r ≤ t ≤ T`:
`|Comm_N(Mᵀ∇U^{r,t}φ; X, ρ_N^r)| ≤ K_c ‖Jφ‖ (F_N(X,ρ_N^r) + oNΛ(C₀,Λ,N) (+ c₂ e_N))`,
with `K_c, c₂, C₀min` depending only on `d, s, fd, MB, Λ, Kad` (not on `S, N, X, r, t, φ`).
* `sa11_orbit_facts`: the data of `AdjointInputRd` at `(r,t,φ)`.
* `sa11_commBound_super`: `s ≥ d-2` (S.B.5(i), `Mᵀ∇U^{r,t}φ` is Lipschitz).
* `sa11_commBound_sub`: `s < d-2`, the admissible density `c` (S.B.5(ii),(iii), fractional transport bound).
-/

noncomputable section

open MeasureTheory
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.ZeroTemp

variable {d : ℕ} {m : ℕ} {p : ℝ} [Fact (2 ≤ p)]

/-- Facts about `f = U^{r,t}φ` from the adjoint input. -/
theorem sa11_orbit_facts {C : WholeCoeff d} {T K : ℝ} {r t : ℝ}
    (hA : AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) C T K) (hr : 0 ≤ r) (hrt : r ≤ t) (htT : t ≤ T)
    (φ : sa11_V d) :
    ContDiff ℝ ((mStar d : ℕ) : WithTop ℕ∞) (propagatorW C r t φ.1) ∧
    (∀ z, ‖iteratedFDeriv ℝ 2 (propagatorW C r t φ.1) z‖ ≤ K * (wClass m p).norm φ.1) ∧
    ∃ G : WmpSpace d m p, (∀ᵐ x ∂(volume : Measure (Euc d)),
        ((G : WLp d m p) : Euc d → (WIndex d m → ℝ)) x (wZero d m) = propagatorW C r t φ.1 x) ∧
      ‖G‖ ≤ K * (wClass m p).norm φ.1 := by
  obtain ⟨-, hmem, hnorm, hcb, hcbn⟩ := hA r t hr hrt htT φ.1 (sa11_cd2 φ.2) (sa11_wClass_mem φ)
  refine ⟨hcb.1, fun z => ?_, ?_⟩
  · exact (sa11_iter_le_cbNorm hcb (by unfold mStar; omega) z).trans hcbn
  · obtain ⟨G, hG⟩ := sa11_exists_weakJet hmem
    exact ⟨G, hG, by rw [← sa11_wWeak_norm_eq hG]; exact hnorm⟩

theorem sa11_hasLip_mono {v : Euc d → Euc d} {K K' : ℝ} (h : HasLipBoundW v K) (hK : K ≤ K') : HasLipBoundW v K' := by
  obtain ⟨L, hL, hLK⟩ := h
  exact ⟨L, hL, hLK.trans hK⟩

/-- the bound `Kad * ‖φ‖_{wClass} ≤ max Kad 0 * cJ * ‖Jφ‖`, and its sign -/
theorem sa11_wnorm_bound (Kad : ℝ) (φ : sa11_V d) :
    0 ≤ (wClass (d := d) m p).norm φ.1 ∧
    Kad * (wClass (d := d) m p).norm φ.1 ≤ max Kad 0 * (sa11_cJ d m * ‖sa11_J (m := m) (p := p) φ‖) := by
  have h0 : 0 ≤ (wClass (d := d) m p).norm φ.1 := ENNReal.toReal_nonneg
  refine ⟨h0, ?_⟩
  calc Kad * (wClass (d := d) m p).norm φ.1 ≤ max Kad 0 * (wClass (d := d) m p).norm φ.1 :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) h0
    _ ≤ max Kad 0 * (sa11_cJ d m * ‖sa11_J (m := m) (p := p) φ‖) :=
        mul_le_mul_of_nonneg_left (sa11_wClass_norm_le φ) (le_max_right _ _)

theorem sa11_density_prob {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {rs mV : ℕ}
    {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 rs mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N) {t : ℝ}
    (ht : t ∈ Set.Icc (0 : ℝ) S.T) : HRS.Whole.IsProbDensity (S.ρ N t) :=
  ((hS.mean_field.solution N hN).density t ht)

/-- `S.B.5 (i)`: the super-Coulomb range. -/
theorem sa11_commBound_super (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hsc : (d : ℝ) - 2 ≤ s)
    {Λ : ℝ} (hΛ : 0 < Λ) (MB Kad : ℝ) :
    ∃ C₀min Kc : ℝ, 0 ≤ Kc ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ →
      ∀ (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (ΛV G₀ m20 : ℝ) (rs mV : ℕ) (𝔈 : ℕ → ℝ),
        S.s = s → RdStanding S R MB Λ ΛV G₀ m20 rs mV C₀ 𝔈 →
        ∀ N : ℕ, 2 ≤ N → AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) (S.coeff N) S.T Kad →
        ∀ X : EucConfig d N, Function.Injective X → ∀ r₀ t : ℝ, 0 ≤ r₀ → r₀ ≤ t → t ≤ S.T → ∀ φ : sa11_V d,
        |commN d S.s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r₀ t φ.1) x)) X
            (HRS.Whole.withDensityReal (S.ρ N r₀))| ≤
          Kc * ‖sa11_J (m := m) (p := p) φ‖ *
            (rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N r₀)) + oNΛ d S.s C₀ Λ N) := by
  obtain ⟨Lm, hLm⟩ := HRS.MS.SuppU15.u15_logmoment (d := d) (L := (d : ℝ) + 3) (by linarith) Λ
  obtain ⟨C₀', C, hC₀', hC, H⟩ := HRS.MH.CommSuper.whole_commutator_super_of_concentration_proof hd hs0 hsd hsc Lm
  obtain ⟨C₀cmp, hcmp⟩ := sa11_oN_cmp hd hs0 C₀' Λ hΛ
  have hKc : 0 ≤ C * ((d : ℝ) ^ 2 * max MB 0) * (max Kad 0 * sa11_cJ d m) :=
    mul_nonneg (mul_nonneg hC.le (by positivity)) (mul_nonneg (le_max_right _ _) (sa11_cJ_nonneg d m))
  refine ⟨C₀cmp, C * ((d : ℝ) ^ 2 * max MB 0) * (max Kad 0 * sa11_cJ d m), hKc, ?_⟩
  intro C₀ hC₀ S R ΛV G₀ m20 rs mV 𝔈 hs hS N hN2 hA X hX r₀ t hr₀ hrt htT φ
  have hN1 : 1 ≤ N := by omega
  have hr0 : r₀ ∈ Set.Icc (0 : ℝ) S.T := ⟨hr₀, hrt.trans htT⟩
  obtain ⟨hf, hσ, -⟩ := sa11_orbit_facts hA hr₀ hrt htT φ
  obtain ⟨hw0, hw1⟩ := sa11_wnorm_bound (m := m) (p := p) Kad φ
  obtain ⟨hρle, hρw⟩ := sa11_density_facts hS hN1 hr0
  have hρprob := sa11_density_prob hS hN1 hr0
  have hf2 : ContDiff ℝ 2 (propagatorW (S.coeff N) r₀ t φ.1) :=
    hf.of_le (by exact_mod_cast (by unfold mStar; omega : 2 ≤ mStar d))
  have hσ0 : 0 ≤ Kad * (wClass m p).norm φ.1 := (norm_nonneg _).trans (hσ 0)
  have hlip := sa11_hasLipBound S.M.transpose hf2 hσ
  have hcM : HRS.MS.SuppU15.u15_cM S.M.transpose ≤ (d : ℝ) ^ 2 * max MB 0 :=
    sa11_cM_le (B := max MB 0) _ (fun i j => by
      have := hS.matrix_bound j i
      rw [Matrix.transpose_apply]
      exact this.trans (le_max_left _ _))
  set nJ : ℝ := ‖sa11_J (m := m) (p := p) φ‖ with hnJ
  set Kbig : ℝ := ((d : ℝ) ^ 2 * max MB 0) * (max Kad 0 * (sa11_cJ d m * nJ)) with hKbig
  have hcMnn := HRS.MS.SuppU15.u15_cM_nonneg S.M.transpose
  have hKle : HRS.MS.SuppU15.u15_cM S.M.transpose * (Kad * (wClass m p).norm φ.1) ≤ Kbig :=
    mul_le_mul hcM hw1 hσ0 (by positivity)
  have hlipK := sa11_hasLip_mono hlip hKle
  have hK0 : 0 ≤ Kbig := (mul_nonneg hcMnn hσ0).trans hKle
  rw [hs]
  have hlog := hLm (S.ρ N r₀) hρprob hρw
  obtain ⟨-, hb⟩ := H (max Λ 1) (le_max_right _ _) N hN2 (S.ρ N r₀) hρprob hρle (fun _ => hlog) X hX _ Kbig hlipK
  have hcmpN := hcmp C₀ hC₀ N hN1
  have hCK : 0 ≤ C * Kbig := mul_nonneg hC.le hK0
  calc |commN d s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r₀ t φ.1) x)) X
          (HRS.Whole.withDensityReal (S.ρ N r₀))|
      ≤ C * Kbig * (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (S.ρ N r₀)) + oNΛ d s C₀' (max Λ 1) N) := hb
    _ ≤ C * Kbig * (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (S.ρ N r₀)) + oNΛ d s C₀ Λ N) :=
        mul_le_mul_of_nonneg_left (by linarith) hCK
    _ = _ := by rw [hKbig]; ring

/-- regularity facts of an admissible density -/
theorem sa11_regularity_facts {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) (c : DecayingDensity d s) :
    0 < c.regularity ∧ ⌊c.regularity⌋₊ + 2 ≤ mStar d := by
  have hd2 : (2 : ℝ) < d := by linarith
  have key : 0 < c.regularity ∧ c.regularity < (d : ℝ) / 2 + 1 := by
    cases c with
    | sharp a ha =>
      obtain ⟨h1, h2⟩ := ha
      have h3 := (lt_min_iff.1 h2).1
      simp only [DecayingDensity.regularity]
      constructor <;> linarith
    | lower hs =>
      simp only [DecayingDensity.regularity]
      constructor <;> linarith
  obtain ⟨h1, h3⟩ := key
  refine ⟨h1, ?_⟩
  have hfl : ⌊c.regularity⌋₊ < d / 2 + 2 := by
    rw [Nat.floor_lt h1.le]
    have : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : d ≤ 2 * (d / 2) + 1)
    push_cast
    linarith
  unfold mStar
  omega

/-- the sub-Coulomb core: from an abstract form of S.B.5 (ii)/(iii). -/
theorem sa11_commBound_sub_core (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (c : DecayingDensity d s) {Λ : ℝ} (hΛ : 0 < Λ) (MB Kad : ℝ) {m : ℕ} (hmm : mStar d ≤ m)
    (hpc : p = c.integrability) (Lm : ℝ)
    (hLm : ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, jbracket x ^ ((d : ℝ) + 3) * |ρ x| ≤ max Λ 0) →
      HasLogMoment (HRS.Whole.withDensityReal ρ) Lm)
    (hSB : ∃ C₀' Cs : ℝ, 0 ≤ C₀' ∧ 0 < Cs ∧ ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ,
      HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ') → (s = 0 → HasLogMoment (HRS.Whole.withDensityReal ρ) Lm) →
      ∀ X : EucConfig d N, Function.Injective X → ∀ (v : Euc d → Euc d) (K : ℝ),
        HasFracTransportBound c.regularity c.integrability v K →
        |commN d s v X (HRS.Whole.withDensityReal ρ)| ≤
          Cs * K * (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + oNΛ d s C₀' Λ' N +
            Cs * c.errorRate N)) :
    ∃ C₀min Kc c₂ : ℝ, 0 ≤ Kc ∧ 0 ≤ c₂ ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ →
      ∀ (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (ΛV G₀ m20 : ℝ) (rs mV : ℕ) (𝔈 : ℕ → ℝ),
        S.s = s → RdStanding S R MB Λ ΛV G₀ m20 rs mV C₀ 𝔈 →
        ∀ N : ℕ, 2 ≤ N → AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) (S.coeff N) S.T Kad →
        ∀ X : EucConfig d N, Function.Injective X → ∀ r₀ t : ℝ, 0 ≤ r₀ → r₀ ≤ t → t ≤ S.T → ∀ φ : sa11_V d,
        |commN d S.s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r₀ t φ.1) x)) X
            (HRS.Whole.withDensityReal (S.ρ N r₀))| ≤
          Kc * ‖sa11_J (m := m) (p := p) φ‖ *
            (rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N r₀)) + oNΛ d S.s C₀ Λ N +
              c₂ * c.errorRate N) := by
  subst hpc
  obtain ⟨hα, hℓ⟩ := sa11_regularity_facts hs0 hsd c
  obtain ⟨Ctr, hCtr0, hTr⟩ := sa11_transport (m := m) (p := c.integrability) hd hα hℓ hmm
  obtain ⟨C₀', Cs, hC₀', hCs, H⟩ := hSB
  obtain ⟨C₀cmp, hcmp⟩ := sa11_oN_cmp hd hs0 C₀' Λ hΛ
  have hKc : 0 ≤ Cs * ((d : ℝ) ^ 2 * max MB 0 * (1 + Ctr)) * (max Kad 0 * sa11_cJ d m) :=
    mul_nonneg (mul_nonneg hCs.le (by positivity)) (mul_nonneg (le_max_right _ _) (sa11_cJ_nonneg d m))
  refine ⟨C₀cmp, Cs * ((d : ℝ) ^ 2 * max MB 0 * (1 + Ctr)) * (max Kad 0 * sa11_cJ d m), Cs, hKc, hCs.le, ?_⟩
  intro C₀ hC₀ S R ΛV G₀ m20 rs mV 𝔈 hs hS N hN2 hA X hX r₀ t hr₀ hrt htT φ
  have hN1 : 1 ≤ N := by omega
  have hr0 : r₀ ∈ Set.Icc (0 : ℝ) S.T := ⟨hr₀, hrt.trans htT⟩
  obtain ⟨hf, hσ, G, hG, hGn⟩ := sa11_orbit_facts hA hr₀ hrt htT φ
  obtain ⟨hw0, hw1⟩ := sa11_wnorm_bound (m := m) (p := c.integrability) Kad φ
  obtain ⟨hρle, hρw⟩ := sa11_density_facts hS hN1 hr0
  have hρprob := sa11_density_prob hS hN1 hr0
  have hσ0 : 0 ≤ Kad * (wClass m c.integrability).norm φ.1 := (norm_nonneg _).trans (hσ 0)
  have hcM : HRS.MS.SuppU15.u15_cM S.M.transpose ≤ (d : ℝ) ^ 2 * max MB 0 :=
    sa11_cM_le (B := max MB 0) _ (fun i j => by
      have := hS.matrix_bound j i
      rw [Matrix.transpose_apply]
      exact this.trans (le_max_left _ _))
  have hcMnn := HRS.MS.SuppU15.u15_cM_nonneg S.M.transpose
  set nJ : ℝ := ‖sa11_J (m := m) (p := c.integrability) φ‖ with hnJ
  set Kbig : ℝ := ((d : ℝ) ^ 2 * max MB 0 * (1 + Ctr)) * (max Kad 0 * (sa11_cJ d m * nJ)) with hKbig
  have htr := hTr S.M.transpose G _ (Kad * (wClass m c.integrability).norm φ.1) hf hG hσ
  have hKle : HRS.MS.SuppU15.u15_cM S.M.transpose *
      (Kad * (wClass m c.integrability).norm φ.1 + Ctr * ‖G‖) ≤ Kbig := by
    have h1 : Kad * (wClass m c.integrability).norm φ.1 + Ctr * ‖G‖ ≤ (1 + Ctr) * (max Kad 0 * (sa11_cJ d m * nJ)) := by
      have := mul_le_mul_of_nonneg_left hGn hCtr0
      nlinarith
    calc HRS.MS.SuppU15.u15_cM S.M.transpose * (Kad * (wClass m c.integrability).norm φ.1 + Ctr * ‖G‖)
        ≤ ((d : ℝ) ^ 2 * max MB 0) * ((1 + Ctr) * (max Kad 0 * (sa11_cJ d m * nJ))) :=
          mul_le_mul hcM h1 (by nlinarith [norm_nonneg G]) (by positivity)
      _ = _ := by rw [hKbig]; ring
  have hv := HRS.MS.SuppU15.u15_hasFrac_mono htr hKle
  have hK0 : 0 ≤ Kbig := by
    have := mul_nonneg hcMnn (add_nonneg hσ0 (mul_nonneg hCtr0 (norm_nonneg G)))
    exact this.trans hKle
  rw [hs]
  have hlog := hLm (S.ρ N r₀) hρprob hρw
  have hb := H (max Λ 1) (le_max_right _ _) N hN2 (S.ρ N r₀) hρprob hρle (fun _ => hlog) X hX _ Kbig hv
  have hcmpN := hcmp C₀ hC₀ N hN1
  have hCK : 0 ≤ Cs * Kbig := mul_nonneg hCs.le hK0
  calc |commN d s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r₀ t φ.1) x)) X
          (HRS.Whole.withDensityReal (S.ρ N r₀))|
      ≤ Cs * Kbig * (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (S.ρ N r₀)) +
          oNΛ d s C₀' (max Λ 1) N + Cs * c.errorRate N) := hb
    _ ≤ Cs * Kbig * (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal (S.ρ N r₀)) +
          oNΛ d s C₀ Λ N + Cs * c.errorRate N) :=
        mul_le_mul_of_nonneg_left (by linarith) hCK
    _ = _ := by rw [hKbig]; ring

/-- `S.B.5 (ii),(iii)`: the sub-Coulomb range. -/
theorem sa11_commBound_sub (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2)
    (c : DecayingDensity d s) {Λ : ℝ} (hΛ : 0 < Λ) (MB Kad : ℝ) {m : ℕ} (hmm : mStar d ≤ m)
    (hpc : p = c.integrability) :
    ∃ C₀min Kc c₂ : ℝ, 0 ≤ Kc ∧ 0 ≤ c₂ ∧ ∀ C₀ : ℝ, C₀min ≤ C₀ →
      ∀ (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (ΛV G₀ m20 : ℝ) (rs mV : ℕ) (𝔈 : ℕ → ℝ),
        S.s = s → RdStanding S R MB Λ ΛV G₀ m20 rs mV C₀ 𝔈 →
        ∀ N : ℕ, 2 ≤ N → AdjointInputRd (wClass m p) (wWeakClass m p) (mStar d) (S.coeff N) S.T Kad →
        ∀ X : EucConfig d N, Function.Injective X → ∀ r₀ t : ℝ, 0 ≤ r₀ → r₀ ≤ t → t ≤ S.T → ∀ φ : sa11_V d,
        |commN d S.s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r₀ t φ.1) x)) X
            (HRS.Whole.withDensityReal (S.ρ N r₀))| ≤
          Kc * ‖sa11_J (m := m) (p := p) φ‖ *
            (rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N r₀)) + oNΛ d S.s C₀ Λ N +
              c₂ * c.errorRate N) := by
  obtain ⟨Lm, hLm⟩ := HRS.MS.SuppU15.u15_logmoment (d := d) (L := (d : ℝ) + 3) (by linarith) Λ
  refine sa11_commBound_sub_core hd hs0 hsd c hΛ MB Kad hmm hpc Lm hLm ?_
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

end HRS.MS.ZeroTemp
