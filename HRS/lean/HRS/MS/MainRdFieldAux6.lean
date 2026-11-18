import HRS.MS.MainRdFieldAux5

/-!
# S.A.6, packet P4b: the pairing identity and the remainder bound

`sa6_pairing_identity`: for every smooth test `φ ∈ H^Γ` and a.e. `ζ`,
`⟨φ, Ξ - I' - M_t⟩ = (σ/2) ∫_0^t Comm_N(Mᵀ∇U^{r,t}φ; X_r, ρ_r) dr`, from `duality_identity_rd` at `τ = t` with the
adjoint solution `f^r = U^{r,t}φ`, linearity of the Itô integral in the constant `c_N`, and
`flucInteractionRd = ½ commN` (`s56_fluc_eq_comm`).

`sa6_remainder_pathwise` (a.e. `‖R‖ ≤ (σ/2)K' ∫_0^T (F + o + e)`) and `sa6_remainder_L1`
(`E‖R‖ ≤ ½ K' σ T (𝔈 + e)`) are the field version of `mrr_perN` (index `Γ`, one time `t`; the injectivity of the
configuration is only used for a.e. `r`, as an explicit hypothesis).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdField

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MS.GenPath HRS.MH.DualityRd HRS.MP.RdGen

variable {d : ℕ}

section Identity

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}
  {Γ : ℕ} {Kad : ℝ}

theorem sa6_pairing_identity
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 3) (Γ + 3) C₀ 𝔈)
    (hadj : AdjointDerivInput (Γ : ℝ) (mStar d) S.coeff S.T Kad)
    {N : ℕ} (hN : 1 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution (R N).P ℱ W' (R N).W (R N).X)
    {C₁ : ℝ} {Kern : Fin d → ℝ → ℝ → Euc d → HNeg d (Γ : ℝ)}
    (hK : Sa6Kern (S.coeff N) S.T Γ C₁ Kern)
    (M : ℝ → (R N).Ω → HNeg d (Γ : ℝ))
    (hMp : ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → ∀ᵐ ζ ∂(R N).P,
      HNeg.pairing φ (M t ζ) = itoIntegral (R N).P ℱ W'
        (mrmPhi (S.coeff N) (sa6_cN S N) t (fun _ => S.T) (R N).X φ) t ζ)
    (Ξ I' : (R N).Ω → HNeg d (Γ : ℝ))
    (hΞ : ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → ∀ᵐ ζ ∂(R N).P,
      HNeg.pairing φ (Ξ ζ) = S.sigma N *
        (HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ)) φ - HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) φ))
    (hI' : ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → ∀ᵐ ζ ∂(R N).P,
      HNeg.pairing φ (I' ζ) = S.sigma N *
        (HRS.Whole.pair (HRS.Whole.empirical ((R N).X 0 ζ)) (propagatorW (S.coeff N) 0 t φ) -
          HRS.Whole.pair S.μ0 (propagatorW (S.coeff N) 0 t φ)))
    (φ : Euc d → ℝ) (hφ : IsSobolevTest (Γ : ℝ) φ) :
    ∀ᵐ ζ ∂(R N).P, HNeg.pairing φ (Ξ ζ - I' ζ - M t ζ) = (S.sigma N / 2) * ∫ r in (0 : ℝ)..t,
      commN d S.s (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r t φ) x))
        ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) := by
  have hT0 : 0 ≤ S.T := S.hT.le
  have hd1 : 1 ≤ d := S.hd
  have hadjN := hadj N hN
  have hex : ∃ f, IsClassicalAdjointW (S.coeff N) t φ f :=
    (hadjN t t ht.1 le_rfl ht.2 φ hφ).1
  have hf := sa6_classical_prop hex
  have hV : VHypRd 2 ΛV G₀ (S.dyn N).V :=
    rg_VHyp_mono hS.potential (by omega) le_rfl le_rfl
  have hreg : IsRegularMFRd S.s 3 Λ S.T (S.ρ N) :=
    sa6_regular_mono (hS.mean_field.regular N hN) (by omega)
  have hflow := hS.flow N hN
  have hdual := HRS.MH.DualityRd.duality_identity_rd_proof S.s Λ S.T ΛV G₀ (S.dyn N) rfl S.hs0 S.hsd
    (S.hinvβ N) hV (S.ρ N) (hS.mean_field.solution N hN) hreg (R N).P (R N).X₀ (R N).W (R N).X
    hflow ℱ W' hF t ht φ (fun r => propagatorW (S.coeff N) r t φ) hf
  unfold DualityIdentityRd at hdual
  -- the Itô integral of the truncated gradient
  have hΦ : IsProgressiveL2 (R N).P ℱ
      (mrmPhi (S.coeff N) 1 t (fun _ => S.T) (R N).X φ) := by
    refine IsProgressiveL2.of_bounded (R N).P (isProgressive_pi (fun ia =>
      mrmPhi_progressive 1 ht.2 (fun _ => S.T) (R N).X hF.progressive (sa6_tau_prog ℱ S.T) φ ia))
      (|Kad| * HRS.Whole.sobolevNorm (Γ : ℝ) φ) fun r ζ ia => ?_
    unfold mrmPhi
    by_cases h : r ∈ Set.Icc (0 : ℝ) t ∧ r ≤ S.T
    · simp only [if_pos h, one_mul]
      exact (sa6_grad_bound hadjN h.1.1 h.1.2 ht.2 hφ _ _).trans
        (mul_le_mul_of_nonneg_right (le_abs_self _) (Real.sqrt_nonneg _))
    · simp only [if_neg h, abs_zero]
      exact mul_nonneg (abs_nonneg _) (Real.sqrt_nonneg _)
  have hsmul := itoIntegral_smul hF.brownian hΦ (sa6_cN S N)
  have hmrm : (mrmPhi (S.coeff N) (sa6_cN S N) t (fun _ => S.T) (R N).X φ) =
      fun s ω => (sa6_cN S N) • mrmPhi (S.coeff N) 1 t (fun _ => S.T) (R N).X φ s ω := by
    funext s ω ia
    unfold mrmPhi
    by_cases h : s ∈ Set.Icc (0 : ℝ) t ∧ s ≤ S.T <;> simp [h]
  have htrunc : truncGradIntegrand t (fun r => propagatorW (S.coeff N) r t φ) (R N).X =
      mrmPhi (S.coeff N) 1 t (fun _ => S.T) (R N).X φ := by
    funext r ζ ia
    unfold truncGradIntegrand mrmPhi gradComp
    by_cases h : r ∈ Set.Icc (0 : ℝ) t
    · have h' : r ∈ Set.Icc (0 : ℝ) t ∧ r ≤ S.T := ⟨h, h.2.trans ht.2⟩
      simp [h, h']
    · have h' : ¬ (r ∈ Set.Icc (0 : ℝ) t ∧ r ≤ S.T) := fun hh => h hh.1
      simp [h, h']
  filter_upwards [hdual, hsmul, hMp φ hφ, hΞ φ hφ, hI' φ hφ] with ζ hd hsm hM hΞ' hI''
  obtain ⟨-, hid⟩ := hd t ⟨ht.1, le_rfl⟩
  have hft : propagatorW (S.coeff N) t t φ = φ := sa6_prop_terminal hex
  have hdat : HRS.Whole.withDensityReal (S.ρ N 0) = S.μ0 := hS.mean_field.datum N hN
  have hMF : MFData S.s Λ S.T ΛV G₀ (S.dyn N) (S.ρ N) :=
    ⟨rfl, S.hs0, S.hsd, S.hinvβ N, hV, hS.mean_field.solution N hN, hreg⟩
  have hJ : ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N)
        (propagatorW (S.coeff N) r t φ) ((R N).X (Real.toNNReal r) ζ) (S.ρ N r) =
      (1 / 2) * ∫ r in (0 : ℝ)..t, commN d S.s
        (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r t φ) x))
        ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) := by
    rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    have hrT : r ∈ Set.Icc (0 : ℝ) S.T := ⟨hr.1, hr.2.trans ht.2⟩
    exact s56_fluc_eq_comm (S.dyn N) hd1 S.hs0 S.hsd (hMF.regSlice hrT)
      (s56_propagator_memCb (S.coeff N) t φ hr) _
  change HRS.Whole.pair (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ)) (propagatorW (S.coeff N) t t φ) -
      HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N t)) (propagatorW (S.coeff N) t t φ) =
    (HRS.Whole.pair (HRS.Whole.empirical ((R N).X 0 ζ)) (propagatorW (S.coeff N) 0 t φ) -
      HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0)) (propagatorW (S.coeff N) 0 t φ)) +
    (Real.sqrt (2 * S.invβ N) / N) * itoIntegral (R N).P ℱ W'
      (truncGradIntegrand t (fun r => propagatorW (S.coeff N) r t φ) (R N).X) t ζ +
    ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) r t φ)
      ((R N).X (Real.toNNReal r) ζ) (S.ρ N r) at hid
  rw [htrunc, hft, hdat, hJ] at hid
  have hM' : HNeg.pairing φ (M t ζ) = sa6_cN S N * itoIntegral (R N).P ℱ W'
      (mrmPhi (S.coeff N) 1 t (fun _ => S.T) (R N).X φ) t ζ := by
    rw [hM, hmrm]; exact hsm t
  rw [mhn_pairing_sub hφ, mhn_pairing_sub hφ, hΞ', hI'', hM', hid]
  unfold sa6_cN
  ring

end Identity

section Remainder

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}
  {Γ : ℕ}

/-- The corrected-energy integrand along the particle path, at the clamped time. -/
def sa6_Gc (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (N : ℕ) (C₀ Λ : ℝ) (e : ℕ → ℝ) :
    ℝ → (R N).Ω → ℝ := fun r ζ =>
  rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal (mrrClamp S.T r)) ζ)
    (HRS.Whole.withDensityReal (S.ρ N (mrrClamp S.T r))) + oNΛ d S.s C₀ Λ N + e N

theorem sa6_remainder_pathwise
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 3) (Γ + 3) C₀ 𝔈) (hΛ : 1 ≤ Λ) {K' : ℝ} {e : ℕ → ℝ}
    (he : ∀ N, 0 ≤ e N) (hsel : SelectedCommutatorInput S (Γ : ℝ) S.T K' C₀ Λ e) {N : ℕ}
    (hN : 2 ≤ N)
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal r) ζ))
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) (Rr : (R N).Ω → HNeg d (Γ : ℝ))
    (hRid : ∀ φ : Euc d → ℝ, IsSobolevTest (Γ : ℝ) φ → ∀ᵐ ζ ∂(R N).P,
      HNeg.pairing φ (Rr ζ) = (S.sigma N / 2) * ∫ r in (0 : ℝ)..t, commN d S.s
        (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r t φ) x))
        ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r))) :
    ∀ᵐ ζ ∂(R N).P, ‖Rr ζ‖ₑ ≤ ENNReal.ofReal (S.sigma N / 2 * max K' 0) *
      ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (sa6_Gc S R N C₀ Λ e r ζ) := by
  classical
  have hN1 : 1 ≤ N := by omega
  obtain ⟨φ, hφt, hφn, hnormF⟩ := hneg_norming d (Γ : ℝ)
  have hσ := mrr_sigma_nonneg S N
  set c : ℝ := S.sigma N / 2 * max K' 0 with hc
  have hc0 : 0 ≤ c := mul_nonneg (by positivity) (le_max_right _ _)
  have hpair : ∀ n : ℕ, ∀ᵐ ζ ∂(R N).P, ENNReal.ofReal |HNeg.pairing (φ n) (Rr ζ)| ≤
      ENNReal.ofReal c * ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (sa6_Gc S R N C₀ Λ e r ζ) := by
    intro n
    filter_upwards [hRid (φ n) (hφt n), hinj] with ζ hpairζ hinjζ
    rw [hpairζ]
    have hnn' : ∀ r ∈ Set.Icc (0 : ℝ) S.T, Function.Injective ((R N).X (Real.toNNReal r) ζ) →
        0 ≤ rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ)
          (HRS.Whole.withDensityReal (S.ρ N r)) + oNΛ d S.s C₀ Λ N + e N := by
      intro r hr hinjr
      have hreg := (hS.mean_field.regular N hN1).1 r hr
      have hrho := (hS.mean_field.solution N hN1).density r hr
      have hle : ∀ x, S.ρ N r x ≤ Λ := fun x =>
        ((le_abs_self _).trans (mrr_abs_le_cbNorm hreg.1 x)).trans
          (le_trans (le_add_of_nonneg_right ENNReal.toReal_nonneg) hreg.2.2)
      have hcomp := hS.energy.completion.2 Λ hΛ N hN (S.ρ N r) hrho hle
        (fun _ => Q09A.log_integrable_withDensityReal hrho
          ((hS.mean_field.solution N hN1).second_moment r hr))
        ((R N).X (Real.toNNReal r) ζ) (fun ⟨i, j, hij, heq⟩ => hij (hinjr heq))
      exact add_nonneg hcomp (he N)
    have hb := mrr_path_bound S hsel hN (fun r => (R N).X (Real.toNNReal r) ζ) hnn' hinjζ ht
      (le_refl (Γ : ℝ)) (hφt n)
    have hZeq : ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (sa6_Gc S R N C₀ Λ e r ζ) =
        ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
          (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) +
            oNΛ d S.s C₀ Λ N + e N) := by
      refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp only [sa6_Gc, mrrClamp_of_mem hr]
    rw [hZeq]
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ S.sigma N / 2),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ S.sigma N / 2)]
    have h1 : ENNReal.ofReal (max K' 0 * HRS.Whole.sobolevNorm (Γ : ℝ) (φ n)) ≤
        ENNReal.ofReal (max K' 0) :=
      ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (le_max_right _ _) (hφn n))
    calc ENNReal.ofReal (S.sigma N / 2) * ENNReal.ofReal |∫ r in (0 : ℝ)..t,
          commN d S.s (fun x => Torus.matVec S.M.transpose
            (gradient (propagatorW (S.coeff N) r t (φ n)) x))
            ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r))|
        ≤ ENNReal.ofReal (S.sigma N / 2) * (ENNReal.ofReal (max K' 0) *
            ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
              (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) +
                oNΛ d S.s C₀ Λ N + e N)) := by
          gcongr
          exact hb.trans (by gcongr)
      _ = ENNReal.ofReal c * _ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ S.sigma N / 2)]
  filter_upwards [ae_all_iff.2 hpair] with ζ hζ
  exact mrr_enorm_le (hnormF (Rr ζ)) _ hζ

theorem sa6_remainder_L1
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 3) (Γ + 3) C₀ 𝔈) {e : ℕ → ℝ} (he : ∀ N, 0 ≤ e N)
    {N : ℕ} (hN : 1 ≤ N) {c : ℝ} (hc0 : 0 ≤ c) (Rr : (R N).Ω → HNeg d (Γ : ℝ))
    (hpath : ∀ᵐ ζ ∂(R N).P, ‖Rr ζ‖ₑ ≤ ENNReal.ofReal c *
      ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (sa6_Gc S R N C₀ Λ e r ζ))
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution (R N).P ℱ W' (R N).W (R N).X) :
    ∫⁻ ζ, ‖Rr ζ‖ₑ ∂(R N).P ≤ ENNReal.ofReal (c * S.T * (𝔈 N + e N)) := by
  have hT : 0 ≤ S.T := S.hT.le
  have hXm := mrr_prog_meas ℱ (R N).X hF.progressive hT
  have hGm : Measurable fun p : ℝ × (R N).Ω => sa6_Gc S R N C₀ Λ e p.1 p.2 :=
    ((mrr_energy_meas hS hN).comp (measurable_fst.prodMk hXm)).add measurable_const
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN).le
  have hmom : ∀ r ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ζ, ENNReal.ofReal (sa6_Gc S R N C₀ Λ e r ζ) ∂(R N).P ≤ ENNReal.ofReal (𝔈 N + e N) := by
    intro r hr
    have hb := hS.energy.bound N hN r hr
    calc ∫⁻ ζ, ENNReal.ofReal (sa6_Gc S R N C₀ Λ e r ζ) ∂(R N).P
        ≤ ∫⁻ ζ, (ENNReal.ofReal (correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal r) ζ) r) +
            ENNReal.ofReal (e N)) ∂(R N).P := by
          refine lintegral_mono fun ζ => ?_
          simp only [sa6_Gc, mrrClamp_of_mem hr]
          exact ENNReal.ofReal_add_le
      _ = ∫⁻ ζ, ENNReal.ofReal (correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal r) ζ) r) ∂(R N).P +
            ENNReal.ofReal (e N) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (𝔈 N) + ENNReal.ofReal (e N) := add_le_add hb le_rfl
      _ = ENNReal.ofReal (𝔈 N + e N) := (ENNReal.ofReal_add h𝔈 (he N)).symm
  have hZ := mrr_time_moment (T := S.T) (R N).P (sa6_Gc S R N C₀ Λ e) hGm _ hmom
  calc ∫⁻ ζ, ‖Rr ζ‖ₑ ∂(R N).P
      ≤ ∫⁻ ζ, ENNReal.ofReal c *
          (∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (sa6_Gc S R N C₀ Λ e r ζ)) ∂(R N).P :=
        lintegral_mono_ae hpath
    _ = ENNReal.ofReal c * ∫⁻ ζ, (∫⁻ r in Set.Icc (0 : ℝ) S.T,
          ENNReal.ofReal (sa6_Gc S R N C₀ Λ e r ζ)) ∂(R N).P :=
        lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal S.T * ENNReal.ofReal (𝔈 N + e N)) := by gcongr
    _ = ENNReal.ofReal (c * S.T * (𝔈 N + e N)) := by
        have h2 : 0 ≤ 𝔈 N + e N := add_nonneg h𝔈 (he N)
        rw [← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_mul hc0, mul_assoc]

end Remainder

end HRS.MS.MainRdField
