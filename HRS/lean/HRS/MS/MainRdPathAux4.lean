import HRS.MS.MainRdPathAux3
import HRS.MP.TightAssemble
import HRS.MP.RdInitClose

/-!
# S.A.9, packet P4: the tightness of the path laws from fixed-time tightness

`sa9_tight_of_fix`: with the decomposition `Z = Iq + Mq + Rm` (`sa9_decomp`), continuous versions `Ic` (S.A.23, as a
hypothesis), `Mc` (S.A.24(a) with the propagated second moment, `sa9_martingale_tight`) and the remainder bound
(S.A.25, `sa9_perN`, with a.e.-in-time injectivity of the flow instead of injectivity at each fixed time), the path laws
of the particle fields `Z_N` are tight (`HRS.MP.TightAsm.mta_tight`), provided the fixed-time marginals are tight.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.MainRdPath

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MP.RdMart HRS.MP.RdProp
  HRS.MP.HNegInfra HRS.MP.RdRem HRS.MS.MainRdField HRS.MH.DualityRd HRS.MP.RdGen HRS.MP.KC

variable {d : ℕ}

theorem sa9_standing_mono {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ}
    {r r' mV mV' : ℕ} {𝔈 : ℕ → ℝ} (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hr : r' ≤ r)
    (hm : mV' ≤ mV) : RdStanding S R MB Λ ΛV G₀ m20 r' mV' C₀ 𝔈 :=
  { flow := hS.flow
    mean_field :=
      { solution := hS.mean_field.solution
        datum := hS.mean_field.datum
        regular := fun N hN => sa6_regular_mono (hS.mean_field.regular N hN) hr
        time_derivative := hS.mean_field.time_derivative }
    matrix_bound := hS.matrix_bound
    potential := rg_VHyp_mono hS.potential hm le_rfl le_rfl
    energy := hS.energy
    second_moment := hS.second_moment
    filtered := hS.filtered }

section PerN

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}
  {Γ : ℕ}

/-- The per-`N` form of the remainder bound, with a.e.-in-time injectivity of the flow as hypothesis. -/
theorem sa9_perN (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 5) (Γ + 5) C₀ 𝔈) (hΛ : 1 ≤ Λ)
    {K' : ℝ} {e : ℕ → ℝ} (he : ∀ N, 0 ≤ e N)
    (hsel : SelectedCommutatorInput S (Γ : ℝ) S.T K' C₀ Λ e)
    {N : ℕ} (hN : 2 ≤ N)
    (hinjAE : ∀ᵐ ζ ∂(R N).P, ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal r) ζ))
    (Rm Rc : ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ))
    (hRem : IsRemainderW S R N (Γ + 2) Rm) (hCont : HasContVersion S.T (R N).P Rm Rc) :
    ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) S.T, ‖Rc t ζ‖ₑ ∂(R N).P ≤
      ENNReal.ofReal (max K' 0 / 2 * S.T * S.sigma N * (𝔈 N + e N)) := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hT : 0 ≤ S.T := S.hT.le
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  have hXm := mrr_prog_meas ℱ (R N).X hF.progressive hT
  set Gc : ℝ → (R N).Ω → ℝ := fun r ζ =>
    rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal (mrrClamp S.T r)) ζ)
      (HRS.Whole.withDensityReal (S.ρ N (mrrClamp S.T r))) + oNΛ d S.s C₀ Λ N + e N with hGc
  have hGm : Measurable fun p : ℝ × (R N).Ω => Gc p.1 p.2 :=
    ((mrr_energy_meas hS hN1).comp (measurable_fst.prodMk hXm)).add measurable_const
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  have hmom : ∀ r ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ζ, ENNReal.ofReal (Gc r ζ) ∂(R N).P ≤ ENNReal.ofReal (𝔈 N + e N) := by
    intro r hr
    have hb := hS.energy.bound N hN1 r hr
    calc ∫⁻ ζ, ENNReal.ofReal (Gc r ζ) ∂(R N).P
        ≤ ∫⁻ ζ, (ENNReal.ofReal (correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal r) ζ) r) +
            ENNReal.ofReal (e N)) ∂(R N).P := by
          refine lintegral_mono fun ζ => ?_
          simp only [hGc, mrrClamp_of_mem hr]
          exact ENNReal.ofReal_add_le
      _ = ∫⁻ ζ, ENNReal.ofReal (correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal r) ζ) r) ∂(R N).P +
            ENNReal.ofReal (e N) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (𝔈 N) + ENNReal.ofReal (e N) := add_le_add hb le_rfl
      _ = ENNReal.ofReal (𝔈 N + e N) := (ENNReal.ofReal_add h𝔈 (he N)).symm
  have hZ := mrr_time_moment (R N).P Gc hGm _ hmom
  set Z : (R N).Ω → ℝ≥0∞ := fun ζ => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (Gc r ζ) with hZdef
  set c : ℝ := S.sigma N / 2 * max K' 0 with hc
  have hσ := mrr_sigma_nonneg S N
  have hc0 : 0 ≤ c := mul_nonneg (by positivity) (le_max_right _ _)
  obtain ⟨φ, hφt, hφn, hnormF⟩ := HRS.MP.HNegInfra.hneg_norming d (((Γ + 2 : ℕ) : ℝ))
  have hΓle : (Γ : ℝ) ≤ ((Γ + 2 : ℕ) : ℝ) := by exact_mod_cast Nat.le_add_right Γ 2
  -- the pathwise bound for one time and one test
  have hpair : ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ n : ℕ, ∀ᵐ ζ ∂(R N).P,
      ENNReal.ofReal |HNeg.pairing (φ n) (Rc t ζ)| ≤ ENNReal.ofReal c * Z ζ := by
    intro t ht n
    filter_upwards [hCont.1 t ht, hRem.2 t ht (φ n) (hφt n), hinjAE] with ζ hRc hpairζ hinj
    rw [hRc, hpairζ]
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
    have hb := mrr_path_bound S hsel hN (fun r => (R N).X (Real.toNNReal r) ζ) hnn' hinj ht hΓle
      (hφt n)
    have hZeq : ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
        (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) +
          oNΛ d S.s C₀ Λ N + e N) = Z ζ := by
      refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp only [hGc, mrrClamp_of_mem hr]
    rw [hZeq] at hb
    rw [abs_mul, abs_of_nonneg (by positivity : (0 : ℝ) ≤ S.sigma N / 2),
      ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ S.sigma N / 2)]
    have h1 : ENNReal.ofReal (max K' 0 * HRS.Whole.sobolevNorm (((Γ + 2 : ℕ) : ℝ)) (φ n)) ≤
        ENNReal.ofReal (max K' 0) :=
      ENNReal.ofReal_le_ofReal (mul_le_of_le_one_right (le_max_right _ _) (hφn n))
    calc ENNReal.ofReal (S.sigma N / 2) * ENNReal.ofReal |∫ r in (0 : ℝ)..t,
          commN d S.s (fun x => Torus.matVec S.M.transpose
            (gradient (propagatorW (S.coeff N) r t (φ n)) x))
            ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r))|
        ≤ ENNReal.ofReal (S.sigma N / 2) * (ENNReal.ofReal (max K' 0) * Z ζ) := by
          gcongr
          exact hb.trans (by gcongr)
      _ = ENNReal.ofReal c * Z ζ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by positivity : (0 : ℝ) ≤ S.sigma N / 2)]
  -- the supremum over all times
  obtain ⟨D, hDc, hDd⟩ := TopologicalSpace.exists_countable_dense (Set.Icc (0 : ℝ) S.T)
  haveI : Countable D := hDc.to_subtype
  have hall : ∀ᵐ ζ ∂(R N).P, ∀ (t : D) (n : ℕ),
      ENNReal.ofReal |HNeg.pairing (φ n) (Rc t.1.1 ζ)| ≤ ENNReal.ofReal c * Z ζ :=
    ae_all_iff.2 fun t => ae_all_iff.2 fun n => hpair t.1.1 t.1.2 n
  have hsup : ∀ᵐ ζ ∂(R N).P, ⨆ t ∈ Set.Icc (0 : ℝ) S.T, ‖Rc t ζ‖ₑ ≤ ENNReal.ofReal c * Z ζ := by
    filter_upwards [hall, hCont.2] with ζ hζ hcont
    have hD : ∀ t : Set.Icc (0 : ℝ) S.T, t ∈ D → ‖Rc t.1 ζ‖ₑ ≤ ENNReal.ofReal c * Z ζ :=
      fun t ht => mrr_enorm_le (hnormF (Rc t.1 ζ)) _ (fun n => hζ ⟨t, ht⟩ n)
    have := mrr_closure_enorm D hDd (fun t => Rc t ζ) hcont _ hD
    exact iSup₂_le this
  calc ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) S.T, ‖Rc t ζ‖ₑ ∂(R N).P
      ≤ ∫⁻ ζ, ENNReal.ofReal c * Z ζ ∂(R N).P := lintegral_mono_ae hsup
    _ = ENNReal.ofReal c * ∫⁻ ζ, Z ζ ∂(R N).P := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal S.T * ENNReal.ofReal (𝔈 N + e N)) := by gcongr
    _ = ENNReal.ofReal (max K' 0 / 2 * S.T * S.sigma N * (𝔈 N + e N)) := by
        have h2 : 0 ≤ 𝔈 N + e N := add_nonneg h𝔈 (he N)
        rw [← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_mul hc0]
        congr 1
        rw [hc]; ring


end PerN

section Martingale

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}
  {Γ : ℕ} {C₁ m₂ : ℝ}

/-- Part (a) of `path_martingale_modulus_rd`, with the propagated second moment `m₂` in place of the energy bound
`Ē` (the `Θ_N` estimate only needs `sup_N sup_t E⟨|x|², μ_N^t⟩`). -/
theorem sa9_martingale_tight
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 5) (Γ + 5) C₀ 𝔈) (hm₂ : PropagatedSecondMoment S R m₂)
    (hker : ∀ N : ℕ, 1 ≤ N → KernelBoundRd (S.coeff N) S.T (Γ + 2) C₁)
    (ℱ : ∀ N, Filtration ℝ (R N).mΩ) (W' : ∀ N, ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ)
    (hfilt : ∀ N : ℕ, 1 ≤ N → IsWholeFilteredSolution (R N).P (ℱ N) (W' N) (R N).W (R N).X)
    (Mq : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ))
    (hMq : ∀ N : ℕ, 1 ≤ N → IsStochConvW (R N).P (ℱ N) (W' N) (S.coeff N)
      (S.sigma N * Real.sqrt (2 * S.invβ N) / N) (Γ + 2) S.T (R N).X (fun _ => S.T) (Mq N)) :
    ContVersionTight S.T (fun N => (R N).P) Mq (fun N => mkc_Zc (Mq N) S.T mrmR) := by
  classical
  have hT0 : 0 < S.T := S.hT
  set CLfun : ℝ → ℝ := fun L => mrmCb * (8 * (d : ℝ) ^ 2 * |C₁| ^ 4) * (4 * L ^ 2 * S.T ^ 2 + 1)
    with hCLfun
  -- the kernel families
  have hKex : ∀ N : ℕ, ∃ Kern : Fin d → ℝ → ℝ → Euc d → HNeg d ((Γ + 2 : ℕ) : ℝ),
      1 ≤ N → MrmKern (S.coeff N) S.T (Γ + 2) |C₁| Kern := by
    intro N
    by_cases hN : 1 ≤ N
    · obtain ⟨K, hK⟩ := mrmKern_exists (S.coeff N) S.T (Γ + 2) C₁ (hker N hN)
      exact ⟨K, fun _ => hK⟩
    · exact ⟨fun _ _ _ _ => 0, fun h => absurd h hN⟩
  choose Kern hKern using hKex
  -- second moment bound
  have hm2 : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∫⁻ ζ, ENNReal.ofReal
      (secondMomentOf (HRS.Whole.empirical ((R N).X (Real.toNNReal t) ζ))) ∂(R N).P ≤
        ENNReal.ofReal m₂ := by
    intro N hN t ht
    refine le_trans (lintegral_mono fun ζ => ENNReal.ofReal_le_ofReal ?_) (hm₂ N hN t ht)
    have := HRS.Whole.Q09A.secondMomentOf_nonneg (d := d) (HRS.Whole.withDensityReal (S.ρ N t))
    linarith
  have hcont : ∀ N : ℕ, 1 ≤ N → ∀ᵐ ζ ∂(R N).P, ∀ i, Continuous fun t : ℝ≥0 => (R N).X t ζ i :=
    fun N hN => mrm_flow_cont (hS.flow N hN)
  -- localized families
  have hex : ∀ (L N : ℕ), ∃ M : ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ), 1 ≤ L → 1 ≤ N →
      IsStochConvW (R N).P (ℱ N) (W' N) (S.coeff N) (S.sigma N * Real.sqrt (2 * S.invβ N) / N)
        (Γ + 2) S.T (R N).X (tauNL S.T (L : ℝ) (R N).X) M := by
    intro L N
    by_cases h : 1 ≤ L ∧ 1 ≤ N
    · have hLpos : (0 : ℝ) < (L : ℝ) := by exact_mod_cast h.1
      obtain ⟨M, hM⟩ := mrm_exists_stochConv (hfilt N h.2).brownian (hKern N h.2) _
        (tauNL S.T (L : ℝ) (R N).X) (R N).X (hfilt N h.2).progressive
        (mrm_tau_progressive (by omega) (hfilt N h.2).progressive hLpos)
      exact ⟨M, fun _ _ => hM⟩
    · exact ⟨fun _ _ => 0, fun h1 h2 => absurd ⟨h1, h2⟩ h⟩
  choose ZL hZL using hex
  have hA : ContVersionTight S.T (fun N => (R N).P) Mq (fun N => mkc_Zc (Mq N) S.T mrmR) := by
    refine mrm_kc_main S.T hT0 (fun N => (R N).P) Mq (fun N hN t => (hMq N hN).1 t)
      (S.T * (1 + max m₂ 0)) (fun L => CLfun (L : ℝ)) ZL
      (fun L N hL hN t => (hZL L N hL hN).1 t) ?_
      (fun L N => {ζ | tauNL S.T (L : ℝ) (R N).X ζ < S.T}) ?_ ?_
    · intro L N hL hN s' hs' t ht
      have hL1 : (1 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
      exact mrm_hmom_conv (fun ζ => ZL L N t ζ - ZL L N s' ζ) _ s' t
        (mrm_stopped_fourth (hfilt N hN).brownian (hKern N hN) _ (by omega)
          (mrm_cN_sq S (by omega)) (hfilt N hN).progressive (hcont N hN) hL1 hT0.le
          (hZL L N hL hN) hs' ht)
    · intro L N hL hN
      have hL1 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
      exact mrm_prob_bound (by omega) (hfilt N hN).progressive (hcont N hN) hT0.le hL1
        (hm2 N hN)
    · intro L N hL hN t ht
      have hL1 : (0 : ℝ) < (L : ℝ) := by exact_mod_cast hL
      exact mrm_agree (hfilt N hN).brownian (hKern N hN) _ (by omega) (hfilt N hN).progressive
        (hcont N hN) hL1 hT0.le (hMq N hN) (hZL L N hL hN) ht
  exact hA

end Martingale

section Tight

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {𝔈 : ℕ → ℝ}
  {Γ : ℕ} {C₁ m₂ K' : ℝ} {e : ℕ → ℝ}

theorem sa9_tight_of_fix
    (hS : RdStanding S R MB Λ ΛV G₀ m20 (Γ + 5) (Γ + 5) C₀ 𝔈) (hΛ : 1 ≤ Λ)
    (hm₂ : PropagatedSecondMoment S R m₂)
    (hker : ∀ N : ℕ, 1 ≤ N → KernelBoundRd (S.coeff N) S.T (Γ + 2) C₁)
    (he : ∀ N, 0 ≤ e N) (hsel : SelectedCommutatorInput S (Γ : ℝ) S.T K' C₀ Λ e)
    (hsmall : Tendsto (fun N => S.sigma N * (𝔈 N + e N)) atTop (𝓝 0))
    (Z Iq Mq Rm : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ))
    (ℱ : ∀ N, Filtration ℝ (R N).mΩ) (W' : ∀ N, ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ)
    (hfilt : ∀ N : ℕ, 1 ≤ N → IsWholeFilteredSolution (R N).P (ℱ N) (W' N) (R N).W (R N).X)
    (hMq : ∀ N : ℕ, 1 ≤ N → IsStochConvW (R N).P (ℱ N) (W' N) (S.coeff N)
      (S.sigma N * Real.sqrt (2 * S.invβ N) / N) (Γ + 2) S.T (R N).X (fun _ => S.T) (Mq N))
    (hRm : ∀ N : ℕ, 1 ≤ N → IsRemainderW S R N (Γ + 2) (Rm N))
    (hdec : ∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ ζ, Rm N t ζ = Z N t ζ - Iq N t ζ - Mq N t ζ)
    (hZm : ∀ N : ℕ, 1 ≤ N → ∀ t, Measurable (Z N t))
    (hZc : ∀ N : ℕ, 1 ≤ N → ∀ᵐ ζ ∂(R N).P, Continuous fun t : Set.Icc (0 : ℝ) S.T => Z N t.1 ζ)
    (Ic : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ))
    (hIc : ContVersionTight S.T (fun N => (R N).P) Iq Ic)
    (hfix : ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (R N).P.map (Z N t)}) :
    IsTightMeasureSet {μ | ∃ N : ℕ, 2 ≤ N ∧
      μ = (R N).P.map (fun ζ => contPathOf S.T (fun t => Z N t ζ))} := by
  classical
  have hT0 : 0 < S.T := S.hT
  have hMc := sa9_martingale_tight hS hm₂ hker ℱ W' hfilt Mq hMq
  set Mc : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ) := fun N => mkc_Zc (Mq N) S.T mrmR with hMcdef
  set Rc : ∀ N, ℝ → (R N).Ω → HNeg d ((Γ + 2 : ℕ) : ℝ) :=
    fun N t ζ => Z N t ζ - Ic N t ζ - Mc N t ζ with hRcdef
  have hHas : ∀ N : ℕ, 1 ≤ N → HasContVersion S.T (R N).P (Rm N) (Rc N) := by
    intro N hN
    refine ⟨fun t ht => ?_, ?_⟩
    · filter_upwards [hIc.1 N hN t ht, hMc.1 N hN t ht] with ζ h1 h2
      simp only [hRcdef]
      rw [hdec N hN t ht ζ, h1, h2]
    · filter_upwards [hZc N hN, hIc.2.1 N hN, hMc.2.1 N hN] with ζ h1 h2 h3
      exact continuousOn_iff_continuous_restrict.2 ((h1.sub h2).sub h3)
  have hsup : ∀ n : ℕ, 1 ≤ n → ∫⁻ ζ, ⨆ t ∈ Set.Icc (0 : ℝ) S.T,
      ‖Z (n + 1) t ζ - Ic (n + 1) t ζ - Mc (n + 1) t ζ‖ₑ ∂(R (n + 1)).P ≤
      ENNReal.ofReal (max K' 0 / 2 * S.T * S.sigma (n + 1) * (𝔈 (n + 1) + e (n + 1))) := fun n hn =>
    sa9_perN hS hΛ he hsel (by omega) (sa6_inj_N hS (by omega)) (Rm (n + 1)) (Rc (n + 1))
      (hRm (n + 1) (by omega)) (hHas (n + 1) (by omega))
  have hc : Tendsto (fun n : ℕ => max K' 0 / 2 * S.T * S.sigma (n + 1) * (𝔈 (n + 1) + e (n + 1)))
      atTop (𝓝 0) := by
    have h := (hsmall.comp (tendsto_add_atTop_nat 1)).const_mul (max K' 0 / 2 * S.T)
    simp only [mul_zero] at h
    refine h.congr fun n => ?_
    simp [mul_assoc]
  have hItight : ∀ ε : ℝ, 0 < ε → Tendsto (fun δ : ℝ =>
      ⨆ n : ℕ, ⨆ (_ : 1 ≤ n), (R (n + 1)).P {ζ | ENNReal.ofReal ε <
        omegaE (fun t => Ic (n + 1) t ζ) S.T δ}) (𝓝[>] 0) (𝓝 0) := fun ε hε =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hIc.2.2.2.1 ε hε)
      (fun δ => zero_le) (fun δ => iSup_le fun n => iSup_le fun hn =>
        le_iSup₂_of_le (n + 1) (by omega) le_rfl)
  have hMtight : ∀ ε : ℝ, 0 < ε → Tendsto (fun δ : ℝ =>
      ⨆ n : ℕ, ⨆ (_ : 1 ≤ n), (R (n + 1)).P {ζ | ENNReal.ofReal ε <
        omegaE (fun t => Mc (n + 1) t ζ) S.T δ}) (𝓝[>] 0) (𝓝 0) := fun ε hε =>
    tendsto_of_tendsto_of_tendsto_of_le_of_le tendsto_const_nhds (hMc.2.2.2.1 ε hε)
      (fun δ => zero_le) (fun δ => iSup_le fun n => iSup_le fun hn =>
        le_iSup₂_of_le (n + 1) (by omega) le_rfl)
  have hZpath : ∀ n : ℕ, 1 ≤ n →
      AEMeasurable (fun ζ => contPathOf S.T (fun t => Z (n + 1) t ζ)) (R (n + 1)).P := by
    intro n hn
    obtain ⟨Ξ, hΞm, -, hΞe⟩ := sa9_pathRepr (T := S.T) (R (n + 1)).P (Z (n + 1))
      (hZm (n + 1) (by omega)) (hZc (n + 1) (by omega))
    exact ⟨Ξ, hΞm, hΞe.mono fun ζ h => h.symm⟩
  have htightc := HRS.MP.TightAsm.mta_tight (E := HNeg d ((Γ + 2 : ℕ) : ℝ)) S.T hT0
    (Ω := fun n => (R (n + 1)).Ω) (fun n => (R (n + 1)).P) (fun n t ζ => Z (n + 1) t ζ)
    (fun n => Ic (n + 1)) (fun n => Mc (n + 1))
    (fun n hn t => hZm (n + 1) (by omega) t) (fun n hn => hZc (n + 1) (by omega))
    hZpath hItight hMtight
    (fun n => max K' 0 / 2 * S.T * S.sigma (n + 1) * (𝔈 (n + 1) + e (n + 1))) hc
    hsup
    (fun t ht => (hfix t ht).subset (by rintro _ ⟨n, hn, rfl⟩; exact ⟨n + 1, by omega, rfl⟩))
  refine htightc.subset ?_
  rintro _ ⟨N, hN, rfl⟩
  obtain ⟨n, rfl⟩ : ∃ n, N = n + 1 := ⟨N - 1, by omega⟩
  exact ⟨n, by omega, rfl⟩

end Tight

end HRS.MS.MainRdPath
