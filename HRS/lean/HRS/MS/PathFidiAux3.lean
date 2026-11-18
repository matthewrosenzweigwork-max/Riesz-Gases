import HRS.MS.PathFidiAux2

/-!
# SA26 packet P3: remainder, decomposition, martingale integrands, covariance density
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.PathFidi

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas

variable {d : ℕ}

/-! ### Selected flows: injectivity for a.e. time, or `M = 0` -/

theorem sa26_flow_inj {Ω : Type*} [MeasurableSpace Ω] {N : ℕ} {P : Measure Ω} {D : WholeDyn d} {T : ℝ}
    {X₀ : Ω → EucConfig d N} {W : ℝ≥0 → Ω → (Fin N → Euc d)} {X : ℝ≥0 → Ω → EucConfig d N}
    (h : SelectedFlowRd P D T X₀ W X) :
    (∀ᵐ ζ ∂P, ∀ᵐ r ∂(volume.restrict (Set.Icc (0 : ℝ) T)),
      Function.Injective (X (Real.toNNReal r) ζ)) ∨ D.M = 0 := by
  rcases h.flow with ⟨h1, -⟩ | ⟨-, -, -, -, h2⟩ | ⟨-, -, -, h3M, -⟩
  · left
    filter_upwards [h1.no_collision] with ζ hζ
    refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun r hr => ?_)
    intro i j hij
    by_contra hne
    exact hζ (Real.toNNReal r) (by rw [Real.coe_toNNReal _ hr.1]; exact hr.2) ⟨i, j, hne, hij⟩
  · left
    filter_upwards [h2.occupation] with ζ hζ
    have h3 := measure_eq_zero_iff_ae_notMem.1 hζ
    refine (ae_restrict_iff' measurableSet_Icc).2 ?_
    filter_upwards [h3] with r hr hrm
    intro i j hij
    by_contra hne
    exact hr ⟨hrm, ⟨i, j, hne, hij⟩⟩
  · right
    exact h3M

section Rem

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ} {𝔈 : ℕ → ℝ}

/-- `E ∫_0^{t} flucInteractionRd` is controlled by the energy: the pathwise commutator bound integrated in `ζ`. -/
theorem sa26_rem_L1 (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hr3 : 3 ≤ r)
    {Γ K' : ℝ} {e : ℕ → ℝ} (he : ∀ N, 0 ≤ e N) (hsel : SelectedCommutatorInput S Γ S.T K' C₀ Λ e)
    (hnn : ∀ N : ℕ, 2 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) S.T, ∀ X : EucConfig d N, Function.Injective X →
      0 ≤ rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N t)) + oNΛ d S.s C₀ Λ N)
    {N : ℕ} (hN : 2 ≤ N) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) {Γ' : ℝ} (hΓ : Γ ≤ Γ') {φ : Euc d → ℝ}
    (hφ : IsSobolevTest Γ' φ) :
    ∫⁻ ζ, ENNReal.ofReal |∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N)
        (propagatorW (S.coeff N) r t φ) ((R N).X (Real.toNNReal r) ζ) (S.ρ N r)| ∂(R N).P ≤
      ENNReal.ofReal (max K' 0 / 2 * HRS.Whole.sobolevNorm Γ' φ * S.T * (𝔈 N + e N)) := by
  classical
  have hN1 : 1 ≤ N := by omega
  have hT : 0 ≤ S.T := S.hT.le
  obtain ⟨ℱ, W', hF⟩ := hS.filtered N
  have hrew : ∀ ζ, ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N)
      (propagatorW (S.coeff N) r t φ) ((R N).X (Real.toNNReal r) ζ) (S.ρ N r) =
      (1 / 2 : ℝ) * ∫ r in (0 : ℝ)..t, commN d S.s
        (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r t φ) x))
        ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) := by
    intro ζ
    rw [intervalIntegral.integral_of_le ht.1, ← integral_Icc_eq_integral_Ioc, ← integral_const_mul]
    refine setIntegral_congr_fun measurableSet_Icc fun r hr => ?_
    rw [HRS.MS.GenPath.s56_fluc_eq_comm (S.dyn N) S.hd S.hs0 S.hsd
      (sa26_regSlice hS hr3 hN1 ⟨hr.1, hr.2.trans ht.2⟩)
      (HRS.MS.GenPath.s56_propagator_memCb (S.coeff N) t φ hr) _]
    rfl
  have hsel0 : 0 ≤ max K' 0 / 2 * HRS.Whole.sobolevNorm Γ' φ * S.T * (𝔈 N + e N) := by
    have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
    have : 0 ≤ HRS.Whole.sobolevNorm Γ' φ := Real.sqrt_nonneg _
    have := he N
    positivity
  rcases sa26_flow_inj (hS.flow N hN1) with hcase | hM0
  swap
  · -- `M = 0`: the commutator kernel vanishes
    have hz : ∀ ζ, ∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N)
        (propagatorW (S.coeff N) r t φ) ((R N).X (Real.toNNReal r) ζ) (S.ρ N r) = 0 := by
      intro ζ
      rw [hrew ζ]
      have : ∀ r : ℝ, commN d S.s
          (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r t φ) x))
          ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) = 0 := by
        intro r
        have hM0' : S.M = 0 := hM0
        simp [commN, centeredPairFunctional, commutatorKernel, hM0', Torus.matVec]
      simp [this]
    simp only [hz, abs_zero, ENNReal.ofReal_zero, lintegral_zero]
    exact bot_le
  have hXm := HRS.MP.RdRem.mrr_prog_meas ℱ (R N).X hF.progressive hT
  set Gc : ℝ → (R N).Ω → ℝ := fun r ζ =>
    rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T r)) ζ)
      (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T r))) + oNΛ d S.s C₀ Λ N + e N with hGc
  have hGm : Measurable fun p : ℝ × (R N).Ω => Gc p.1 p.2 :=
    ((HRS.MP.RdRem.mrr_energy_meas hS hN1).comp (measurable_fst.prodMk hXm)).add measurable_const
  have h𝔈 : 0 ≤ 𝔈 N := (hS.energy.pos N hN1).le
  have hmom : ∀ r ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ζ, ENNReal.ofReal (Gc r ζ) ∂(R N).P ≤ ENNReal.ofReal (𝔈 N + e N) := by
    intro r hr
    have hb := hS.energy.bound N hN1 r hr
    calc ∫⁻ ζ, ENNReal.ofReal (Gc r ζ) ∂(R N).P
        ≤ ∫⁻ ζ, (ENNReal.ofReal (correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal r) ζ) r) +
            ENNReal.ofReal (e N)) ∂(R N).P := by
          refine lintegral_mono fun ζ => ?_
          simp only [hGc, HRS.MP.RdRem.mrrClamp_of_mem hr]
          exact ENNReal.ofReal_add_le
      _ = ∫⁻ ζ, ENNReal.ofReal (correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal r) ζ) r) ∂(R N).P +
            ENNReal.ofReal (e N) := by
          rw [lintegral_add_right _ measurable_const, lintegral_const, measure_univ, mul_one]
      _ ≤ ENNReal.ofReal (𝔈 N) + ENNReal.ofReal (e N) := add_le_add hb le_rfl
      _ = ENNReal.ofReal (𝔈 N + e N) := (ENNReal.ofReal_add h𝔈 (he N)).symm
  have hZ := HRS.MP.RdRem.mrr_time_moment (R N).P Gc hGm _ hmom
  set Z : (R N).Ω → ℝ≥0∞ := fun ζ => ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (Gc r ζ) with hZdef
  set c : ℝ := max K' 0 / 2 * HRS.Whole.sobolevNorm Γ' φ with hc
  have hc0 : 0 ≤ c := by
    have : 0 ≤ HRS.Whole.sobolevNorm Γ' φ := Real.sqrt_nonneg _
    positivity
  have hpt : ∀ᵐ ζ ∂(R N).P, ENNReal.ofReal |∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N)
      (propagatorW (S.coeff N) r t φ) ((R N).X (Real.toNNReal r) ζ) (S.ρ N r)| ≤
      ENNReal.ofReal c * Z ζ := by
    filter_upwards [hcase] with ζ hinj
    rw [hrew ζ, abs_mul, abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 1 / 2),
      ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
    have hnn' : ∀ r ∈ Set.Icc (0 : ℝ) S.T, Function.Injective ((R N).X (Real.toNNReal r) ζ) →
        0 ≤ rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) +
          oNΛ d S.s C₀ Λ N + e N := fun r hr hinjr =>
      add_nonneg (hnn N hN r hr _ hinjr) (he N)
    have hb := HRS.MP.RdRem.mrr_path_bound S hsel hN (fun r => (R N).X (Real.toNNReal r) ζ) hnn' hinj
      ht hΓ hφ
    have hZeq : ∫⁻ r in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal
        (rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r)) +
          oNΛ d S.s C₀ Λ N + e N) = Z ζ := by
      refine setLIntegral_congr_fun measurableSet_Icc fun r hr => ?_
      simp only [hGc, HRS.MP.RdRem.mrrClamp_of_mem hr]
    rw [hZeq] at hb
    have hKc : 0 ≤ max K' 0 * HRS.Whole.sobolevNorm Γ' φ := mul_nonneg (le_max_right _ _) (Real.sqrt_nonneg _)
    calc ENNReal.ofReal (1 / 2) * ENNReal.ofReal |∫ r in (0 : ℝ)..t, commN d S.s
          (fun x => Torus.matVec S.M.transpose (gradient (propagatorW (S.coeff N) r t φ) x))
          ((R N).X (Real.toNNReal r) ζ) (HRS.Whole.withDensityReal (S.ρ N r))|
        ≤ ENNReal.ofReal (1 / 2) * (ENNReal.ofReal (max K' 0 * HRS.Whole.sobolevNorm Γ' φ) * Z ζ) :=
          by gcongr
      _ = ENNReal.ofReal c * Z ζ := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul (by norm_num : (0 : ℝ) ≤ 1 / 2)]
          congr 2
          rw [hc]; ring
  calc ∫⁻ ζ, ENNReal.ofReal |∫ r in Set.Icc (0 : ℝ) t, flucInteractionRd (S.dyn N)
        (propagatorW (S.coeff N) r t φ) ((R N).X (Real.toNNReal r) ζ) (S.ρ N r)| ∂(R N).P
      ≤ ∫⁻ ζ, ENNReal.ofReal c * Z ζ ∂(R N).P := lintegral_mono_ae hpt
    _ = ENNReal.ofReal c * ∫⁻ ζ, Z ζ ∂(R N).P := lintegral_const_mul' _ _ ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal c * (ENNReal.ofReal S.T * ENNReal.ofReal (𝔈 N + e N)) := by gcongr
    _ = ENNReal.ofReal (max K' 0 / 2 * HRS.Whole.sobolevNorm Γ' φ * S.T * (𝔈 N + e N)) := by
        have h2 : 0 ≤ 𝔈 N + e N := add_nonneg h𝔈 (he N)
        rw [← ENNReal.ofReal_mul hT, ← ENNReal.ofReal_mul hc0]
        congr 1
        rw [hc]; ring

end Rem


/-! ### The multi-time duality decomposition -/

section Decomp

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

/-- The adjoint orbit of the `a`-th test at particle number `N`. -/
def sa26_f (S : WholeMainData d) (N : ℕ) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) (a : Fin p) :
    ℝ → Euc d → ℝ := fun r => propagatorW (S.coeff N) r (ts a) (φ a)

/-- The Itô integrands `c_N 1_{[0,t_a]}(r) ∇U^{r,t_a}φ_a(X_i^r)`, `c_N = σ_N √(2β_N⁻¹)/N`. -/
def sa26_K (S : WholeMainData d) (N : ℕ) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) {Ω : Type*}
    (X : ℝ≥0 → Ω → EucConfig d N) (a : Fin p) : ℝ → Ω → (Fin N × Fin d) → ℝ :=
  fun r ζ => (S.sigma N * Real.sqrt (2 * S.invβ N) / N) •
    HRS.MH.DualityRd.truncGradIntegrand (ts a) (sa26_f S N ts φ a) X r ζ

/-- The scaled initial statistics. -/
def sa26_Iemp (S : WholeMainData d) (N : ℕ) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) {Ω : Type*}
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun a => S.sigma N *
    (HRS.Whole.pair (HRS.Whole.empirical (X 0 ζ)) (propagatorW (S.coeff N) 0 (ts a) (φ a)) -
      HRS.Whole.pair (HRS.Whole.withDensityReal (S.ρ N 0)) (propagatorW (S.coeff N) 0 (ts a) (φ a)))

/-- The scaled interaction remainders. -/
def sa26_Rem (S : WholeMainData d) (N : ℕ) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ) {Ω : Type*}
    (X : ℝ≥0 → Ω → EucConfig d N) (ζ : Ω) : EuclideanSpace ℝ (Fin p) :=
  WithLp.toLp 2 fun a => S.sigma N * ∫ r in Set.Icc (0 : ℝ) (ts a),
    flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) r (ts a) (φ a)) (X (Real.toNNReal r) ζ) (S.ρ N r)

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ} {𝔈 : ℕ → ℝ}

theorem sa26_vhyp_mono {mV : ℕ} {ΛV G₀ : ℝ} {V : Euc d → ℝ} (h : VHypRd mV ΛV G₀ V) (hm : 2 ≤ mV) :
    VHypRd 2 ΛV G₀ V :=
  ⟨h.1, fun j hj1 hj2 x => h.2.1 j hj1 (hj2.trans hm) x, h.2.2⟩

/-- the integrands are progressive and `L²` -/
theorem sa26_K_progL2 (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} {p : ℕ} (ts : Fin p → ℝ)
    (φ : Fin p → Euc d → ℝ) (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (hex : ∀ a, ∃ f, IsClassicalAdjointW (S.coeff N) (ts a) (φ a) f)
    {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X)) (a : Fin p) :
    IsProgressiveL2 (R N).P ℱ (sa26_K S N ts φ (R N).X a) := by
  have hf := (HRS.MS.Fcau.propagatorW_isClassical (hex a)).isC12TestRd
  exact (HRS.MH.DualityRd.isProgressiveL2_truncGrad_proof (hts a).1 hf hprog).smul _

theorem sa26_decomp (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hr : 3 ≤ r) (hmV : 2 ≤ mV)
    {N : ℕ} (hN : 1 ≤ N) {p : ℕ} (ts : Fin p → ℝ) (φ : Fin p → Euc d → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T)
    (hex : ∀ a, ∃ f, IsClassicalAdjointW (S.coeff N) (ts a) (φ a) f)
    {ℱ : Filtration ℝ (R N).mΩ} {W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ}
    (hF : IsWholeFilteredSolution (R N).P ℱ W' (R N).W (R N).X) :
    ∀ᵐ ζ ∂(R N).P, fluctStatRd (S.sigma N) (R N).X (S.ρ N) ts φ ζ =
      sa26_Iemp S N ts φ (R N).X ζ +
        vectorItoIntegral (R N).P ℱ W' (fun a => killAfter (sa26_K S N ts φ (R N).X a) (ts a)) S.T ζ +
        sa26_Rem S N ts φ (R N).X ζ := by
  have hSF := hS.flow N hN
  have hV := sa26_vhyp_mono hS.potential hmV
  have hdual := fun a => HRS.MH.DualityRd.duality_identity_rd_proof (N := N) S.s Λ S.T ΛV G₀ (S.dyn N)
    rfl S.hs0 S.hsd (S.hinvβ N) hV (S.ρ N) (hS.mean_field.solution N hN)
    (sa26_regular_mono hr (hS.mean_field.regular N hN)) (R N).P (R N).X₀ (R N).W (R N).X hSF ℱ W' hF
    (ts a) (hts a) (φ a) (sa26_f S N ts φ a) (HRS.MS.Fcau.propagatorW_isClassical (hex a))
  have hK := sa26_K_progL2 hS ts φ hts hex hF.progressive
  obtain ⟨-, hmart⟩ := several_times_covariation (R N).P hF.brownian
    (fun a => sa26_K S N ts φ (R N).X a) hK ts (fun a => (hts a).1) S.T (fun a => (hts a).2)
  have hsm := fun a => itoIntegral_smul hF.brownian
    (HRS.MH.DualityRd.isProgressiveL2_truncGrad_proof (hts a).1
      (HRS.MS.Fcau.propagatorW_isClassical (hex a)).isC12TestRd hF.progressive)
    (S.sigma N * Real.sqrt (2 * S.invβ N) / N)
  filter_upwards [hmart, ae_all_iff.2 hdual, ae_all_iff.2 hsm] with ζ h1 h2 h3
  ext a
  have hd := (h2 a) (ts a) ⟨(hts a).1, le_rfl⟩
  have hterm : sa26_f S N ts φ a (ts a) = φ a :=
    (HRS.MS.Fcau.propagatorW_isClassical (hex a)).terminal
  have e1 := h1 a
  have e3 := h3 a (ts a)
  simp only [fluctStatRd, sa26_Iemp, sa26_Rem, PiLp.add_apply, PiLp.toLp_apply]
  rw [hterm] at hd
  have hd2 := hd.2
  have hinv : (S.dyn N).invβ = S.invβ N := rfl
  rw [hinv] at hd2
  simp only [sa26_f] at hd2
  have e4 : itoIntegral (R N).P ℱ W' (sa26_K S N ts φ (R N).X a) (ts a) ζ =
      (S.sigma N * Real.sqrt (2 * S.invβ N) / N) * itoIntegral (R N).P ℱ W'
        (fun r ζ' (ia : Fin N × Fin d) => if r ∈ Set.Icc (0 : ℝ) (ts a) then
          gradComp ia.2 (propagatorW (S.coeff N) r (ts a) (φ a)) ((R N).X (Real.toNNReal r) ζ' ia.1)
          else 0) (ts a) ζ := e3
  rw [e1, e4]
  rw [hd2]
  ring

end Decomp


/-! ### The deterministic covariance density (port of `a8p_sigBar_*` to `ℝ^d`) -/

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

theorem sa26_s1Norm_le_sum {q : ℕ} (Q : Matrix (Fin q) (Fin q) ℝ) : s1Norm Q ≤ ∑ a, ∑ b, |Q a b| :=
  HRS.Main.A8P.a8p_s1Norm_le_sum Q

/-- The deterministic covariance density `Σ̄_r^{ab} = 1_{0 ≤ r < min(t_a,t_b)} c ∫ ⟨G_a(r),G_b(r)⟩ ρ_r`. -/
def sa26SigBar {q : ℕ} (ts : Fin q → ℝ) (G : Fin q → ℝ → Euc d → Euc d) (ρ : ℝ → Euc d → ℝ) (c : ℝ)
    (r : ℝ) : Matrix (Fin q) (Fin q) ℝ :=
  Matrix.of fun a b => if 0 ≤ r ∧ r < min (ts a) (ts b) then
    c * ∫ x, inner ℝ (G a r x) (G b r x) * ρ r x else 0

section SigBar

variable {q : ℕ} {ts : Fin q → ℝ} {G : Fin q → ℝ → Euc d → Euc d} {ρ : ℝ → Euc d → ℝ} {c : ℝ}

theorem sa26_sigBar_integrand_meas (hGm : ∀ a, Measurable fun p : ℝ × Euc d => G a p.1 p.2)
    (hρm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) (a b : Fin q) :
    Measurable fun p : ℝ × Euc d => inner ℝ (G a p.1 p.2) (G b p.1 p.2) * ρ p.1 p.2 :=
  ((hGm a).inner (hGm b)).mul hρm

theorem sa26_sigBar_integrable (hGm : ∀ a, Measurable fun p : ℝ × Euc d => G a p.1 p.2)
    (hρm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) {B : ℝ} (hGb : ∀ a r x, ‖G a r x‖ ≤ B)
    (hρ0 : ∀ r x, 0 ≤ ρ r x) (hρi : ∀ r, Integrable (ρ r)) (a b : Fin q) (r : ℝ) :
    Integrable (fun x => inner ℝ (G a r x) (G b r x) * ρ r x) := by
  refine Integrable.mono' ((hρi r).const_mul (B * B))
    ((sa26_sigBar_integrand_meas hGm hρm a b).comp measurable_prodMk_left).aestronglyMeasurable
    (Eventually.of_forall fun x => ?_)
  rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 r x)]
  have h1 : |inner ℝ (G a r x) (G b r x)| ≤ B * B :=
    (abs_real_inner_le_norm _ _).trans (mul_le_mul (hGb a r x) (hGb b r x) (norm_nonneg _)
      ((norm_nonneg _).trans (hGb a r x)))
  exact mul_le_mul_of_nonneg_right h1 (hρ0 r x)

theorem sa26_sigBar_entry_bound (hGm : ∀ a, Measurable fun p : ℝ × Euc d => G a p.1 p.2)
    (hρm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) {B : ℝ} (hGb : ∀ a r x, ‖G a r x‖ ≤ B)
    (hρ0 : ∀ r x, 0 ≤ ρ r x) (hρi : ∀ r, Integrable (ρ r)) (hρ1 : ∀ r, ∫ x, ρ r x ≤ 1)
    (a b : Fin q) (r : ℝ) :
    |sa26SigBar ts G ρ c r a b| ≤ |c| * (B * B) := by
  unfold sa26SigBar
  simp only [Matrix.of_apply]
  split_ifs with h
  · rw [abs_mul]
    refine mul_le_mul_of_nonneg_left ?_ (abs_nonneg _)
    refine (abs_integral_le_integral_abs).trans ?_
    have hbd : ∀ x, |inner ℝ (G a r x) (G b r x) * ρ r x| ≤ (B * B) * ρ r x := by
      intro x
      rw [abs_mul, abs_of_nonneg (hρ0 r x)]
      have h1 : |inner ℝ (G a r x) (G b r x)| ≤ B * B :=
        (abs_real_inner_le_norm _ _).trans (mul_le_mul (hGb a r x) (hGb b r x) (norm_nonneg _)
          ((norm_nonneg _).trans (hGb a r x)))
      exact mul_le_mul_of_nonneg_right h1 (hρ0 r x)
    have hB : 0 ≤ B * B := mul_self_nonneg B
    calc ∫ x, |inner ℝ (G a r x) (G b r x) * ρ r x| ≤ ∫ x, (B * B) * ρ r x :=
          integral_mono_of_nonneg (Eventually.of_forall fun x => abs_nonneg _)
            ((hρi r).const_mul _) (Eventually.of_forall hbd)
      _ = (B * B) * ∫ x, ρ r x := integral_const_mul _ _
      _ ≤ (B * B) * 1 := mul_le_mul_of_nonneg_left (hρ1 r) hB
      _ = B * B := mul_one _
  · simp only [abs_zero]
    have hB : 0 ≤ B := (norm_nonneg _).trans (hGb a r (0 : Euc d))
    positivity

theorem sa26_sigBar_entry_meas (hGm : ∀ a, Measurable fun p : ℝ × Euc d => G a p.1 p.2)
    (hρm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) (a b : Fin q) :
    Measurable fun r => sa26SigBar ts G ρ c r a b := by
  have hI : Measurable fun r : ℝ => ∫ x, inner ℝ (G a r x) (G b r x) * ρ r x := by
    have hsm : StronglyMeasurable fun p : ℝ × Euc d => inner ℝ (G a p.1 p.2) (G b p.1 p.2) * ρ p.1 p.2 :=
      (sa26_sigBar_integrand_meas hGm hρm a b).stronglyMeasurable
    exact (hsm.integral_prod_right' (ν := (volume : Measure (Euc d)))).measurable
  unfold sa26SigBar
  simp only [Matrix.of_apply]
  refine Measurable.ite ?_ (measurable_const.mul hI) measurable_const
  exact (measurableSet_le measurable_const measurable_id).inter (measurableSet_lt measurable_id measurable_const)

theorem sa26_sigBar_meas (hGm : ∀ a, Measurable fun p : ℝ × Euc d => G a p.1 p.2)
    (hρm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) : Measurable (sa26SigBar ts G ρ c) :=
  measurable_pi_iff.2 fun a => measurable_pi_iff.2 fun b => sa26_sigBar_entry_meas hGm hρm a b

theorem sa26_sigBar_psd (hGm : ∀ a, Measurable fun p : ℝ × Euc d => G a p.1 p.2)
    (hρm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) {B : ℝ} (hGb : ∀ a r x, ‖G a r x‖ ≤ B)
    (hρ0 : ∀ r x, 0 ≤ ρ r x) (hρi : ∀ r, Integrable (ρ r)) (hc : 0 ≤ c) (r : ℝ) :
    (sa26SigBar ts G ρ c r).PosSemidef := by
  by_cases hr : 0 ≤ r
  swap
  · have : sa26SigBar ts G ρ c r = 0 := by
      ext a b
      simp [sa26SigBar, hr]
    rw [this]
    exact Matrix.PosSemidef.zero
  set g : Fin q → Euc d → Euc d := fun a x => if r < ts a then G a r x else 0 with hg
  have hent : ∀ a b, sa26SigBar ts G ρ c r a b = c * ∫ x, inner ℝ (g a x) (g b x) * ρ r x := by
    intro a b
    unfold sa26SigBar
    simp only [Matrix.of_apply, hg]
    by_cases h1 : r < ts a
    · by_cases h2 : r < ts b
      · simp only [h1, h2, if_true, if_pos (show 0 ≤ r ∧ r < min (ts a) (ts b) from ⟨hr, lt_min h1 h2⟩)]
      · have : ¬ (0 ≤ r ∧ r < min (ts a) (ts b)) := fun h => h2 (lt_of_lt_of_le h.2 (min_le_right _ _))
        simp [h2, this]
    · have : ¬ (0 ≤ r ∧ r < min (ts a) (ts b)) := fun h => h1 (lt_of_lt_of_le h.2 (min_le_left _ _))
      simp [h1, this]
  have hgm : ∀ a, Measurable (g a) := by
    intro a
    by_cases h : r < ts a
    · simp only [hg, if_pos h]; exact (hGm a).comp measurable_prodMk_left
    · simp only [hg, if_neg h]; exact measurable_const
  have hgb : ∀ a x, ‖g a x‖ ≤ B := by
    intro a x
    by_cases h : r < ts a
    · simp only [hg, if_pos h]; exact hGb a r x
    · simp only [hg, if_neg h, norm_zero]
      exact (norm_nonneg _).trans (hGb a r (0 : Euc d))
  have hint : ∀ a b, Integrable (fun x => inner ℝ (g a x) (g b x) * ρ r x) := by
    intro a b
    refine Integrable.mono' ((hρi r).const_mul (B * B)) (((hgm a).inner (hgm b)).mul
      (hρm.comp measurable_prodMk_left)).aestronglyMeasurable (Eventually.of_forall fun x => ?_)
    rw [Real.norm_eq_abs, abs_mul, abs_of_nonneg (hρ0 r x)]
    have h1 : |inner ℝ (g a x) (g b x)| ≤ B * B :=
      (abs_real_inner_le_norm _ _).trans (mul_le_mul (hgb a x) (hgb b x) (norm_nonneg _)
        ((norm_nonneg _).trans (hgb a x)))
    exact mul_le_mul_of_nonneg_right h1 (hρ0 r x)
  refine Matrix.PosSemidef.of_dotProduct_mulVec_nonneg ?_ fun x => ?_
  · refine Matrix.IsHermitian.ext fun a b => ?_
    have hsym : ∀ y, inner ℝ (g b y) (g a y) = inner ℝ (g a y) (g b y) := fun y => real_inner_comm _ _
    simp only [star_trivial, hent, hsym]
  · simp only [star_trivial, dotProduct, Matrix.mulVec, hent]
    have e2 : ∑ a, x a * ∑ b, c * (∫ y, inner ℝ (g a y) (g b y) * ρ r y) * x b =
        c * ∫ y, ∑ a, ∑ b, (x a * x b) * (inner ℝ (g a y) (g b y) * ρ r y) := by
      rw [integral_finsetSum _ (fun a _ => integrable_finsetSum _ fun b _ => (hint a b).const_mul _)]
      rw [Finset.mul_sum]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [integral_finsetSum _ (fun b _ => (hint a b).const_mul _), Finset.mul_sum, Finset.mul_sum]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [integral_const_mul]; ring
    rw [e2]
    refine mul_nonneg hc (integral_nonneg fun y => ?_)
    have : ∑ a, ∑ b, (x a * x b) * (inner ℝ (g a y) (g b y) * ρ r y) =
        ‖∑ a, x a • g a y‖ ^ 2 * ρ r y := by
      rw [← real_inner_self_eq_norm_sq, sum_inner, Finset.sum_mul]
      refine Finset.sum_congr rfl fun a _ => ?_
      rw [inner_sum, Finset.sum_mul]
      refine Finset.sum_congr rfl fun b _ => ?_
      rw [real_inner_smul_left, real_inner_smul_right]; ring
    rw [this]
    exact mul_nonneg (sq_nonneg _) (hρ0 r y)

theorem sa26_sigBar_isDet (hGm : ∀ a, Measurable fun p : ℝ × Euc d => G a p.1 p.2)
    (hρm : Measurable fun p : ℝ × Euc d => ρ p.1 p.2) {B : ℝ} (hGb : ∀ a r x, ‖G a r x‖ ≤ B)
    (hρ0 : ∀ r x, 0 ≤ ρ r x) (hρi : ∀ r, Integrable (ρ r)) (hρ1 : ∀ r, ∫ x, ρ r x ≤ 1)
    (hc : 0 ≤ c) (T : ℝ) : IsDetCovMatrix T (sa26SigBar ts G ρ c) := by
  refine ⟨sa26_sigBar_meas hGm hρm, fun σ _ => sa26_sigBar_psd hGm hρm hGb hρ0 hρi hc σ, ?_⟩
  have hm : Measurable fun σ => s1Norm (sa26SigBar ts G ρ c σ) :=
    measurable_traceNormMatrix (sa26SigBar ts G ρ c) (fun i j => sa26_sigBar_entry_meas hGm hρm i j)
  refine Integrable.mono' (g := fun _ => ∑ _a : Fin q, ∑ _b : Fin q, |c| * (B * B))
    (integrable_const _) hm.aestronglyMeasurable ?_
  refine (ae_restrict_iff' measurableSet_Icc).2 (Eventually.of_forall fun σ _ => ?_)
  rw [Real.norm_of_nonneg (traceNormMatrix_nonneg _)]
  exact (sa26_s1Norm_le_sum _).trans (Finset.sum_le_sum fun a _ => Finset.sum_le_sum fun b _ =>
    sa26_sigBar_entry_bound hGm hρm hGb hρ0 hρi hρ1 a b σ)

end SigBar

end HRS.MS.PathFidi
