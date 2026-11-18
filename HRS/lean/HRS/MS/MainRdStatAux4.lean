import HRS.MS.MainRdStatAux3
import HRS.Main.A8PAux21
import HRS.Main.A8PAux4
import HRS.MS.GenPathAux5

/-!
# SA2, packet 4: the remainder `R = σ ∫ ½ Comm_N(Mᵀ∇U^{r,t_a}φ_a)`

* `Sa2Comm`: the conclusion of S.B.5(i) (`whole_commutator_super`) at the log moment `Lm`, constants `(C₀ᶜ, Cq)`;
* `sa2_hasLip`: `Mᵀ∇f` is Lipschitz with constant `d²·MB·cbNorm 2 f`;
* `sa2_rem_ae`: a.s. `ofReal ‖Rem‖ ≤ ofReal cR · ∫⁻_0^T ofReal(F + o)` (the commutator bound at a.e. `r`);
* `sa2_rem_L1`, `sa2_rem_L2`: the moment bounds (`E‖Rem‖ ≤ cR T 𝔈_N`, `‖Rem‖_{L²} ≤ cR T 𝔈'_N`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open HRS HRS.Whole HRS.Whole.AppendixA
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.MainRdStat

variable {d : ℕ}

/-- The conclusion of S.B.5(i) at the log moment `Lm` and the constants `(C₀ᶜ, Cq)`. -/
def Sa2Comm (d : ℕ) (s Lm C₀c Cq : ℝ) : Prop :=
  ∀ Λ' : ℝ, 1 ≤ Λ' → ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ') →
    (s = 0 → HasLogMoment (HRS.Whole.withDensityReal ρ) Lm) →
    ∀ X : EucConfig d N, Function.Injective X →
    ∀ (v : Euc d → Euc d) (K : ℝ), HasLipBoundW v K →
      CommIntegrableW d s v X (HRS.Whole.withDensityReal ρ) ∧
      |commN d s v X (HRS.Whole.withDensityReal ρ)| ≤
        Cq * K * (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + oNΛ d s C₀c Λ' N)

theorem sa2_comm_data (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (hsc : (d : ℝ) - 2 ≤ s) (Lm : ℝ) :
    ∃ C₀ Cq : ℝ, 0 ≤ C₀ ∧ 0 < Cq ∧ Sa2Comm d s Lm C₀ Cq := by
  obtain ⟨C₀, C, h0, hC, h⟩ :=
    HRS.MH.CommSuper.whole_commutator_super_of_concentration_proof (d := d) hd hs0 hsd hsc Lm
  exact ⟨C₀, C, h0, hC, h⟩

/-! ### Lipschitz transport -/

theorem sa2_cMB_nonneg {MB : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : PDE.MatBound MB M) :
    0 ≤ (d : ℝ) * d * MB := by
  rcases Nat.eq_zero_or_pos d with h | h
  · subst h; simp
  · have : 0 ≤ MB := (abs_nonneg _).trans (hM ⟨0, h⟩ ⟨0, h⟩)
    positivity

theorem sa2_matBound_transpose {MB : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : PDE.MatBound MB M) :
    PDE.MatBound MB M.transpose := fun i j => by
  simpa [Matrix.transpose_apply] using hM j i

theorem sa2_hasLip {MB : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} (hM : PDE.MatBound MB M) {f : Euc d → ℝ}
    (hf : MemCb 2 f) {K : ℝ} (hK : cbNorm 2 f ≤ K) :
    HasLipBoundW (fun x => Torus.matVec M.transpose (gradient f x)) ((d : ℝ) * d * MB * K) := by
  have hc0 := sa2_cMB_nonneg hM
  have hcb0 := sa2_cbNorm_nonneg 2 f
  refine ⟨Real.toNNReal ((d : ℝ) * d * MB * cbNorm 2 f), ?_, ?_⟩
  · refine LipschitzWith.of_dist_le_mul fun x y => ?_
    rw [dist_eq_norm, dist_eq_norm, Real.coe_toNNReal _ (mul_nonneg hc0 hcb0)]
    have e1 : Torus.matVec M.transpose (gradient f x) - Torus.matVec M.transpose (gradient f y) =
        Torus.matVec M.transpose (gradient f x - gradient f y) := by
      simp only [Torus.matVec]; simp
    rw [e1]
    calc ‖Torus.matVec M.transpose (gradient f x - gradient f y)‖
        ≤ ((d : ℝ) * d * MB) * ‖gradient f x - gradient f y‖ :=
          HRS.Main.A8P.a8p_matVec_bound (sa2_matBound_transpose hM) _
      _ ≤ ((d : ℝ) * d * MB) * (cbNorm 2 f * ‖x - y‖) :=
          mul_le_mul_of_nonneg_left (HRS.MS.Go.s55_grad_lip_cb hf x y) hc0
      _ = (d : ℝ) * d * MB * cbNorm 2 f * ‖x - y‖ := by ring
  · rw [Real.coe_toNNReal _ (mul_nonneg hc0 hcb0)]
    exact mul_le_mul_of_nonneg_left hK hc0

/-! ### The energy integrand and the pointwise remainder bound -/

/-- `F_N(X_r, ρ_r) + o_N(C₀ᶜ, Λ̂)` along a path, with the clamped time (a jointly measurable version). -/
def sa2En (S : WholeMainData d) (R : ∀ N, RealizationRd d N) (N : ℕ) (C₀c Λ : ℝ) (ζ : (R N).Ω) (r : ℝ) : ℝ :=
  rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T r)) ζ)
    (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T r))) + oNΛ d S.s C₀c (max Λ 1) N

section Rem

variable {S : WholeMainData d} {R : ∀ N, RealizationRd d N} {MB Λ ΛV G₀ m20 C₀ : ℝ} {r mV : ℕ}
  {𝔈 : ℕ → ℝ}

theorem sa2_regSlice (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hr3 : 3 ≤ r) {N : ℕ} (hN : 1 ≤ N)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) S.T) : HRS.MH.DualityRd.RegSliceRd (S.ρ N t) := by
  obtain ⟨hm, hw, -⟩ := (sa2_regular_mono (hS.mean_field.regular N hN) hr3 le_rfl).1 t ht
  exact ⟨(hS.mean_field.solution N hN).density t ht, hm, hw⟩

/-- the commutator bound for one test at one `r`, in `ofReal` form. -/
theorem sa2_rem_pt (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hr3 : 3 ≤ r) (hd : 1 ≤ d)
    {N : ℕ} (hN : 2 ≤ N) {Lm C₀c Cq : ℝ} (hLm : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) S.T →
      HasLogMoment (HRS.Whole.withDensityReal (S.ρ N t)) Lm)
    (hcomm : Sa2Comm d S.s Lm C₀c Cq) (hCq : 0 ≤ Cq) {t : ℝ} {φ : Euc d → ℝ} {B : ℝ}
    {rr : ℝ} (hrr : rr ∈ Set.Icc (0 : ℝ) t) (htT : t ≤ S.T)
    (hmem : MemCb 2 (propagatorW (S.coeff N) rr t φ)) (hB : cbNorm 2 (propagatorW (S.coeff N) rr t φ) ≤ B)
    (X : EucConfig d N) (hX : Function.Injective X) :
    ENNReal.ofReal |flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) rr t φ) X (S.ρ N rr)| ≤
      ENNReal.ofReal (1 / 2 * (Cq * ((d : ℝ) * d * MB * B))) *
        ENNReal.ofReal (rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N rr)) +
          oNΛ d S.s C₀c (max Λ 1) N) := by
  have hrT : rr ∈ Set.Icc (0 : ℝ) S.T := ⟨hrr.1, hrr.2.trans htT⟩
  have hN1 : 1 ≤ N := by omega
  have hbr := HRS.MS.GenPath.s56_fluc_eq_comm (S.dyn N) hd S.hs0 S.hsd (sa2_regSlice hS hr3 hN1 hrT)
    hmem X
  have hlip := sa2_hasLip hS.matrix_bound hmem hB
  have hprob := (hS.mean_field.solution N hN1).density rr hrT
  have hρΛ : ∀ x, S.ρ N rr x ≤ max Λ 1 := fun x => (sa2_rho_le hS hN1 hrT x).trans (le_max_left _ _)
  have hc := (hcomm (max Λ 1) (le_max_right _ _) N hN _ hprob hρΛ (fun _ => hLm hrT) X hX _ _ hlip).2
  have hcomm' : |commN d S.s (fun x => Torus.matVec S.M.transpose
      (gradient (propagatorW (S.coeff N) rr t φ) x)) X (HRS.Whole.withDensityReal (S.ρ N rr))| ≤
      Cq * ((d : ℝ) * d * MB * B) * (rieszModulatedEnergy d S.s X (HRS.Whole.withDensityReal (S.ρ N rr)) +
        oNΛ d S.s C₀c (max Λ 1) N) := hc
  have hKB : 0 ≤ Cq * ((d : ℝ) * d * MB * B) := by
    have hB0 : 0 ≤ B := (sa2_cbNorm_nonneg 2 _).trans hB
    have := sa2_cMB_nonneg hS.matrix_bound
    positivity
  rw [hbr, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
  have hunfold : commN d S.s (fun x => Torus.matVec S.M.transpose
      (gradient (propagatorW (S.coeff N) rr t φ) x)) X (HRS.Whole.withDensityReal (S.ρ N rr)) =
      centeredPairFunctional (commutatorKernel d (S.dyn N).s (fun x => Torus.matVec (S.dyn N).M.transpose
        (gradient (propagatorW (S.coeff N) rr t φ) x))) X (HRS.Whole.withDensityReal (S.ρ N rr)) := rfl
  rw [hunfold] at hcomm'
  rw [← ENNReal.ofReal_mul (by positivity)]
  refine ENNReal.ofReal_le_ofReal ?_
  calc 1 / 2 * |centeredPairFunctional _ X _| ≤ 1 / 2 * (Cq * ((d : ℝ) * d * MB * B) * _) := by
        gcongr
    _ = 1 / 2 * (Cq * ((d : ℝ) * d * MB * B)) * _ := by ring


/-- the a.s. bound of the remainder vector by the energy integral -/
theorem sa2_rem_ae (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hr3 : 3 ≤ r) (hd : 1 ≤ d)
    {N : ℕ} (hN : 2 ≤ N) {Lm C₀c Cq : ℝ} (hLm : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) S.T →
      HasLogMoment (HRS.Whole.withDensityReal (S.ρ N t)) Lm)
    (hcomm : Sa2Comm d S.s Lm C₀c Cq) (hCq : 0 ≤ Cq) {q : ℕ} (ts : Fin q → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) {B : Fin q → ℝ}
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a)
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ rr ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal rr) ζ)) :
    ∀ᵐ ζ ∂(R N).P, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ≤
      ENNReal.ofReal (∑ a, S.sigma N * (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a)))) *
        ∫⁻ rr in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr) := by
  filter_upwards [hinj] with ζ hζ
  set G : ℝ≥0∞ := ∫⁻ rr in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr) with hG
  have hσ := sa2_sigma_nonneg S N
  have hc0 := sa2_cMB_nonneg hS.matrix_bound
  have hBa : ∀ a, 0 ≤ B a := fun a =>
    (sa2_cbNorm_nonneg 2 _).trans ((hB a (ts a) ⟨(hts a).1, le_rfl⟩).2)
  have hcoef : ∀ a, 0 ≤ S.sigma N * (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a))) := fun a => by
    have := hBa a
    positivity
  have hone : ∀ a, ENNReal.ofReal |(sa2Rem S R N ts φ ζ) a| ≤
      ENNReal.ofReal (S.sigma N * (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a)))) * G := by
    intro a
    have hta := hts a
    have hsub : Set.Icc (0 : ℝ) (ts a) ⊆ Set.Icc (0 : ℝ) S.T := Set.Icc_subset_Icc_right hta.2
    simp only [sa2Rem, PiLp.toLp_apply]
    set g : ℝ → ℝ := fun rr => flucInteractionRd (S.dyn N) (propagatorW (S.coeff N) rr (ts a) (φ a))
      ((R N).X (Real.toNNReal rr) ζ) (S.ρ N rr) with hg
    rw [abs_mul, abs_of_nonneg hσ, ENNReal.ofReal_mul hσ]
    have h1 : ENNReal.ofReal |∫ rr in Set.Icc (0 : ℝ) (ts a), g rr| ≤
        ∫⁻ rr in Set.Icc (0 : ℝ) (ts a), ENNReal.ofReal |g rr| := by
      have := enorm_integral_le_lintegral_enorm (μ := volume.restrict (Set.Icc (0 : ℝ) (ts a))) g
      simpa [Real.enorm_eq_ofReal_abs] using this
    have hae : ∀ᵐ rr ∂(volume.restrict (Set.Icc (0 : ℝ) (ts a))),
        ENNReal.ofReal |g rr| ≤ ENNReal.ofReal (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a))) *
          ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr) := by
      have h2 := ae_restrict_of_ae_restrict_of_subset hsub hζ
      filter_upwards [h2, ae_restrict_mem measurableSet_Icc] with rr hinjr hrr
      have hrT := hsub hrr
      have := sa2_rem_pt hS hr3 hd hN hLm hcomm hCq hrr hta.2
        (hB a rr hrr).1 (hB a rr hrr).2 ((R N).X (Real.toNNReal rr) ζ) hinjr
      simpa [sa2En, HRS.MP.RdRem.mrrClamp_of_mem hrT] using this
    calc ENNReal.ofReal (S.sigma N) * ENNReal.ofReal |∫ rr in Set.Icc (0 : ℝ) (ts a), g rr|
        ≤ ENNReal.ofReal (S.sigma N) * ∫⁻ rr in Set.Icc (0 : ℝ) (ts a), ENNReal.ofReal |g rr| := by
          gcongr
      _ ≤ ENNReal.ofReal (S.sigma N) * ∫⁻ rr in Set.Icc (0 : ℝ) (ts a),
            ENNReal.ofReal (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a))) *
              ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr) := by
          exact mul_le_mul' le_rfl (lintegral_mono_ae hae)
      _ = ENNReal.ofReal (S.sigma N) * (ENNReal.ofReal (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a))) *
            ∫⁻ rr in Set.Icc (0 : ℝ) (ts a), ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr)) := by
          rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
      _ ≤ ENNReal.ofReal (S.sigma N) * (ENNReal.ofReal (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a))) * G) := by
          exact mul_le_mul' le_rfl (mul_le_mul' le_rfl (lintegral_mono_set hsub))
      _ = ENNReal.ofReal (S.sigma N * (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a)))) * G := by
          rw [← mul_assoc, ← ENNReal.ofReal_mul hσ]
  calc ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖
      ≤ ENNReal.ofReal (∑ a, |(sa2Rem S R N ts φ ζ) a|) :=
        ENNReal.ofReal_le_ofReal (HRS.Main.A8P.a8p_norm_le_sum_abs _)
    _ = ∑ a, ENNReal.ofReal |(sa2Rem S R N ts φ ζ) a| :=
        ENNReal.ofReal_sum_of_nonneg fun a _ => abs_nonneg _
    _ ≤ ∑ a, ENNReal.ofReal (S.sigma N * (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a)))) * G :=
        Finset.sum_le_sum fun a _ => hone a
    _ = ENNReal.ofReal (∑ a, S.sigma N * (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a)))) * G := by
        rw [← Finset.sum_mul, ENNReal.ofReal_sum_of_nonneg fun a _ => hcoef a]

/-- joint measurability of the energy integrand -/
theorem sa2_en_meas (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) {N : ℕ} (hN : 1 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X)) (C₀c : ℝ) :
    Measurable fun p : (R N).Ω × ℝ => sa2En S R N C₀c Λ p.1 p.2 := by
  have hT : 0 ≤ S.T := S.hT.le
  have hm := HRS.MP.RdRem.mrr_prog_meas ℱ (R N).X hprog hT
  have hg : Measurable fun p : (R N).Ω × ℝ => (p.2, (R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T p.2)) p.1) :=
    measurable_snd.prodMk (hm.comp measurable_swap)
  have h1 := (HRS.MP.RdRem.mrr_energy_meas hS hN).comp hg
  have h2 : Measurable fun p : (R N).Ω × ℝ =>
      rieszModulatedEnergy d S.s ((R N).X (Real.toNNReal (HRS.MP.RdRem.mrrClamp S.T p.2)) p.1)
        (HRS.Whole.withDensityReal (S.ρ N (HRS.MP.RdRem.mrrClamp S.T p.2))) :=
    by simpa using h1.sub_const (oNΛ d S.s C₀ Λ N)
  exact (h2.add_const _)


theorem sa2_ofReal_sq_le (x : ℝ) : ENNReal.ofReal x ^ 2 ≤ ENNReal.ofReal (x ^ 2) := by
  by_cases hx : 0 ≤ x
  · rw [ENNReal.ofReal_pow hx]
  · push Not at hx
    simp [ENNReal.ofReal_of_nonpos hx.le]

theorem sa2_G_moment (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X)) {C₀c : ℝ}
    (hC₀c : 0 ≤ C₀c) (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) :
    ∫⁻ ζ, (∫⁻ rr in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr)) ∂(R N).P ≤
      ENNReal.ofReal (𝔈 N) * ENNReal.ofReal S.T := by
  have hN1 : 1 ≤ N := by omega
  refine HRS.MS.GenPath.s56_rem_moment_p1 (R N).P (fun ζ rr => sa2En S R N C₀c Λ ζ rr) ?_ ?_
  · exact (sa2_en_meas hS hN1 hprog C₀c).aemeasurable
  · intro rr hrr
    have := sa2_energy_bound hS hd hC₀c hC₀ hN1 hrr
    simpa [sa2En, HRS.MP.RdRem.mrrClamp_of_mem hrr] using this

theorem sa2_G_moment2 (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hd : 1 ≤ d) {N : ℕ} (hN : 2 ≤ N)
    {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X)) {C₀c : ℝ}
    (hC₀c : 0 ≤ C₀c) (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {χ : Euc d → ℝ} {m₀ : ℕ}
    {Ψ : ℕ → Set (Euc d → ℝ)} {𝔈' ε2 : ℕ → ℝ} (hE2 : EnergySmallness2Rd S R C₀ Λ χ m₀ Ψ 𝔈' ε2) :
    (∫⁻ ζ, (∫⁻ rr in Set.Icc (0 : ℝ) S.T, ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr)) ^ (2 : ℝ) ∂(R N).P) ^
        (1 / 2 : ℝ) ≤ ENNReal.ofReal (𝔈' N) * ENNReal.ofReal S.T := by
  have hN1 : 1 ≤ N := by omega
  refine HRS.MS.GenPath.s56_rem_moment_p2 (R N).P (fun ζ rr => sa2En S R N C₀c Λ ζ rr) ?_ ?_
  · exact (sa2_en_meas hS hN1 hprog C₀c).aemeasurable
  · intro rr hrr
    have hb := hE2.bound N hN1 rr hrr
    have hnn := hE2.𝔈'_nonneg N hN1
    calc ∫⁻ ζ, ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr) ^ (2 : ℝ) ∂(R N).P
        ≤ ∫⁻ ζ, ENNReal.ofReal ((correctedEnergyRd S C₀ Λ N ((R N).X (Real.toNNReal rr) ζ) rr) ^ 2)
            ∂(R N).P := by
          refine lintegral_mono fun ζ => ?_
          rw [ENNReal.rpow_two]
          refine le_trans (pow_le_pow_left' (ENNReal.ofReal_le_ofReal ?_) 2) (sa2_ofReal_sq_le _)
          simpa [sa2En, HRS.MP.RdRem.mrrClamp_of_mem hrr] using
            sa2_corrected_le hd S.hs0 (sa2_Lam_pos hS) hC₀c hC₀ hN1 ((R N).X (Real.toNNReal rr) ζ) rr
      _ ≤ ENNReal.ofReal ((𝔈' N) ^ 2) := hb
      _ = ENNReal.ofReal (𝔈' N) ^ (2 : ℝ) := by
          rw [ENNReal.rpow_two, ENNReal.ofReal_pow hnn]

theorem sa2_rem_L1 (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hr3 : 3 ≤ r) (hd : 1 ≤ d)
    {N : ℕ} (hN : 2 ≤ N) {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    {Lm C₀c Cq : ℝ} (hLm : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) S.T →
      HasLogMoment (HRS.Whole.withDensityReal (S.ρ N t)) Lm)
    (hcomm : Sa2Comm d S.s Lm C₀c Cq) (hCq : 0 ≤ Cq) (hC₀c : 0 ≤ C₀c)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {q : ℕ} (ts : Fin q → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) {B : Fin q → ℝ}
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a)
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ rr ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal rr) ζ)) :
    ∫⁻ ζ, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ∂(R N).P ≤
      ENNReal.ofReal (∑ a, S.sigma N * (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a)))) *
        (ENNReal.ofReal (𝔈 N) * ENNReal.ofReal S.T) := by
  refine (lintegral_mono_ae (sa2_rem_ae hS hr3 hd hN hLm hcomm hCq ts hts φ hB hinj)).trans ?_
  rw [lintegral_const_mul' _ _ ENNReal.ofReal_ne_top]
  exact mul_le_mul' le_rfl (sa2_G_moment hS hd hN hprog hC₀c hC₀)

theorem sa2_rem_L2 (hS : RdStanding S R MB Λ ΛV G₀ m20 r mV C₀ 𝔈) (hr3 : 3 ≤ r) (hd : 1 ≤ d)
    {N : ℕ} (hN : 2 ≤ N) {ℱ : Filtration ℝ (R N).mΩ} (hprog : IsProgressive ℱ (ofNNRealTime (R N).X))
    {Lm C₀c Cq : ℝ} (hLm : ∀ {t : ℝ}, t ∈ Set.Icc (0 : ℝ) S.T →
      HasLogMoment (HRS.Whole.withDensityReal (S.ρ N t)) Lm)
    (hcomm : Sa2Comm d S.s Lm C₀c Cq) (hCq : 0 ≤ Cq) (hC₀c : 0 ≤ C₀c)
    (hC₀ : sa2C0min d S.s Λ C₀c ≤ C₀) {q : ℕ} (ts : Fin q → ℝ)
    (hts : ∀ a, ts a ∈ Set.Icc (0 : ℝ) S.T) (φ : Fin q → Euc d → ℝ) {B : Fin q → ℝ}
    (hB : ∀ a, ∀ rr ∈ Set.Icc (0 : ℝ) (ts a), MemCb 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ∧
      cbNorm 2 (propagatorW (S.coeff N) rr (ts a) (φ a)) ≤ B a)
    (hinj : ∀ᵐ ζ ∂(R N).P, ∀ᵐ rr ∂(volume.restrict (Set.Icc (0 : ℝ) S.T)),
      Function.Injective ((R N).X (Real.toNNReal rr) ζ))
    {χ : Euc d → ℝ} {m₀ : ℕ} {Ψ : ℕ → Set (Euc d → ℝ)} {𝔈' ε2 : ℕ → ℝ}
    (hE2 : EnergySmallness2Rd S R C₀ Λ χ m₀ Ψ 𝔈' ε2) :
    (∫⁻ ζ, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ^ (2 : ℝ) ∂(R N).P) ^ (1 / 2 : ℝ) ≤
      ENNReal.ofReal (∑ a, S.sigma N * (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a)))) *
        (ENNReal.ofReal (𝔈' N) * ENNReal.ofReal S.T) := by
  set c : ℝ≥0∞ := ENNReal.ofReal (∑ a, S.sigma N * (1 / 2 * (Cq * ((d : ℝ) * d * MB * B a)))) with hc
  set G : (R N).Ω → ℝ≥0∞ := fun ζ => ∫⁻ rr in Set.Icc (0 : ℝ) S.T,
    ENNReal.ofReal (sa2En S R N C₀c Λ ζ rr) with hG
  have hae := sa2_rem_ae hS hr3 hd hN hLm hcomm hCq ts hts φ hB hinj
  have h1 : ∫⁻ ζ, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ^ (2 : ℝ) ∂(R N).P ≤
      ∫⁻ ζ, (c * G ζ) ^ (2 : ℝ) ∂(R N).P := by
    refine lintegral_mono_ae ?_
    filter_upwards [hae] with ζ hζ
    exact ENNReal.rpow_le_rpow hζ (by norm_num)
  have h2 : ∫⁻ ζ, (c * G ζ) ^ (2 : ℝ) ∂(R N).P = c ^ (2 : ℝ) * ∫⁻ ζ, (G ζ) ^ (2 : ℝ) ∂(R N).P := by
    rw [← lintegral_const_mul' _ _ (ENNReal.rpow_ne_top_of_nonneg (by norm_num) ENNReal.ofReal_ne_top)]
    refine lintegral_congr fun ζ => ?_
    rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 2)]
  have h3 := sa2_G_moment2 hS hd hN hprog hC₀c hC₀ hE2
  calc (∫⁻ ζ, ENNReal.ofReal ‖sa2Rem S R N ts φ ζ‖ ^ (2 : ℝ) ∂(R N).P) ^ (1 / 2 : ℝ)
      ≤ (c ^ (2 : ℝ) * ∫⁻ ζ, (G ζ) ^ (2 : ℝ) ∂(R N).P) ^ (1 / 2 : ℝ) := by
        gcongr
        exact h1.trans h2.le
    _ = c * (∫⁻ ζ, (G ζ) ^ (2 : ℝ) ∂(R N).P) ^ (1 / 2 : ℝ) := by
        rw [ENNReal.mul_rpow_of_nonneg _ _ (by norm_num : (0 : ℝ) ≤ 1 / 2), ← ENNReal.rpow_mul]
        norm_num
    _ ≤ c * (ENNReal.ofReal (𝔈' N) * ENNReal.ofReal S.T) := mul_le_mul' le_rfl h3

end Rem

end HRS.MS.MainRdStat
