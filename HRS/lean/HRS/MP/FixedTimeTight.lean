import HRS.Main.TorusTheorems
import HRS.Main.A9Final
import HRS.Main.A9Aux2
import HRS.Main.A8PAux7
import HRS.Main.GFB1Aux1
import HRS.Main.GFEVAux7
import HRS.Sections.AdjKBAux1
import HRS.Sections.AdjKAAux11

/-!
# Packet MPFTT: fixed-time tightness from the A.9 first-moment bound

* `mpt_isTight_of_bound`: a family of random elements `Z n` of `E_{m₁}` with a uniform bound on
  `E ‖Z n‖_{E_{m₁}}` has tight laws in `E_m` (`m₁ < m`), via the compact sublevel sets of
  `adjkEnergy m₁ m` and Markov's inequality.
* `mpt_fixed_time_tight_torus`: the consequence of Proposition A.9 (`main_torus_field_proof`) at a fixed
  time: the laws of the rescaled fluctuation fields `σ_N Ξ_N^t` are tight in `H^{-(γ+2)}(𝕋^d)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MP.FixedTimeTight

open HRS HRS.GF HRS.Uniform HRS.Main HRS.AdjK

variable {d : ℕ}

/-- The continuous linear inclusion `E_{m₁} ↪ E_m` (`m₁ ≤ m`), of norm `≤ 1`. -/
def mpt_embedCLM {m₁ m : ℝ} (hmm : m₁ ≤ m) : NegSobolev d m₁ →L[ℝ] NegSobolev d m :=
  LinearMap.mkContinuous (gfevEmbL hmm) 1 (fun F => by
    change ‖NegSobolev.embed m F‖ ≤ 1 * ‖F‖
    rw [one_mul]
    exact NegSobolev.norm_embed_le m hmm F)

theorem mpt_embedCLM_apply {m₁ m : ℝ} (hmm : m₁ ≤ m) (F : NegSobolev d m₁) :
    mpt_embedCLM hmm F = NegSobolev.embed m F := rfl

/-- General tightness criterion: uniformly bounded `E_{m₁}`-moments give tight laws of the embedded
random elements in `E_m`, `m₁ < m`. -/
theorem mpt_isTight_of_bound {m₁ m : ℝ} (hm : m₁ < m) {Ω : ℕ → Type*} [∀ n, MeasurableSpace (Ω n)]
    (P : ∀ n, Measure (Ω n)) (Z : ∀ n, Ω n → NegSobolev d m₁) (W : ∀ n, Ω n → NegSobolev d m)
    (hZ : ∀ n : ℕ, 1 ≤ n → AEMeasurable (Z n) (P n))
    (hW : ∀ n : ℕ, 1 ≤ n → ∀ ω, W n ω = NegSobolev.embed m (Z n ω))
    (B : ℝ) (hB : ∀ n : ℕ, 1 ≤ n → ∫⁻ ω, ‖Z n ω‖ₑ ∂(P n) ≤ ENNReal.ofReal B) :
    IsTightMeasureSet {μ | ∃ n : ℕ, 1 ≤ n ∧ μ = (P n).map (W n)} := by
  have hWe : ∀ n : ℕ, 1 ≤ n → W n = fun ω => NegSobolev.embed m (Z n ω) :=
    fun n hn => funext (hW n hn)
  have hset : {μ | ∃ n : ℕ, 1 ≤ n ∧ μ = (P n).map (W n)} =
      {μ | ∃ n : ℕ, 1 ≤ n ∧ μ = (P n).map (fun ω => NegSobolev.embed m (Z n ω))} := by
    ext μ
    constructor
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, by rw [hWe n hn]⟩
    · rintro ⟨n, hn, rfl⟩
      exact ⟨n, hn, by rw [hWe n hn]⟩
  rw [hset, isTightMeasureSet_iff_exists_isCompact_measure_compl_le]
  intro ε hε
  obtain ⟨r, hr0, hrlt, hrε⟩ := ENNReal.lt_iff_exists_real_btwn.1 hε
  have hr : 0 < r := ENNReal.ofReal_pos.1 hrlt
  set Rr : ℝ := (max B 0 + 1) / r with hRr
  have hRpos : 0 < Rr := div_pos (by have := le_max_right B 0; linarith) hr
  have hrR : r * Rr = max B 0 + 1 := by
    rw [hRr]; field_simp
  refine ⟨{F : NegSobolev d m | adjkEnergy m₁ m F ≤ ENNReal.ofReal (Rr ^ 2)},
    adjkb_ball_isCompact (d := d) m m₁ Rr hm, ?_⟩
  rintro μ ⟨n, hn, rfl⟩
  have hEmb : Measurable (fun z : NegSobolev d m₁ => NegSobolev.embed m z) :=
    (mpt_embedCLM hm.le).continuous.measurable
  have hf : AEMeasurable (fun ω => NegSobolev.embed m (Z n ω)) (P n) :=
    hEmb.comp_aemeasurable (hZ n hn)
  have hKc : MeasurableSet
      ({F : NegSobolev d m | adjkEnergy m₁ m F ≤ ENNReal.ofReal (Rr ^ 2)})ᶜ :=
    (adjkb_ball_isCompact (d := d) m m₁ Rr hm).isClosed.isOpen_compl.measurableSet
  rw [Measure.map_apply_of_aemeasurable hf hKc]
  have hsub : (fun ω => NegSobolev.embed m (Z n ω)) ⁻¹'
      ({F : NegSobolev d m | adjkEnergy m₁ m F ≤ ENNReal.ofReal (Rr ^ 2)})ᶜ ⊆
      {ω | ENNReal.ofReal Rr ≤ ‖Z n ω‖ₑ} := by
    intro ω hω
    simp only [Set.mem_preimage, Set.mem_compl_iff, Set.mem_setOf_eq] at hω
    rw [adjka_energy_embed' hm.le, not_le] at hω
    simp only [Set.mem_setOf_eq]
    by_contra hlt
    push_neg at hlt
    have hsq : ‖Z n ω‖ₑ ^ 2 ≤ ENNReal.ofReal Rr ^ 2 := by gcongr
    rw [← ENNReal.ofReal_pow hRpos.le] at hsq
    exact absurd hsq (not_le.2 hω)
  have hnorm : AEMeasurable (fun ω => ‖Z n ω‖ₑ) (P n) :=
    continuous_enorm.measurable.comp_aemeasurable (hZ n hn)
  have hmul : ENNReal.ofReal (max B 0) ≤ ENNReal.ofReal r * ENNReal.ofReal Rr := by
    rw [← ENNReal.ofReal_mul hr0]
    exact ENNReal.ofReal_le_ofReal (by rw [hrR]; linarith)
  calc (P n) ((fun ω => NegSobolev.embed m (Z n ω)) ⁻¹'
          ({F : NegSobolev d m | adjkEnergy m₁ m F ≤ ENNReal.ofReal (Rr ^ 2)})ᶜ)
      ≤ (P n) {ω | ENNReal.ofReal Rr ≤ ‖Z n ω‖ₑ} := measure_mono hsub
    _ ≤ (∫⁻ ω, ‖Z n ω‖ₑ ∂(P n)) / ENNReal.ofReal Rr :=
        meas_ge_le_lintegral_div hnorm (ENNReal.ofReal_pos.2 hRpos).ne'
          ENNReal.ofReal_ne_top
    _ ≤ ENNReal.ofReal (max B 0) / ENNReal.ofReal Rr :=
        ENNReal.div_le_div_right ((hB n hn).trans (ENNReal.ofReal_le_ofReal (le_max_left B 0))) _
    _ ≤ ENNReal.ofReal r := ENNReal.div_le_of_le_mul hmul
    _ ≤ ε := hrε.le

/-- Fourier coefficients of the embedded measure difference (`d < 2m`). -/
theorem mpt_embed_smul_ofMeasureDiff {m m' : ℝ} (hmm : m ≤ m') (hm : (d : ℝ) < 2 * m)
    (hm' : (d : ℝ) < 2 * m') (σ : ℝ) (μ ν : Measure (Torus d)) [IsFiniteMeasure μ]
    [IsFiniteMeasure ν] :
    NegSobolev.embed m' (σ • NegSobolev.ofMeasureDiff m μ ν) =
      σ • NegSobolev.ofMeasureDiff m' μ ν := by
  refine gfev_ext fun k => ?_
  rw [gfev_coord_embed hmm, gfev_fc_smul, gfev_coord_smul, coord_ofMeasureDiff hm' μ ν k,
    NegSobolev.fourierCoeff_ofMeasureDiff hm μ ν k]
  ring

/-- Measurability of `ω ↦ σ • ofMeasureDiff γ (empirical (X t ω)) (ρ t)` (template:
`mpf_fluc_cont_meas` in `HRS/MP/FlucPath.lean`). -/
theorem mpt_fluc_measurable {S : HRS.Main.MainData d} {R : ∀ N, HRS.Main.Realization d N}
    {Rg : HRS.PDE.Regime} {ν₀ MB Λ VB C₀ Cc : ℝ} {𝔈 : ℕ → ℝ}
    (hS : HRS.Main.TorusStanding S R Rg ν₀ MB Λ VB (HRS.PDE.mStar d) C₀ Cc 𝔈)
    {N : ℕ} (hN : 1 ≤ N) (γ : ℝ) (hγ : (d : ℝ) / 2 < γ) (t : ℝ) :
    Measurable fun ω => S.sigma N • NegSobolev.ofMeasureDiff γ
      (HRS.empirical ((R N).X (Real.toNNReal t) ω)) (HRS.withDensityReal (S.ρ N t)) := by
  have hX := (HRS.Main.A8P.a8p_flow_facts hS hN).1
  refine (measurable_const_smul (S.sigma N)).comp ?_
  exact (HRS.GF.gf_measurable_ofMeasureDiff_proof (N := N) γ hγ _).comp (hX.adapted _)

/-- Proposition A.9 consequence: fixed-time tightness of the laws of `σ_N Ξ_N^t` in `H^{-(γ+2)}(𝕋^d)`
(`γ = gammaIdx d`), under the hypotheses of `main_torus_field`. -/
theorem mpt_fixed_time_tight_torus (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ),
        TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d + 2) C₀ Cc 𝔈 →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuation S R m₀ Cin ε (fun _ => ∅) →
        ∀ (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ))
          (νin : Measure (NegSobolev d (gammaIdx d : ℝ))),
          InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          IsTightMeasureSet {μ | ∃ N : ℕ, 1 ≤ N ∧ μ = (R N).P.map (fun ω =>
            S.sigma N • NegSobolev.ofMeasureDiff ((gammaIdx d + 2 : ℕ) : ℝ)
              (empirical ((R N).X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t)))} := by
  obtain ⟨C₀min, h9⟩ := HRS.Main.main_torus_field_proof (d := d) s
  refine ⟨C₀min, fun Rg ν₀ MB Λ T VB Cin C₀ Cc hC S hs hT R 𝔈 hstand m₀ ε hinit εf ηF νin hfield t ht => ?_⟩
  obtain ⟨C, ΛT, -, -, hmain⟩ := h9 Rg ν₀ MB Λ T VB Cin C₀ Cc hC
  have hstand9 : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈 :=
    HRS.Main.A9.a9_standing_mono (by omega) hstand
  have hstandM : TorusStanding S R Rg ν₀ MB Λ VB (HRS.PDE.mStar d) C₀ Cc 𝔈 :=
    HRS.Main.A9.a9_standing_mono (by
      have hγdef : HRS.PDE.mStar d + d + 3 = gammaIdx d := rfl
      omega) hstand
  obtain ⟨B, hB⟩ := (hmain S hs hT R 𝔈 hstand9 m₀ ε hinit εf ηF νin hfield t ht).2
  have htS : t ∈ Set.Icc (0 : ℝ) S.T := by rw [hT]; exact ht
  -- real forms of the index bounds
  have hγdef : HRS.PDE.mStar d + d + 3 = gammaIdx d := rfl
  have hγR : (gammaIdx d : ℝ) = (HRS.PDE.mStar d : ℝ) + d + 3 := by
    rw [← hγdef]; push_cast; ring
  have hmS0 : (0 : ℝ) ≤ (HRS.PDE.mStar d : ℝ) := Nat.cast_nonneg _
  have hd0 : (0 : ℝ) ≤ (d : ℝ) := Nat.cast_nonneg _
  have hγ0 : (d : ℝ) / 2 < (gammaIdx d : ℝ) := by rw [hγR]; linarith
  have hγ2 : (d : ℝ) < 2 * ((gammaIdx d + 2 : ℕ) : ℝ) := by
    push_cast; rw [hγR]; linarith
  have hγ0' : (d : ℝ) < 2 * (gammaIdx d : ℝ) := by rw [hγR]; linarith
  have hlt : ((gammaIdx d : ℕ) : ℝ) < ((gammaIdx d + 2 : ℕ) : ℝ) := by
    exact_mod_cast (by omega : gammaIdx d < gammaIdx d + 2)
  refine mpt_isTight_of_bound hlt (Ω := fun N => (R N).Ω)
    (fun N => (R N).P)
    (fun N ω => S.sigma N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
      (empirical ((R N).X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t)))
    (fun N ω => S.sigma N • NegSobolev.ofMeasureDiff ((gammaIdx d + 2 : ℕ) : ℝ)
      (empirical ((R N).X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t)))
    (fun N hN => (mpt_fluc_measurable hstandM hN (gammaIdx d : ℝ) hγ0 t).aemeasurable)
    (fun N hN ω => by
      have hMFN := hstand9.mean_field.solution N hN
      have : IsProbabilityMeasure (withDensityReal (S.ρ N t)) :=
        isProb_withDensityReal (hMFN.density t htS)
      have : IsFiniteMeasure (empirical ((R N).X (Real.toNNReal t) ω)) := inferInstance
      exact (mpt_embed_smul_ofMeasureDiff hlt.le hγ0' hγ2 (S.sigma N) _ _).symm)
    B (fun N hN => hB N hN)
