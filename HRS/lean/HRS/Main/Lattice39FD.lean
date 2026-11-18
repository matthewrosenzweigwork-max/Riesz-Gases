import HRS.Main.Lattice39Main
import HRS.Main.Lattice39FA2
import HRS.Main.Lattice39FB2
import HRS.Main.Lattice39FCGlue
import HRS.Main.Lattice39FCEnergy

/-!
# Example A.39, final form: assembly (packet `l39d`)

`perturbedLattice_linearization_final_proof`: derive the lattice packages (D1-D3, glue) and apply the interim
theorem `perturbedLattice_linearization_proof` with `Cin' = max Cin (...)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

/-- the lattice rate `κ⁻¹ + κ N^{-2/d}` tends to zero along `N = n^d`. -/
theorem lat39fd_rate_tendsto (hd : 1 ≤ d) (κ : ℕ → ℝ) (hκpos : ∀ N, 0 < κ N)
    (hκ1 : Tendsto (fun n : ℕ => κ (n ^ d)) atTop atTop)
    (hκ2 : Tendsto (fun n : ℕ => κ (n ^ d) / (n : ℝ)) atTop (𝓝 0)) :
    Tendsto (fun n : ℕ => (κ (n ^ d))⁻¹ +
      κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) atTop (𝓝 0) := by
  have hd0 : (d : ℝ) ≠ 0 := by exact_mod_cast (show d ≠ 0 by omega)
  have h1 : Tendsto (fun n : ℕ => (κ (n ^ d))⁻¹) atTop (𝓝 0) :=
    tendsto_inv_atTop_zero.comp hκ1
  have h2 : Tendsto (fun n : ℕ => κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)))
      atTop (𝓝 0) := by
    refine squeeze_zero' ?_ ?_ hκ2
    · exact Eventually.of_forall fun n => by have := hκpos (n ^ d); positivity
    · filter_upwards [eventually_ge_atTop 1] with n hn
      have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn
      have hpow : ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) = (n : ℝ) ^ (-(2 : ℝ)) := by
        rw [Nat.cast_pow, ← Real.rpow_natCast, ← Real.rpow_mul (by positivity)]
        congr 1
        field_simp
      have hle : (n : ℝ) ^ (-(2 : ℝ)) ≤ (n : ℝ)⁻¹ := by
        rw [← Real.rpow_neg_one]
        exact Real.rpow_le_rpow_of_exponent_le hnr (by norm_num)
      rw [hpow, div_eq_mul_inv]
      exact mul_le_mul_of_nonneg_left hle (hκpos _).le
  simpa using h1.add h2

/-- A sequence supported on the lattice set tends to `0` if it does along `N = n^d`. -/
theorem lat39fd_tendsto_indicator (hd : 1 ≤ d) (n₁ : ℕ) (g u : ℕ → ℝ)
    (hu : Tendsto u atTop (𝓝 0)) (hg : ∀ᶠ n : ℕ in atTop, g (n ^ d) = u n) :
    Tendsto (Set.indicator (lattice39fSet d n₁) g) atTop (𝓝 0) := by
  have hd0 : d ≠ 0 := by omega
  rw [Metric.tendsto_atTop]
  intro ε hε
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 ((hu.eventually (Metric.ball_mem_nhds 0 hε)).and hg)
  refine ⟨n0 ^ d, fun N hN => ?_⟩
  by_cases hmem : N ∈ lattice39fSet d n₁
  · obtain ⟨n, hn, rfl⟩ := hmem
    have hn0n : n0 ≤ n := (Nat.pow_le_pow_iff_left hd0).1 hN
    obtain ⟨h1, h2⟩ := hn0 n hn0n
    rw [Set.indicator_of_mem (show n ^ d ∈ lattice39fSet d n₁ from ⟨n, hn, rfl⟩), h2]
    simpa [Metric.mem_ball] using h1
  · rw [Set.indicator_of_notMem hmem]
    simpa using hε

theorem perturbedLattice_linearization_final_proof (s : ℝ) (hd2 : 1 ≤ d) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (a : Torus d → Euc d), Torus.IsSmooth a →
    ∃ ΛT : ℝ, 0 < ΛT ∧
    ∀ (S : MainData d), S.s = s → S.T = T → S.μ0 = volume → (∀ N : ℕ, S.invβ N = 0) →
    (∀ (N M : ℕ) (t : ℝ), S.ρ N t = S.ρ M t) →
    ∀ (R : ∀ N, Realization d N) (𝔈 εf : ℕ → ℝ) (Λ' : ℝ) (n₁ : ℕ),
    -- A.1-A.3 (the fields of `TorusStanding` other than `energy`), all `N ≥ 1`
    SelectedFlows S R →
    (∀ N : ℕ, 1 ≤ N → ∃ (ℱ : MeasureTheory.Filtration ℝ (R N).mΩ)
      (W' : ℝ≥0 → (R N).Ω → (Fin N × Fin d) → ℝ),
      IsFilteredSolution (R N).P ℱ W' (R N).W (R N).X) →
    S.RegimeHolds Rg ν₀ → MeanFieldRegularity S (gammaIdx d + 3) Λ →
    PDE.MatBound MB S.M → PDE.VHyp (gammaIdx d) VB S.V →
    -- tacit TeX hypotheses (zero-temperature reduction, Proposition 3.36 (C1)) and the completion pair
    Torus.SymNonpos S.M →
    (∀ N : ℕ, 1 ≤ N → ∀ t ∈ Set.Icc (0 : ℝ) T,
      HasTransportBound d s (meanFieldDrift (S.dyn N) (S.ρ N t)) Λ') →
    IsCoercivityPair d s C₀ Cc →
    -- the data: `η° = -div a`, deterministic, for every `N`; `1 ≤ Cin`
    1 ≤ Cin →
    (∀ (N : ℕ) (ω : (R N).Ω) (ψ : Torus d → ℝ), (R N).η ω ψ = ∫ x, ψ x * (-Torus.div a x)) →
    -- the lattice and the scales (as in the interim form)
    (∀ n : ℕ, max 2 n₁ ≤ n → ∀ᵐ ω ∂(R (n ^ d)).P,
      (R (n ^ d)).X₀ ω = perturbedLattice n (S.κ (n ^ d)) a) →
    Tendsto (fun n : ℕ => S.κ (n ^ d)) atTop atTop →
    Tendsto (fun n : ℕ => S.κ (n ^ d) / (n : ℝ)) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)) atTop (𝓝 0) →
    -- A.4 (`I2`, `m₀ = m_*`), assumed only off the lattice
    (∀ N : ℕ, 1 ≤ N → N ∉ lattice39fSet d n₁ → ∀ ψ : Torus d → ℝ,
      MemSobolev ((PDE.mStar d : ℕ) : ℝ) ψ → Continuous ψ →
      ∫⁻ ω, ENNReal.ofReal ((S.κ N * (pair (empirical ((R N).X₀ ω)) ψ - pair S.μ0 ψ)) ^ 2)
          ∂(R N).P +
        ∫⁻ ω, ENNReal.ofReal (((R N).η ω ψ) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal (Cin ^ 2 * sobolevNorm ((PDE.mStar d : ℕ) : ℝ) ψ ^ 2)) →
    -- A.5 (field moments), assumed only off the lattice
    (∀ N : ℕ, 1 ≤ N → N ∉ lattice39fSet d n₁ → 0 ≤ εf N ∧
      ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0 -
          lattice39fEta a‖ₑ ∂(R N).P ≤ ENNReal.ofReal (εf N) ∧
      ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0‖ₑ ^ 2
          ∂(R N).P +
        ∫⁻ _ω, ‖lattice39fEta a‖ₑ ^ 2 ∂(R N).P ≤ ENNReal.ofReal (Cin ^ 2)) →
    -- A.6 (`pos`, `bound`, `small`), assumed only off the lattice
    (∀ N : ℕ, 1 ≤ N → N ∉ lattice39fSet d n₁ → 0 < 𝔈 N ∧
      ∀ t ∈ Set.Icc (0 : ℝ) S.T,
        ∫⁻ ω, ENNReal.ofReal
            (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ∂(R N).P ≤
          ENNReal.ofReal (𝔈 N)) →
    Tendsto (Set.indicator (lattice39fSet d n₁)ᶜ (fun N : ℕ => S.sigma N * 𝔈 N)) atTop (𝓝 0) →
    (∃ (K' : ℝ) (n₀ : ℕ), ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ, n₀ ≤ n →
      smoothDist 2
        (particleFieldLaw (R (n ^ d)).P (S.sigma (n ^ d)) (gammaIdx d : ℝ) (R (n ^ d)).X
          (S.ρ (n ^ d)) t)
        (Measure.dirac (transportField (S.dyn (n ^ d)) (S.ρ (n ^ d)) t (gammaIdx d : ℝ)
          (NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x)))) ≤
      K' * Real.exp (ΛT * t) *
        ((S.κ (n ^ d))⁻¹ + S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) +
          S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1))) ∧
    (∀ t ∈ Set.Icc (0 : ℝ) T,
      ConvergesInLaw
        (fun n : ℕ => particleFieldLaw (R (n ^ d)).P (S.sigma (n ^ d)) (gammaIdx d : ℝ)
          (R (n ^ d)).X (S.ρ (n ^ d)) t)
        (Measure.dirac (transportField (S.dyn 1) (S.ρ 1) t (gammaIdx d : ℝ)
          (NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x))))) := by
  have hd1 : 1 ≤ d := by omega
  have hd0 : d ≠ 0 := by omega
  obtain ⟨C₁, hI⟩ := perturbedLattice_linearization_proof (d := d) s
  obtain ⟨C₂, hEn⟩ := lattice39f_energy_proof hd2 s
  refine ⟨max C₁ C₂, fun Rg ν₀ MB Λ T VB Cin C₀ Cc hC₀ a ha => ?_⟩
  refine ⟨1, one_pos, fun S hs hT hμ0 hinv hρ R 𝔈 εf Λ' n₁ hflow hfilt hreg hMF hMB hVH hSym hΛ'
    hCoer hCin hη hlat hκ1 hκ2 hκ3 hI2off hfieldoff henergyoff hsmoff => ?_⟩
  subst hs hT
  obtain ⟨κ₀, Ke, hκ₀, hKe, hE⟩ := hEn C₀ (le_trans (le_max_right _ _) hC₀) Λ S.T VB Λ' a ha
  obtain ⟨Cf, hCf0, hCf⟩ := lattice39f_field_moments_proof hd1 a ha
  obtain ⟨Ca, hCa0, hCa⟩ := lattice39f_I2_proof hd1 a ha
  have hn1 : ∀ n : ℕ, max 2 n₁ ≤ n → 1 ≤ n := fun n hn => by
    have := le_max_left 2 n₁; omega
  have hn2 : ∀ n : ℕ, max 2 n₁ ≤ n → 2 ≤ n := fun n hn => by
    have := le_max_left 2 n₁; omega
  have hN1 : ∀ n : ℕ, 1 ≤ n → 1 ≤ n ^ d := fun n hn => Nat.one_le_pow _ _ hn
  -- the lattice rate and its bound
  have hrate := lat39fd_rate_tendsto hd1 S.κ S.hκ hκ1 hκ2
  obtain ⟨Rb, hRb⟩ := hrate.bddAbove_range
  have hrb : ∀ n : ℕ, (S.κ (n ^ d))⁻¹ + S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) ≤ Rb :=
    fun n => hRb ⟨n, rfl⟩
  have hrnn : ∀ n : ℕ, 0 ≤ (S.κ (n ^ d))⁻¹ +
      S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) := fun n => by
    have := S.hκ (n ^ d); positivity
  have hRb0 : 0 ≤ Rb := (hrnn 0).trans (hrb 0)
  have hη0 : 0 ≤ ‖lattice39fEta a‖ := norm_nonneg _
  set Cin' : ℝ := max Cin (max (Ca * (1 + Rb)) (2 * ‖lattice39fEta a‖ + Cf * Rb)) with hCin'
  have hCinle : Cin ≤ Cin' := le_max_left _ _
  have hCin1 : 1 ≤ Cin' := le_trans hCin hCinle
  have hCa' : Ca * (1 + Rb) ≤ Cin' := le_trans (le_max_left _ _) (le_max_right _ _)
  have hηC : 2 * ‖lattice39fEta a‖ + Cf * Rb ≤ Cin' := le_trans (le_max_right _ _) (le_max_right _ _)
  -- A.4 at every N
  have hI2all : ∀ N : ℕ, 1 ≤ N → ∀ ψ : Torus d → ℝ, MemSobolev ((PDE.mStar d : ℕ) : ℝ) ψ →
      Continuous ψ →
      ∫⁻ ω, ENNReal.ofReal ((S.κ N * (pair (empirical ((R N).X₀ ω)) ψ - pair S.μ0 ψ)) ^ 2)
          ∂(R N).P +
        ∫⁻ ω, ENNReal.ofReal (((R N).η ω ψ) ^ 2) ∂(R N).P ≤
      ENNReal.ofReal (Cin' ^ 2 * sobolevNorm ((PDE.mStar d : ℕ) : ℝ) ψ ^ 2) := by
    intro N hN ψ hψ hψc
    by_cases hmem : N ∈ lattice39fSet d n₁
    · obtain ⟨n, hn, rfl⟩ := hmem
      have hle : Ca * (1 + (S.κ (n ^ d))⁻¹ + S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)))
          ≤ Cin' := by
        refine le_trans ?_ hCa'
        have := hrb n
        have e : 1 + (S.κ (n ^ d))⁻¹ + S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) =
            1 + ((S.κ (n ^ d))⁻¹ + S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) := by ring
        rw [e]
        exact mul_le_mul_of_nonneg_left (by linarith) hCa0
      have := hCa n (hn1 n hn) (S.κ (n ^ d)) (S.hκ _) Cin' hle (R (n ^ d)).Ω (R (n ^ d)).P
        (R (n ^ d)).X₀ (R (n ^ d)).η (hlat n hn) (fun ω ψ => hη (n ^ d) ω ψ) ψ hψ hψc
      rwa [hμ0]
    · refine (hI2off N hN hmem ψ hψ hψc).trans (ENNReal.ofReal_le_ofReal ?_)
      have h0 : 0 ≤ sobolevNorm ((PDE.mStar d : ℕ) : ℝ) ψ ^ 2 := sq_nonneg _
      have hc : Cin ^ 2 ≤ Cin' ^ 2 :=
        pow_le_pow_left₀ (by linarith) hCinle 2
      exact mul_le_mul_of_nonneg_right hc h0
  have hIF := lattice39f_initialFluctuation_of_I2_proof S R a ha Cin' hCin1 hη hflow hI2all
  -- A.5 at every N
  obtain ⟨εf', hεf'lat, hεf'off⟩ : ∃ εf' : ℕ → ℝ,
      (∀ N ∈ lattice39fSet d n₁, εf' N =
        Cf * ((S.κ N)⁻¹ + S.κ N * (N : ℝ) ^ (-(2 : ℝ) / (d : ℝ)))) ∧
      (∀ N ∉ lattice39fSet d n₁, εf' N = εf N) := by
    classical
    exact ⟨fun N => if N ∈ lattice39fSet d n₁ then
      Cf * ((S.κ N)⁻¹ + S.κ N * (N : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) else εf N,
      fun N hN => if_pos hN, fun N hN => if_neg hN⟩
  have hεf'nn : ∀ N : ℕ, 1 ≤ N → 0 ≤ εf' N := by
    intro N hN
    by_cases hmem : N ∈ lattice39fSet d n₁
    · obtain ⟨n, hn, rfl⟩ := hmem
      rw [hεf'lat _ ⟨n, hn, rfl⟩]
      exact mul_nonneg hCf0 (hrnn n)
    · rw [hεf'off N hmem]; exact (hfieldoff N hN hmem).1
  have hF1 : ∀ N : ℕ, 1 ≤ N →
      ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0 -
          lattice39fEta a‖ₑ ∂(R N).P ≤ ENNReal.ofReal (εf' N) := by
    intro N hN
    by_cases hmem : N ∈ lattice39fSet d n₁
    · obtain ⟨n, hn, rfl⟩ := hmem
      rw [hεf'lat _ ⟨n, hn, rfl⟩, hμ0]
      exact (hCf n (hn1 n hn) (S.κ (n ^ d)) (S.hκ _) (R (n ^ d)).Ω (R (n ^ d)).P
        (R (n ^ d)).X₀ (hlat n hn)).1
    · rw [hεf'off N hmem]; exact (hfieldoff N hN hmem).2.1
  have hF2 : ∀ N : ℕ, 1 ≤ N →
      ∫⁻ ω, ‖S.κ N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ) (empirical ((R N).X₀ ω)) S.μ0‖ₑ ^ 2
          ∂(R N).P +
        ∫⁻ _ω, ‖lattice39fEta a‖ₑ ^ 2 ∂(R N).P ≤ ENNReal.ofReal (Cin' ^ 2) := by
    intro N hN
    by_cases hmem : N ∈ lattice39fSet d n₁
    · obtain ⟨n, hn, rfl⟩ := hmem
      rw [hμ0]
      refine (hCf n (hn1 n hn) (S.κ (n ^ d)) (S.hκ _) (R (n ^ d)).Ω (R (n ^ d)).P
        (R (n ^ d)).X₀ (hlat n hn)).2.trans (ENNReal.ofReal_le_ofReal ?_)
      have hx : ‖lattice39fEta a‖ + Cf * ((S.κ (n ^ d))⁻¹ +
          S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) ≤
          ‖lattice39fEta a‖ + Cf * Rb :=
        by have := mul_le_mul_of_nonneg_left (hrb n) hCf0; linarith
      have hx0 : 0 ≤ ‖lattice39fEta a‖ + Cf * ((S.κ (n ^ d))⁻¹ +
          S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) :=
        add_nonneg hη0 (mul_nonneg hCf0 (hrnn n))
      set x := ‖lattice39fEta a‖ + Cf * ((S.κ (n ^ d))⁻¹ +
          S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) with hxdef
      have h3 : x ^ 2 + ‖lattice39fEta a‖ ^ 2 ≤ (x + ‖lattice39fEta a‖) ^ 2 := by
        nlinarith [mul_nonneg hx0 hη0]
      refine h3.trans ?_
      exact pow_le_pow_left₀ (add_nonneg hx0 hη0) (by linarith) 2
    · have := (hfieldoff N hN hmem).2.2
      refine this.trans (ENNReal.ofReal_le_ofReal ?_)
      exact pow_le_pow_left₀ (by linarith) hCinle 2
  have hField := lattice39f_initialFluctuationField_of_moments_proof S R a ha Cin' εf' hη hεf'nn
    hF1 hF2
  -- energy: the lattice part
  obtain ⟨Ke', hKe'⟩ : ∃ Ke' : ℝ, Ke' = max Ke 1 := ⟨_, rfl⟩
  have hKe'pos : 0 < Ke' := by rw [hKe']; exact lt_of_lt_of_le one_pos (le_max_right _ _)
  have hKeKe' : Ke ≤ Ke' := by rw [hKe']; exact le_max_left _ _
  have hB : ∀ N : ℕ, ∃ B : ℝ, N ∈ lattice39fSet d n₁ → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ω, ENNReal.ofReal
          (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ∂(R N).P ≤
        ENNReal.ofReal B := by
    intro N
    by_cases hN : N ∈ lattice39fSet d n₁
    · obtain ⟨n, hn, rfl⟩ := hN
      obtain ⟨B, hB⟩ := (hE S rfl rfl hμ0 hinv hSym hΛ' hMF hVH R hflow n (hn2 n hn) (hlat n hn)).2
      exact ⟨B, fun _ => hB⟩
    · exact ⟨0, fun h => absurd h hN⟩
  choose Bf hBf using hB
  obtain ⟨𝔈L, h𝔈L⟩ : ∃ 𝔈L : ℕ → ℝ, ∀ N : ℕ, 𝔈L N =
      Ke' * (((S.κ N)⁻¹) ^ 2 + (N : ℝ) ^ (S.s / (d : ℝ) - 1)) +
        (if S.κ N < κ₀ then |Bf N| else 0) := by
    classical
    exact ⟨fun N => Ke' * (((S.κ N)⁻¹) ^ 2 + (N : ℝ) ^ (S.s / (d : ℝ) - 1)) +
        (if S.κ N < κ₀ then |Bf N| else 0), fun N => rfl⟩
  have hbrpos : ∀ N : ℕ, 0 < ((S.κ N)⁻¹) ^ 2 + (N : ℝ) ^ (S.s / (d : ℝ) - 1) := fun N => by
    have := S.hκ N; positivity
  have hextra : ∀ N : ℕ, 0 ≤ (if S.κ N < κ₀ then |Bf N| else 0) := fun N => by
    split_ifs
    · exact abs_nonneg _
    · exact le_rfl
  have hposL : ∀ N : ℕ, 1 ≤ N → N ∈ lattice39fSet d n₁ → 0 < 𝔈L N := by
    intro N _ _
    rw [h𝔈L N]
    exact add_pos_of_pos_of_nonneg (mul_pos hKe'pos (hbrpos N)) (hextra N)
  have hbdL : ∀ N : ℕ, 1 ≤ N → N ∈ lattice39fSet d n₁ → ∀ t ∈ Set.Icc (0 : ℝ) S.T,
      ∫⁻ ω, ENNReal.ofReal
          (correctedEnergy (S.dyn N) C₀ Λ (S.ρ N) ((R N).X (Real.toNNReal t) ω) t) ∂(R N).P ≤
        ENNReal.ofReal (𝔈L N) := by
    intro N _ hmem t ht
    have hmem' := hmem
    obtain ⟨n, hn, rfl⟩ := hmem
    by_cases hκ : κ₀ ≤ S.κ (n ^ d)
    · refine ((hE S rfl rfl hμ0 hinv hSym hΛ' hMF hVH R hflow n (hn2 n hn) (hlat n hn)).1 hκ t
        ht).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [h𝔈L]
      have := mul_le_mul_of_nonneg_right hKeKe' (hbrpos (n ^ d)).le
      linarith [hextra (n ^ d)]
    · refine (hBf (n ^ d) hmem' t ht).trans (ENNReal.ofReal_le_ofReal ?_)
      rw [h𝔈L, if_pos (not_le.1 hκ)]
      have := mul_pos hKe'pos (hbrpos (n ^ d))
      linarith [le_abs_self (Bf (n ^ d))]
  have hsmL : Tendsto (Set.indicator (lattice39fSet d n₁)
      (fun N : ℕ => S.sigma N * 𝔈L N)) atTop (𝓝 0) := by
    refine lat39fd_tendsto_indicator hd1 n₁ _
      (fun n => Ke' * ((S.κ (n ^ d))⁻¹ +
        S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (S.s / (d : ℝ) - 1))) ?_ ?_
    · have h1 : Tendsto (fun n : ℕ => (S.κ (n ^ d))⁻¹) atTop (𝓝 0) :=
        tendsto_inv_atTop_zero.comp hκ1
      simpa using (h1.add hκ3).const_mul Ke'
    · filter_upwards [hκ1.eventually_ge_atTop κ₀] with n hn
      obtain ⟨hσ, -, -⟩ := lattice39_scales_of_invβ_zero_proof S (n ^ d) (hinv _)
      have hκp := S.hκ (n ^ d)
      rw [hσ, h𝔈L, if_neg (not_lt.2 hn), add_zero]
      field_simp
  have hC' : IsCoercivityPair d S.s C₀ Cc := hCoer
  have hglue := lattice39f_energySmallness_glue_proof S R C₀ Cc Λ (lattice39fSet d n₁) 𝔈 𝔈L hC'
    (fun N hN hmem => (henergyoff N hN hmem).1) (fun N hN hmem => (henergyoff N hN hmem).2)
    hsmoff hposL hbdL hsmL
  obtain ⟨𝔈', h𝔈'⟩ : ∃ 𝔈' : ℕ → ℝ, EnergySmallness S R C₀ Cc Λ 𝔈' ∧
      ∀ N ∈ lattice39fSet d n₁, 𝔈' N = 𝔈L N := by
    classical
    exact ⟨_, hglue, fun N hN => if_pos hN⟩
  obtain ⟨hES, h𝔈'lat⟩ := h𝔈'
  have hstand : TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈' :=
    ⟨hflow, hreg, hMF, hMB, hVH, hES, hfilt⟩
  -- the domination
  obtain ⟨n0, hn0⟩ := eventually_atTop.1 (hκ1.eventually_ge_atTop κ₀)
  have hdom : ∃ K : ℝ, ∀ n : ℕ, max 2 n₁ ≤ n →
      εf' (n ^ d) ≤ K * ((S.κ (n ^ d))⁻¹ +
        S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) ∧
      𝔈' (n ^ d) ≤ K * (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (S.s / (d : ℝ) - 1)) := by
    refine ⟨Cf + Ke' + ∑ n ∈ Finset.range n0, |Bf (n ^ d)| /
      (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (S.s / (d : ℝ) - 1)), fun n hn => ?_⟩
    have hsum : 0 ≤ ∑ n ∈ Finset.range n0, |Bf (n ^ d)| /
        (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (S.s / (d : ℝ) - 1)) :=
      Finset.sum_nonneg fun i _ => div_nonneg (abs_nonneg _) (hbrpos _).le
    have hmem : n ^ d ∈ lattice39fSet d n₁ := ⟨n, hn, rfl⟩
    refine ⟨?_, ?_⟩
    · rw [hεf'lat _ hmem]
      exact mul_le_mul_of_nonneg_right (by linarith) (hrnn n)
    · rw [h𝔈'lat _ hmem, h𝔈L]
      have hbr := hbrpos (n ^ d)
      have hex : (if S.κ (n ^ d) < κ₀ then |Bf (n ^ d)| else 0) ≤
          (∑ n ∈ Finset.range n0, |Bf (n ^ d)| /
            (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (S.s / (d : ℝ) - 1))) *
          (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (S.s / (d : ℝ) - 1)) := by
        by_cases hlt : S.κ (n ^ d) < κ₀
        · rw [if_pos hlt]
          have hnn : n < n0 := by
            by_contra hh
            exact absurd (hn0 n (not_lt.1 hh)) (not_le.2 hlt)
          have hle := Finset.single_le_sum (f := fun n : ℕ => |Bf (n ^ d)| /
            (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (S.s / (d : ℝ) - 1)))
            (fun i _ => div_nonneg (abs_nonneg _) (hbrpos _).le) (Finset.mem_range.2 hnn)
          have := mul_le_mul_of_nonneg_right hle hbr.le
          calc |Bf (n ^ d)| = |Bf (n ^ d)| / (((S.κ (n ^ d))⁻¹) ^ 2 +
                ((n ^ d : ℕ) : ℝ) ^ (S.s / (d : ℝ) - 1)) * (((S.κ (n ^ d))⁻¹) ^ 2 +
                ((n ^ d : ℕ) : ℝ) ^ (S.s / (d : ℝ) - 1)) := (div_mul_cancel₀ _ hbr.ne').symm
            _ ≤ _ := this
        · rw [if_neg hlt]; exact mul_nonneg hsum hbr.le
      nlinarith [hex, hbr, hKe'pos]
  -- the interim theorem
  obtain ⟨ΛT', hΛT', H⟩ := hI Rg ν₀ MB Λ S.T VB Cin' C₀ Cc (le_trans (le_max_left _ _) hC₀) a ha
  obtain ⟨⟨K', n₀, hK'⟩, hconv⟩ := H S rfl rfl hμ0 hinv hρ R 𝔈' (PDE.mStar d) (fun _ => 0) εf'
    (fun _ _ => lattice39fEta a) (Measure.dirac (lattice39fEta a)) n₁ hstand hIF (fun N ω => rfl)
    hField hlat hκ1 hκ2 hκ3 hdom
  refine ⟨⟨max K' 0 * Real.exp (ΛT' * max S.T 0), n₀, fun t ht n hn => ?_⟩, hconv⟩
  refine (hK' t ht n hn).trans ?_
  have hκp := S.hκ (n ^ d)
  have hrt : 0 ≤ (S.κ (n ^ d))⁻¹ + S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) +
      S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (S.s / (d : ℝ) - 1) := by positivity
  have h1 : Real.exp (ΛT' * t) ≤ Real.exp (ΛT' * max S.T 0) :=
    Real.exp_le_exp.2 (mul_le_mul_of_nonneg_left (ht.2.trans (le_max_left _ _)) hΛT'.le)
  have h2 : (1 : ℝ) ≤ Real.exp (1 * t) := Real.one_le_exp (by linarith [ht.1])
  have h3 : K' * Real.exp (ΛT' * t) ≤ max K' 0 * Real.exp (ΛT' * max S.T 0) * Real.exp (1 * t) := by
    have e0 : K' * Real.exp (ΛT' * t) ≤ max K' 0 * Real.exp (ΛT' * max S.T 0) :=
      mul_le_mul (le_max_left _ _) h1 (Real.exp_pos _).le (le_max_right _ _)
    have e1 : 0 ≤ max K' 0 * Real.exp (ΛT' * max S.T 0) :=
      mul_nonneg (le_max_right _ _) (Real.exp_pos _).le
    nlinarith
  exact mul_le_mul_of_nonneg_right h3 hrt

example := (@perturbedLattice_linearization_final_proof : type_of% @perturbedLattice_linearization_final)

end Main

end HRS
