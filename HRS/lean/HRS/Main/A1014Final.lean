import HRS.Main.TorusTheorems
import HRS.Main.A8Final
import HRS.Main.A9Final
import HRS.Main.A1014Aux11

/-!
# Packet A1014: relocated proofs of Corollary A.14 (`true_limit_stat`, `true_limit_stat_base`,
`true_limit_field`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

theorem torus_field_wasserstein_proof (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ),
        TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈 →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuation S R m₀ Cin ε (fun _ => ∅) →
        ∀ (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ))
          (νin : Measure (NegSobolev d (gammaIdx d : ℝ))),
          InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, C ≤ (N : ℝ) →
        ∀ νG : Measure (NegSobolev d (gammaIdx d : ℝ)),
          IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG →
          wassersteinE 1
            (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
            (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) ≤
          ENNReal.ofReal (C * Real.exp (ΛT * t) *
            masterRate d (εf N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N) ∧
          (∀ (𝔈' ε2 εf2 : ℕ → ℝ),
            EnergySmallness2 S R C₀ Λ m₀ (fun _ => ∅) 𝔈' ε2 →
            (∀ N' : ℕ, 1 ≤ N' → 0 ≤ εf2 N') →
            (∀ N' : ℕ, 1 ≤ N' →
              ∫⁻ ω, ‖S.κ N' • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
                  (empirical ((R N').X₀ ω)) S.μ0 - ηF N' ω‖ₑ ^ 2 ∂(R N').P ≤
                ENNReal.ofReal ((εf2 N') ^ 2)) →
            wassersteinE 2
              (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
              (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) ≤
            ENNReal.ofReal (C * Real.exp (ΛT * t) *
              masterRate d (εf2 N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈' N) N)) := by
  by_cases hok : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  swap
  · refine ⟨0, fun Rg ν₀ MB Λ T VB Cin C₀ Cc _ => ⟨1, 1, one_pos, one_pos, fun S hs => ?_⟩⟩
    exact absurd ⟨S.hd, hs ▸ S.hs0, hs ▸ S.hsd⟩ hok
  obtain ⟨hd, hs0, hsd⟩ := hok
  obtain ⟨C₀', Cq, hC₀', hCq, hcom⟩ := HRS.Main.A8P.a8p_commSpec hd hs0 hsd
  refine ⟨C₀', fun Rg ν₀ MB Λ T VB Cin C₀ Cc hC => ?_⟩
  obtain ⟨Ca, Λ₁, hCa, hspec⟩ := HRS.Main.A8P.a8p_adjSpec hd s hs0 hsd Rg MB Λ VB ν₀
  obtain ⟨Cp, hCp0, hCp⟩ := HRS.Main.A8P.a8p_hom_prod hd hs0 hsd
  obtain ⟨cT, hcT0, hcT⟩ := HRS.Main.A8P.a8p_transport_bound hd MB s hs0
  obtain ⟨Ktr, hKtr0, hKtr'⟩ := HRS.A34.a34_transport_unif hd s hs0 hsd Rg MB Λ VB ν₀ T
  obtain ⟨Z0, hZ0⟩ : ∃ x : ℝ, x = ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-((d : ℝ) + 3)) :=
    ⟨_, rfl⟩
  have hZ00 : 0 ≤ Z0 := by
    rw [hZ0]; exact tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
  obtain ⟨Kb, hKb⟩ : ∃ x : ℝ, x = Real.exp (|Λ₁| * T) * Z0 := ⟨_, rfl⟩
  have hKb0 : 0 ≤ Kb := by rw [hKb]; exact mul_nonneg (Real.exp_pos _).le hZ00
  obtain ⟨c1, hc1⟩ : ∃ x : ℝ, x = (1 / 2) * Cq * cT * |T| * Kb := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ x : ℝ, x = 2 * (|T| * Cq * Kb ^ 2 * (2 * d * Ca ^ 2 + Cp)) := ⟨_, rfl⟩
  obtain ⟨c3, hc3⟩ : ∃ x : ℝ, x = 2 * Real.sqrt (2 * |T|) * (d * Ca) := ⟨_, rfl⟩
  have hc10 : 0 ≤ c1 := by rw [hc1]; positivity
  have hc20 : 0 ≤ c2 := by
    rw [hc2]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    positivity
  have hc30 : 0 ≤ c3 := by
    rw [hc3]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    positivity
  refine ⟨2 + Ktr + c1 + Real.sqrt c2, 1, by positivity, one_pos, ?_⟩
  intro S hSs hST R 𝔈 hS m₀ ε hinit εf ηF νin hfield t ht N hN νG hνG
  subst hSs hST
  have hT0 : 0 < S.T := S.hT
  have hTabs : |S.T| = S.T := abs_of_pos hT0
  have hP : HRS.Main.A8P.A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT :=
    ⟨hCa.le, hspec, hcom, hCq.le, hC, hCp0, hCp, hcT0, hcT⟩
  have hN2 : 2 ≤ N := by
    have h2 : (2 : ℝ) ≤ N := le_trans (by
      have := Real.sqrt_nonneg c2
      linarith) hN
    exact_mod_cast h2
  have hN1 : 1 ≤ N := by omega
  have h𝔈 := (hS.energy.pos N hN1).le
  have hσ := HRS.Main.A8P.a8p_sigma_nonneg S N
  obtain ⟨hq0, hq1⟩ := HRS.Main.A8P.a8p_q_bounds S hN1
  have hKtot : ∑' j, HRS.Main.A9.a9K d Λ₁ t j ≤ Kb := by
    rw [hKb, hZ0]; exact HRS.Main.A9.a9K_tsum_le Λ₁ ht
  have hexp : 1 ≤ Real.exp (1 * t) := by rw [one_mul]; exact Real.one_le_exp ht.1
  have hc1e : c1 = (1 / 2) * Cq * cT * S.T * Kb := by rw [hc1, hTabs]
  have hc2e : c2 = 2 * (S.T * Cq * Kb ^ 2 * (2 * d * Ca ^ 2 + Cp)) := by rw [hc2, hTabs]
  have hc3e : c3 = 2 * Real.sqrt (2 * S.T) * (d * Ca) := by rw [hc3, hTabs]
  have hfinal : ∀ (εp E' : ℝ), 0 ≤ εp → 0 ≤ E' →
      Ktr * εp + c1 * (S.sigma N * E') +
        Real.sqrt (c2 * (S.qN N * (Real.sqrt (𝔈 N) + (N : ℝ) ^ (-(1 : ℝ) / d)))) ≤
      (2 + Ktr + c1 + Real.sqrt c2) * Real.exp (1 * t) *
        masterRate d εp (S.qN N) (S.sigma N) (𝔈 N) E' N := by
    intro εp E' hεp hE'
    have h0 := HRS.Main.A1014.a1014_rate_final (d := d) (N := N) hd hN1 hKtr0 hc10 hc20 hεp hq0 hσ
      h𝔈 hE'
    have hmr := HRS.Main.A8P.a8p_masterRate_nonneg (d := d) (N := N) hεp hq0 hσ h𝔈 hE'
    have h3 : Ktr + c1 + Real.sqrt c2 ≤ (2 + Ktr + c1 + Real.sqrt c2) * Real.exp (1 * t) := by
      have : 0 ≤ 2 + Ktr + c1 + Real.sqrt c2 := by positivity
      have h4 := mul_le_mul_of_nonneg_left hexp this
      linarith
    have := mul_le_mul_of_nonneg_right h3 hmr
    linarith
  -- the generic infimum over the tails
  have hmain : ∀ {p : ℝ} (εp E' : ℝ), 0 ≤ εp → 0 ≤ E' →
      (∀ (q : ℕ) (k : Fin q → NonzeroLattice d), Function.Injective k →
        wassersteinE p
          (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
          (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) ≤
        ENNReal.ofReal (Ktr * εp + (c1 * (S.sigma N * E') +
          Real.sqrt (c2 * (S.qN N * (Real.sqrt (𝔈 N) + (N : ℝ) ^ (-(1 : ℝ) / d)))) +
          c3 * HRS.Main.A9.a9tail d Λ₁ t k))) →
      wassersteinE p
          (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
          (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) ≤
        ENNReal.ofReal ((2 + Ktr + c1 + Real.sqrt c2) * Real.exp (1 * t) *
          masterRate d εp (S.qN N) (S.sigma N) (𝔈 N) E' N) := by
    intro p εp E' hεp hE' hk
    have hB0 : 0 ≤ Ktr * εp + c1 * (S.sigma N * E') +
        Real.sqrt (c2 * (S.qN N * (Real.sqrt (𝔈 N) + (N : ℝ) ^ (-(1 : ℝ) / d)))) := by positivity
    refine le_trans (HRS.Main.A1014.a1014_inf_tail (c3 := c3) hB0 ?_) ?_
    · intro ε' hε'
      obtain ⟨q, k, hkinj, htl⟩ := HRS.Main.A9.a9_exists_finite_tail (d := d) Λ₁ t
        (ε := ε' / (c3 + 1)) (by positivity)
      refine ⟨HRS.Main.A9.a9tail d Λ₁ t k, HRS.Main.A9.a9tail_nonneg Λ₁ t k, ?_, ?_⟩
      · calc c3 * HRS.Main.A9.a9tail d Λ₁ t k ≤ c3 * (ε' / (c3 + 1)) :=
            mul_le_mul_of_nonneg_left htl hc30
          _ ≤ ε' := by
            rw [mul_div_assoc', div_le_iff₀ (by positivity)]
            linarith
      · refine (hk q k hkinj).trans (le_of_eq ?_)
        congr 1
        ring
    · refine ENNReal.ofReal_le_ofReal ?_
      have := hfinal εp E' hεp hE'
      linarith
  have hεf := hfield.εf_nonneg N hN1
  refine ⟨?_, ?_⟩
  · -- W₁
    refine hmain (p := 1) (εf N) (𝔈 N) hεf h𝔈 ?_
    intro q k hk
    have := HRS.Main.A1014.a1014_perk1 hP hKtr0 hKtr' hS hN2 hfield ht hνG hk hKtot
    rw [hc1e, hc2e, hc3e]
    exact this
  · -- W₂
    intro 𝔈' ε2 εf2 hE2 hεf2 hL2
    have h𝔈' := hE2.𝔈'_nonneg N hN1
    refine hmain (p := 2) (εf2 N) (𝔈' N) (hεf2 N hN1) h𝔈' ?_
    intro q k hk
    have := HRS.Main.A1014.a1014_perk2 hP hKtr0 hKtr' hS hN2 hfield h𝔈' (hE2.bound N hN1)
      (hεf2 N hN1) (hL2 N hN1) ht hνG hk hKtot
    rw [hc1e, hc2e, hc3e]
    exact this

example := (@torus_field_wasserstein_proof : type_of% @HRS.Main.torus_field_wasserstein)

theorem true_limit_stat_proof (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ),
        TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 →
        ∀ (L : LimitCoeffs d),
          CoeffConvergence S L Rg ν₀ MB Λ VB (PDE.mStar d + 2) (PDE.mStar d) →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ) (t : ℝ) (φ : Torus d → ℝ), t ∈ Set.Icc (0 : ℝ) T →
          MemSobolev ((PDE.mStar d + 2 : ℕ) : ℝ) φ → Continuous φ →
          InitialFluctuation S R m₀ Cin ε
            (transportedTests S (fun _ : Fin 1 => t) (fun _ => φ)) →
          ∀ N : ℕ, C ≤ (N : ℝ) →
            wassersteinE 1
              (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) (fun _ : Fin 1 => t) (fun _ => φ))
              (surrogateStatLaw (L.dyn S) L.ρ L.A L.invβstar (fun _ : Fin 1 => t) (fun _ => φ)
                (R N).P (R N).η) ≤
            ENNReal.ofReal (C * Real.exp (ΛT * t) *
              (sobolevNorm (PDE.mStar d : ℝ) φ * (1 + sobolevNorm (PDE.mStar d : ℝ) φ) *
                  masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N +
                sobolevNorm ((PDE.mStar d + 2 : ℕ) : ℝ) φ *
                  (S.coeffDiscrepancy L (PDE.mStar d) N +
                    Real.sqrt (S.coeffDiscrepancy L (PDE.mStar d) N)))) := by
  obtain ⟨C₀min, h8⟩ := main_torus_stat_proof (d := d) s
  refine ⟨C₀min, fun Rg ν₀ MB Λ T VB Cin C₀ Cc hC => ?_⟩
  obtain ⟨C8, Λ8, hC8, hΛ8, h8'⟩ := h8 Rg ν₀ MB Λ T VB Cin C₀ Cc hC
  have key : ∀ m₀ : ℕ, m₀ ≤ PDE.mStar d → ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      HRS.Main.A1014.A1014Q34 d s Rg ν₀ MB Λ T VB Cin m₀ C ΛT :=
    fun m₀ hm₀ => HRS.Main.A1014.a1014_Q34_exists s Rg ν₀ MB Λ T VB Cin m₀ hm₀
  choose! f g hf hg hQ using key
  set C34 : ℝ := ∑ m₀ ∈ Finset.range (PDE.mStar d + 1), f m₀ with hC34
  set Λ34 : ℝ := ∑ m₀ ∈ Finset.range (PDE.mStar d + 1), g m₀ with hΛ34
  have hC34pos : 0 < C34 :=
    Finset.sum_pos (fun i hi => hf i (by simp at hi; omega)) ⟨0, by simp⟩
  have hΛ34pos : 0 < Λ34 :=
    Finset.sum_pos (fun i hi => hg i (by simp at hi; omega)) ⟨0, by simp⟩
  refine ⟨C8 + C34, Λ8 + Λ34, by positivity, by positivity, ?_⟩
  intro S hs hT R 𝔈 hS L hcoef m₀ ε t φ ht hφ hφc hinit N hN
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  have hN1 : 1 ≤ N := by omega
  have hN8 : C8 ≤ N := le_trans (by linarith) hN
  have hm₀ : m₀ ≤ PDE.mStar d := hinit.m₀_le
  have hmem8 : MemSobolev (PDE.mStar d : ℝ) φ :=
    HRS.PDE.MFAdjoint.memSobolev_mono_idx hφ (by push_cast; linarith)
  have hA8 := (h8' S hs hT R 𝔈 hS).1 m₀ ε t φ ht hmem8 hφc hinit N hN8
  have hFM := HRS.Main.A1014.a1014_functionalMoment hinit hN1
  have hmr : m₀ ∈ Finset.range (PDE.mStar d + 1) := by simp; omega
  have hfle : f m₀ ≤ C34 :=
    Finset.single_le_sum (f := f) (fun i hi => (hf i (by simp at hi; omega)).le) hmr
  have hgle : g m₀ ≤ Λ34 :=
    Finset.single_le_sum (f := g) (fun i hi => (hg i (by simp at hi; omega)).le) hmr
  have hA34 := HRS.Main.A1014.a1014_Q34_mono (hQ m₀ hm₀) (hf m₀ hm₀) hfle hgle S hs hT L hcoef
    (R N).P (R N).η hFM t ht φ hφ hφc N hN1
  have hηm := hinit.η_meas N
  haveI hSN := HRS.Main.A1014.a1014_surr_prob (S.dyn N) (S.ρ N) (S.AN N) (S.qN N)
    (fun _ : Fin 1 => t) (fun _ => φ) (R N).P (R N).η hηm
  haveI hSI := HRS.Main.A1014.a1014_surr_prob (L.dyn S) L.ρ L.A L.invβstar
    (fun _ : Fin 1 => t) (fun _ => φ) (R N).P (R N).η hηm
  have hfin : wassersteinE 1
      (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) (fun _ : Fin 1 => t) (fun _ => φ))
      (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin 1 => t)
        (fun _ => φ) (R N).P (R N).η) ≠ ⊤ :=
    ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA8
  have hch := HRS.Main.A1014.a1014_w1_chain
    (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) (fun _ : Fin 1 => t) (fun _ => φ))
    (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin 1 => t)
      (fun _ => φ) (R N).P (R N).η)
    (surrogateStatLaw (L.dyn S) L.ρ L.A L.invβstar (fun _ : Fin 1 => t) (fun _ => φ)
      (R N).P (R N).η) hfin
  have hε : 0 ≤ ε N := hinit.eps_anti.le_of_tendsto hinit.eps_tendsto N
  have hr := HRS.Main.A8P.a8p_masterRate_nonneg (d := d) (N := N) hε
    (HRS.Main.A8P.a8p_q_bounds S hN1).1 (HRS.Main.A8P.a8p_sigma_nonneg S N)
    (hS.energy.pos N hN1).le (hS.energy.pos N hN1).le
  have hΔ := HRS.Main.A1014.a1014_delta_nonneg hcoef hN1
  have hX : 0 ≤ sobolevNorm (PDE.mStar d : ℝ) φ := Real.sqrt_nonneg _
  have hY : 0 ≤ sobolevNorm ((PDE.mStar d + 2 : ℕ) : ℝ) φ := Real.sqrt_nonneg _
  have hδ : 0 ≤ S.coeffDiscrepancy L (PDE.mStar d) N +
      Real.sqrt (S.coeffDiscrepancy L (PDE.mStar d) N) := by positivity
  have hsb0 : 0 ≤ statBound C8 Λ8 t (sobolevNorm (PDE.mStar d : ℝ) φ)
      (masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N) := by
    unfold statBound
    positivity
  have h2 : 0 ≤ C34 * Real.exp (Λ34 * t) * sobolevNorm ((PDE.mStar d + 2 : ℕ) : ℝ) φ *
      (S.coeffDiscrepancy L (PDE.mStar d) N + Real.sqrt (S.coeffDiscrepancy L (PDE.mStar d) N)) := by
    positivity
  calc _ ≤ _ := hch
    _ ≤ ENNReal.ofReal (statBound C8 Λ8 t (sobolevNorm (PDE.mStar d : ℝ) φ)
          (masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N)) +
        ENNReal.ofReal (C34 * Real.exp (Λ34 * t) * sobolevNorm ((PDE.mStar d + 2 : ℕ) : ℝ) φ *
          (S.coeffDiscrepancy L (PDE.mStar d) N +
            Real.sqrt (S.coeffDiscrepancy L (PDE.mStar d) N))) := add_le_add hA8 hA34
    _ = ENNReal.ofReal (statBound C8 Λ8 t (sobolevNorm (PDE.mStar d : ℝ) φ)
          (masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N) +
        C34 * Real.exp (Λ34 * t) * sobolevNorm ((PDE.mStar d + 2 : ℕ) : ℝ) φ *
          (S.coeffDiscrepancy L (PDE.mStar d) N +
            Real.sqrt (S.coeffDiscrepancy L (PDE.mStar d) N))) :=
        (ENNReal.ofReal_add hsb0 h2).symm
    _ ≤ _ := ENNReal.ofReal_le_ofReal (HRS.Main.A1014.a1014_arith hC8 hC34pos ht.1 hΛ8 hΛ34pos hX hY
          hr hδ)

example := (@true_limit_stat_proof : type_of% @HRS.Main.true_limit_stat)

theorem true_limit_stat_base_proof (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (S : MainData d) (hs : S.s = s) (hT : S.T = T)
    (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ)
    (hstand : TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈)
    (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (PDE.mStar d + 2) (PDE.mStar d))
    (m₀ : ℕ) (ε : ℕ → ℝ) (t : ℝ) (ht : t ∈ Set.Icc (0 : ℝ) T) (φ : Torus d → ℝ)
    (hφ : MemSobolev (PDE.mStar d : ℝ) φ) (hφc : Continuous φ)
    (hinit : InitialFluctuation S R m₀ Cin ε
      (transportedTests S (fun _ : Fin 1 => t) (fun _ => φ))),
    Tendsto (fun N => wassersteinE 1
      (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) (fun _ : Fin 1 => t) (fun _ => φ))
      (surrogateStatLaw (L.dyn S) L.ρ L.A L.invβstar (fun _ : Fin 1 => t) (fun _ => φ)
        (R N).P (R N).η)) atTop (𝓝 0) := by
  obtain ⟨C₀min, h8⟩ := main_torus_stat_proof (d := d) s
  obtain ⟨C₀min', h8t⟩ := main_torus_stat_tendsto_proof (d := d) s
  refine ⟨max C₀min C₀min', fun Rg ν₀ MB Λ T VB Cin C₀ Cc hC S hs hT R 𝔈 hstand L hcoef m₀ ε t ht
    φ hφ hφc hinit => ?_⟩
  obtain ⟨C8, Λ8, hC8, hΛ8, h8'⟩ := h8 Rg ν₀ MB Λ T VB Cin C₀ Cc (le_trans (le_max_left _ _) hC)
  have hrate := ((h8t Rg ν₀ MB Λ T VB Cin C₀ Cc (le_trans (le_max_right _ _) hC) S hs hT R 𝔈
    hstand).1 m₀ ε _ hinit)
  have hm₀ : m₀ ≤ PDE.mStar d := hinit.m₀_le
  have hmS : PDE.mStar d ≤ PDE.mStar d := le_rfl
  -- the second term: A.34 base, for the realization `R 1` (the law of `η` does not depend on `N`)
  have hFM1 := HRS.Main.A1014.a1014_functionalMoment hinit (le_refl 1)
  have hlim := surrogate_to_limit_stat_base (d := d) s Rg ν₀ MB Λ T VB Cin (PDE.mStar d) m₀
    (by unfold PDE.mStar; omega) hm₀ hmS S hs hT L hcoef (R 1).P (R 1).η hFM1 t ht φ hφ hφc
  obtain ⟨νη, hνη⟩ := hinit.fixed_law
  have hlim' : Tendsto (fun N => wassersteinE 1
      (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin 1 => t) (fun _ => φ)
        (R N).P (R N).η)
      (surrogateStatLaw (L.dyn S) L.ρ L.A L.invβstar (fun _ : Fin 1 => t) (fun _ => φ)
        (R N).P (R N).η)) atTop (𝓝 0) := by
    refine hlim.congr' ?_
    filter_upwards [eventually_ge_atTop 1] with N hN
    rw [HRS.Main.A1014.a1014_surr_law_eq (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) _ _ (R 1).P (R 1).η
        (R N).P (R N).η (hinit.η_meas 1) (hinit.η_meas N) ((hνη 1 le_rfl).trans (hνη N hN).symm),
      HRS.Main.A1014.a1014_surr_law_eq (L.dyn S) L.ρ L.A L.invβstar _ _ (R 1).P (R 1).η
        (R N).P (R N).η (hinit.η_meas 1) (hinit.η_meas N) ((hνη 1 le_rfl).trans (hνη N hN).symm)]
  -- the first term
  have hup : Tendsto (fun N => ENNReal.ofReal (statBound C8 Λ8 t (sobolevNorm (PDE.mStar d : ℝ) φ)
      (masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N))) atTop (𝓝 0) := by
    have h1 := hrate.const_mul (C8 * Real.exp (Λ8 * t) * (sobolevNorm (PDE.mStar d : ℝ) φ) *
      (1 + sobolevNorm (PDE.mStar d : ℝ) φ))
    rw [mul_zero] at h1
    have h2 : Tendsto (fun N => statBound C8 Λ8 t (sobolevNorm (PDE.mStar d : ℝ) φ)
      (masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N)) atTop (𝓝 0) := by
      refine h1.congr fun N => ?_
      unfold statBound
      ring
    simpa using ENNReal.tendsto_ofReal h2
  have hsum : Tendsto (fun N => ENNReal.ofReal (statBound C8 Λ8 t (sobolevNorm (PDE.mStar d : ℝ) φ)
      (masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N)) +
      wassersteinE 1
      (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin 1 => t) (fun _ => φ)
        (R N).P (R N).η)
      (surrogateStatLaw (L.dyn S) L.ρ L.A L.invβstar (fun _ : Fin 1 => t) (fun _ => φ)
        (R N).P (R N).η)) atTop (𝓝 0) := by
    simpa using hup.add hlim'
  refine tendsto_of_tendsto_of_tendsto_of_le_of_le' tendsto_const_nhds hsum
    (Filter.Eventually.of_forall fun N => bot_le) ?_
  filter_upwards [eventually_ge_atTop (max 1 ⌈C8⌉₊)] with N hN
  have hN1 : 1 ≤ N := le_trans (le_max_left _ _) hN
  have hN8 : C8 ≤ N := (Nat.le_ceil C8).trans (by exact_mod_cast le_trans (le_max_right _ _) hN)
  have hA8 := (h8' S hs hT R 𝔈 hstand).1 m₀ ε t φ ht hφ hφc hinit N hN8
  have hηm := hinit.η_meas N
  haveI hSN := HRS.Main.A1014.a1014_surr_prob (S.dyn N) (S.ρ N) (S.AN N) (S.qN N)
    (fun _ : Fin 1 => t) (fun _ => φ) (R N).P (R N).η hηm
  haveI hSI := HRS.Main.A1014.a1014_surr_prob (L.dyn S) L.ρ L.A L.invβstar
    (fun _ : Fin 1 => t) (fun _ => φ) (R N).P (R N).η hηm
  have hfin := ne_top_of_le_ne_top ENNReal.ofReal_ne_top hA8
  refine (HRS.Main.A1014.a1014_w1_chain _ _ _ hfin).trans ?_
  exact add_le_add hA8 le_rfl

example := (@true_limit_stat_base_proof : type_of% @HRS.Main.true_limit_stat_base)

theorem true_limit_field_proof (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin Cs : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ),
        TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈 →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuation S R m₀ Cin ε (fun _ => ∅) →
        ∀ (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ))
          (νin : Measure (NegSobolev d (gammaIdx d : ℝ))),
          InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin →
        ∀ (L : LimitCoeffs d),
          CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d) →
          (∀ N : ℕ, 1 ≤ N → ∀ t' ∈ Set.Icc (0 : ℝ) T,
            smoothDist 2
              (law (R N).P (fun ω => S.AN N •
                transportField (S.dyn N) (S.ρ N) t' (gammaIdx d : ℝ) (ηF N ω)))
              (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
                L.A • transportField (L.dyn S) L.ρ t' (gammaIdx d : ℝ) F)) ≤
              Cs * S.coeffDiscrepancy L (gammaIdx d) N) →
        ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ N : ℕ, C ≤ (N : ℝ) →
        ∀ νG νGlim : Measure (NegSobolev d (gammaIdx d : ℝ)),
          IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG →
          IsLinearFieldNoise (L.dyn S) L.ρ L.invβstar t (gammaIdx d : ℝ) νGlim →
          smoothDist 2
            (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
            (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim) ≤
          C * Real.exp (ΛT * t) *
            (fieldRate d (εf N) (S.qN N) (S.sigma N) (𝔈 N) N +
              (S.coeffDiscrepancy L (gammaIdx d) N + Real.sqrt (S.coeffDiscrepancy L (gammaIdx d) N))) := by
  obtain ⟨C₀min, h9⟩ := main_torus_field_proof (d := d) s
  refine ⟨C₀min, fun Rg ν₀ MB Λ T VB Cin Cs C₀ Cc hC => ?_⟩
  obtain ⟨C9, Λ9, hC9, hΛ9, h9'⟩ := h9 Rg ν₀ MB Λ T VB Cin C₀ Cc hC
  by_cases hg : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  swap
  · exact ⟨1, 1, one_pos, one_pos, fun S hs => absurd ⟨S.hd, hs ▸ S.hs0, hs ▸ S.hsd⟩ hg⟩
  obtain ⟨hd, hs0, hsd⟩ := hg
  obtain ⟨Cg, hCg, hg'⟩ := HRS.A34.a34_gauss_couple hd s hs0 hsd Rg ν₀ MB Λ VB T
  refine ⟨C9 + |Cs| + Real.sqrt Cg + 1, Λ9 + 1, by positivity, by positivity, ?_⟩
  intro S hs hT R 𝔈 hS m₀ ε hinit εf ηF νin hfield L hcoef hCs t ht N hN νG νGlim hνG hνGlim
  have hNpos : (0 : ℝ) < N := lt_of_lt_of_le (by positivity) hN
  have hN0 : 0 < N := by exact_mod_cast hNpos
  have hN1 : 1 ≤ N := by omega
  have hN9 : C9 ≤ N := le_trans (by have := abs_nonneg Cs; have := Real.sqrt_nonneg Cg; linarith) hN
  -- the A.9 comparison particle / linear field with the coupled initial field
  have hA9 := ((h9' S hs hT R 𝔈 hS m₀ ε hinit εf ηF νin hfield t ht).1 N hN9 νG hνG)
  have hGauss := hg' S L hs hT hcoef N hN1 t ht νG νGlim hνG hνGlim
  subst hs hT
  haveI := hνG.1
  haveI := hνGlim.1
  haveI := InitialDataAux.negSobolev_secondCountable d (gammaIdx d : ℝ)
  haveI : IsProbabilityMeasure νin := by
    rw [← hfield.law_eq 1 le_rfl]
    infer_instance
  obtain ⟨hmT₁, hmT₂⟩ := HRS.A34.a34_transport_meas S L Rg ν₀ MB Λ VB hcoef N hN1 ht
  have hmA₁ : Measurable (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F) := hmT₁.const_smul (S.AN N)
  have hmA₂ : Measurable (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F) := hmT₂.const_smul L.A
  have hμ₁ : IsProbabilityMeasure (law (R N).P (fun ω => S.AN N •
      transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) (ηF N ω))) :=
    inferInstance
  have hμ₂ : IsProbabilityMeasure (law νin (fun F : NegSobolev d (gammaIdx d : ℝ) =>
      L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F)) :=
    inferInstance
  have hΔ0 := HRS.Main.A1014.a1014_delta_nonneg hcoef hN1
  set Δ := S.coeffDiscrepancy L (gammaIdx d) N with hΔ
  have hdg : smoothDist 2 νG νGlim ≤ Real.sqrt Cg * (Δ + Real.sqrt Δ) :=
    HRS.Main.A1014.a1014_gauss_dist hCg hΔ0 hGauss
  have hconv : smoothDist 2
      (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG)
      (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim) ≤
      Cs * Δ + Real.sqrt Cg * (Δ + Real.sqrt Δ) := by
    unfold linearFieldLaw limitFieldLaw linearFieldLaw
    refine (HRS.A34.a34_smoothDist_conv _ _ νG νGlim).trans ?_
    exact add_le_add (hCs N hN1 t ht) hdg
  have hεf := hfield.εf_nonneg N hN1
  have hfr := HRS.Main.A1014.a1014_fieldRate_nonneg (d := d) (N := N) hεf
    (HRS.Main.A8P.a8p_q_bounds S hN1).1 (HRS.Main.A8P.a8p_sigma_nonneg S N)
    (hS.energy.pos N hN1).le
  haveI hpp := HRS.Main.A9.a9_particle_prob (S := S) (R := R) (N := N) (gammaIdx d : ℝ) t
  haveI hlinP : IsProbabilityMeasure
      (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) := by
    unfold linearFieldLaw
    infer_instance
  haveI hlimP : IsProbabilityMeasure (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim) := by
    unfold limitFieldLaw linearFieldLaw
    have : IsProbabilityMeasure (law νin (fun ω : NegSobolev d (gammaIdx d : ℝ) =>
        L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) (id ω))) := hμ₂
    infer_instance
  have htri := smoothDist_triangle 2
    (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
    (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG)
    (limitFieldLaw S L (gammaIdx d : ℝ) νin t νGlim)
  have hsq : Δ ≤ Δ + Real.sqrt Δ := le_add_of_nonneg_right (Real.sqrt_nonneg _)
  refine htri.trans ?_
  refine (add_le_add hA9 hconv).trans ?_
  have := HRS.Main.A1014.a1014_arith_field hC9 (Real.sqrt_nonneg Cg) ht.1 hΛ9 hfr hΔ0 hsq
    (Real.sqrt Cg * (Δ + Real.sqrt Δ)) le_rfl (Cs * Δ) le_rfl
  linarith

example := (@true_limit_field_proof : type_of% @HRS.Main.true_limit_field)

end Main

end HRS
