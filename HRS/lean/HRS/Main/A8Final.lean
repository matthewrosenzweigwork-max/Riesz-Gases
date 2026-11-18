import HRS.Main.TorusTheorems
import HRS.Main.A8PAux46

/-!
# Packet A8P: relocated proofs of Proposition A.8 (`main_torus_stat`, `main_torus_stat_tendsto`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

open HRS.Main.A8P

variable {d : ℕ}

theorem a8p_realIm_cont {n : ℕ} {φ : Fin (n + 1) → Torus d → ℂ} (h : ∀ a, Continuous (φ a))
    (ab : Fin (n + 1) × Bool) : Continuous (realImParts φ ab) := by
  unfold realImParts
  cases ab.2
  · exact Complex.continuous_re.comp (h ab.1)
  · exact Complex.continuous_im.comp (h ab.1)

theorem a8p_realIm_mem {n : ℕ} {φ : Fin (n + 1) → Torus d → ℂ} {m : ℝ}
    (h : ∀ a, MemSobolevC m (φ a)) (ab : Fin (n + 1) × Bool) : MemSobolev m (realImParts φ ab) := by
  unfold realImParts
  cases ab.2
  · simpa using (h ab.1).1
  · simpa using (h ab.1).2

theorem main_torus_stat_proof (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ),
        TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 →
        -- (a) single statistics, `W₁`
        (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (t : ℝ) (φ : Torus d → ℝ), t ∈ Set.Icc (0 : ℝ) T →
          MemSobolev (PDE.mStar d : ℝ) φ → Continuous φ →
          InitialFluctuation S R m₀ Cin ε
            (transportedTests S (fun _ : Fin 1 => t) (fun _ => φ)) →
          ∀ N : ℕ, C ≤ (N : ℝ) →
            wassersteinE 1
              (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) (fun _ : Fin 1 => t) (fun _ => φ))
              (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin 1 => t)
                (fun _ => φ) (R N).P (R N).η) ≤
            ENNReal.ofReal (statBound C ΛT t (sobolevNorm (PDE.mStar d : ℝ) φ)
              (masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N))) ∧
        -- (b) joint statistics, `d_{C²}`
        (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (t : ℝ) (p : ℕ) (φ : Fin p → Torus d → ℝ), 1 ≤ p →
          t ∈ Set.Icc (0 : ℝ) T → (∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) →
          (∀ a, Continuous (φ a)) →
          InitialFluctuation S R m₀ Cin ε (transportedTests S (fun _ : Fin p => t) φ) →
          ∀ N : ℕ, C ≤ (N : ℝ) →
            smoothDist 2
              (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) (fun _ : Fin p => t) φ)
              (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin p => t) φ
                (R N).P (R N).η) ≤
            statBound C ΛT t (∑ a, sobolevNorm (PDE.mStar d : ℝ) (φ a))
              (masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N)) ∧
        -- (c) complex tests, finitely many times, `d_{C²}`
        (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (n : ℕ) (ts : Fin (n + 1) → ℝ) (φ : Fin (n + 1) → Torus d → ℂ),
          Monotone ts → 0 ≤ ts 0 → ts (Fin.last n) ≤ T →
          (∀ a, MemSobolevC (PDE.mStar d : ℝ) (φ a)) → (∀ a, Continuous (φ a)) →
          InitialFluctuation S R m₀ Cin ε
            (transportedTests S (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImParts φ)) →
          ∀ N : ℕ, C ≤ (N : ℝ) →
            smoothDist 2
              (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N)
                (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImParts φ))
              (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N)
                (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImParts φ) (R N).P (R N).η) ≤
            statBound C ΛT (ts (Fin.last n)) (∑ a, sobolevNormC (PDE.mStar d : ℝ) (φ a))
              (masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N)) ∧
        -- (d) joint `W₂` variant under A.7, complex tests, finitely many times
        (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (𝔈' ε2 : ℕ → ℝ) (n : ℕ) (ts : Fin (n + 1) → ℝ)
          (φ : Fin (n + 1) → Torus d → ℂ),
          Monotone ts → 0 ≤ ts 0 → ts (Fin.last n) ≤ T →
          (∀ a, MemSobolevC (PDE.mStar d : ℝ) (φ a)) → (∀ a, Continuous (φ a)) →
          InitialFluctuation S R m₀ Cin ε
            (transportedTests S (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImParts φ)) →
          EnergySmallness2 S R C₀ Λ m₀
            (transportedTests S (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImParts φ)) 𝔈' ε2 →
          ∀ N : ℕ, C ≤ (N : ℝ) →
            wassersteinE 2
              (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N)
                (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImParts φ))
              (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N)
                (fun ab : Fin (n + 1) × Bool => ts ab.1) (realImParts φ) (R N).P (R N).η) ≤
            ENNReal.ofReal (statBound C ΛT (ts (Fin.last n)) (∑ a, sobolevNormC (PDE.mStar d : ℝ) (φ a))
              (masterRate d (ε2 N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈' N) N))) := by

  by_cases hok : 1 ≤ d ∧ 0 ≤ s ∧ s < d
  swap
  · refine ⟨0, fun Rg ν₀ MB Λ T VB Cin C₀ Cc _ => ⟨1, 1, one_pos, one_pos, fun S hs => ?_⟩⟩
    exact absurd ⟨S.hd, hs ▸ S.hs0, hs ▸ S.hsd⟩ hok
  obtain ⟨hd, hs0, hsd⟩ := hok
  obtain ⟨C₀', Cq, hC₀', hCq, hcom⟩ := a8p_commSpec hd hs0 hsd
  refine ⟨C₀', fun Rg ν₀ MB Λ T VB Cin C₀ Cc hC => ?_⟩
  obtain ⟨Ca, Λ₁, hCa, hspec⟩ := a8p_adjSpec hd s hs0 hsd Rg MB Λ VB ν₀
  obtain ⟨Cp, hCp0, hCp⟩ := a8p_hom_prod hd hs0 hsd
  obtain ⟨cT, hcT0, hcT⟩ := a8p_transport_bound hd MB s hs0
  obtain ⟨Cb, hCb⟩ : ∃ x : ℝ, x = (1 / 2) * Cq * cT * T + 1 + 4 * T * d * Ca ^ 2 +
      2 * T * Cq * (2 * d * Ca ^ 2 + Cp) := ⟨_, rfl⟩
  obtain ⟨Cw, hCw⟩ : ∃ x : ℝ, x = (1 / 2) * Cq * cT * T + 1 +
      Real.sqrt (2 * T * Cq * (2 * d * Ca ^ 2 + Cp)) := ⟨_, rfl⟩
  refine ⟨2 + 4 * |Cb| + 4 * |Cw|, 2 * |Λ₁| + 1, by positivity, by positivity, ?_⟩
  intro S hSs hST R 𝔈 hS
  subst hSs hST
  have hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT :=
    ⟨hCa.le, hspec, hcom, hCq.le, hC, hCp0, hCp, hcT0, hcT⟩
  have hT0 : 0 ≤ S.T := S.hT.le
  have hCb0 : 0 ≤ Cb := by rw [hCb]; have := hCq.le; positivity
  have hCw0 : 0 ≤ Cw := by rw [hCw]; have := hCq.le; positivity
  have hN2 : ∀ N : ℕ, 2 + 4 * |Cb| + 4 * |Cw| ≤ (N : ℝ) → 2 ≤ N := fun N hN => by
    have : (2 : ℝ) ≤ N := le_trans (by nlinarith [abs_nonneg Cb, abs_nonneg Cw]) hN
    exact_mod_cast this
  have hCC : ∀ x : ℝ, 0 ≤ x → x = Cb ∨ x = Cw → 4 * x ≤ 2 + 4 * |Cb| + 4 * |Cw| := by
    intro x hx h
    rcases h with h | h
    · rw [h]; nlinarith [abs_nonneg Cb, abs_nonneg Cw, le_abs_self Cb]
    · rw [h]; nlinarith [abs_nonneg Cb, abs_nonneg Cw, le_abs_self Cw]
  refine ⟨?_, ?_, ?_, ?_⟩
  · -- (a)
    intro m₀ ε t φ ht hφ hφc hIF N hN
    have hN2' := hN2 N hN
    have hN1 : 1 ≤ N := by omega
    have key := a8p_case_wass1 hP hS hN2' (fun _ : Fin 1 => t) (fun _ => ht) (fun _ => φ)
      (fun _ => hφc) (fun _ => hφ) hIF
    rw [← hCw] at key
    refine key.trans (ENNReal.ofReal_le_ofReal ?_)
    have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
    have hr := a8p_masterRate_nonneg (d := d) (N := N) hε (a8p_q_bounds S hN1).1
      (a8p_sigma_nonneg S N) (hS.energy.pos N hN1).le (hS.energy.pos N hN1).le
    refine a8p_stat_real hCw0 hr ?_ ?_ zero_le_one one_le_two (Real.sqrt_nonneg _) ht.1
      (hCC Cw hCw0 (Or.inr rfl))
    · exact Finset.sum_nonneg fun a _ => a8pK_nonneg Λ₁ t φ
    · simp [a8pK]
  · -- (b)
    intro m₀ ε t p φ hp ht hφ hφc hIF N hN
    have hN2' := hN2 N hN
    have hN1 : 1 ≤ N := by omega
    have key := a8p_case_smooth hP hS hN2' (fun _ : Fin p => t) (fun _ => ht) φ hφc hφ hIF
    rw [← hCb] at key
    refine key.trans ?_
    have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
    have hr := a8p_masterRate_nonneg (d := d) (N := N) hε (a8p_q_bounds S hN1).1
      (a8p_sigma_nonneg S N) (hS.energy.pos N hN1).le (hS.energy.pos N hN1).le
    refine a8p_stat_real hCb0 hr ?_ ?_ zero_le_one one_le_two
      (Finset.sum_nonneg fun a _ => Real.sqrt_nonneg _) ht.1 (hCC Cb hCb0 (Or.inl rfl))
    · exact Finset.sum_nonneg fun a _ => a8pK_nonneg Λ₁ t (φ a)
    · rw [a8p_Ksum_const]; simp
  · -- (c)
    intro m₀ ε n ts φ hmono h0 hlast hφ hφc hIF N hN
    have hN2' := hN2 N hN
    have hN1 : 1 ≤ N := by omega
    have htsm : ∀ ab : Fin (n + 1) × Bool, ts ab.1 ∈ Set.Icc (0 : ℝ) S.T := fun ab =>
      ⟨h0.trans (hmono (Fin.zero_le _)), (hmono (Fin.le_last _)).trans hlast⟩
    have key := a8p_case_smooth hP hS hN2' (fun ab : Fin (n + 1) × Bool => ts ab.1) htsm (realImParts φ)
      (a8p_realIm_cont hφc) (fun ab => a8p_realIm_mem hφ ab) hIF
    rw [← hCb] at key
    refine key.trans ?_
    have hε : 0 ≤ ε N := hIF.eps_anti.le_of_tendsto hIF.eps_tendsto N
    have hr := a8p_masterRate_nonneg (d := d) (N := N) hε (a8p_q_bounds S hN1).1
      (a8p_sigma_nonneg S N) (hS.energy.pos N hN1).le (hS.energy.pos N hN1).le
    have ht0 : 0 ≤ ts (Fin.last n) := h0.trans (hmono (Fin.zero_le _))
    refine a8p_stat_real hCb0 hr ?_ (a8p_Ksum_complex Λ₁ ts hmono φ) zero_le_two le_rfl
      (Finset.sum_nonneg fun a _ => Real.sqrt_nonneg _) ht0 (hCC Cb hCb0 (Or.inl rfl))
    exact Finset.sum_nonneg fun a _ => a8pK_nonneg Λ₁ _ _
  · -- (d)
    intro m₀ ε 𝔈' ε2 n ts φ hmono h0 hlast hφ hφc hIF hE2 N hN
    have hN2' := hN2 N hN
    have hN1 : 1 ≤ N := by omega
    have htsm : ∀ ab : Fin (n + 1) × Bool, ts ab.1 ∈ Set.Icc (0 : ℝ) S.T := fun ab =>
      ⟨h0.trans (hmono (Fin.zero_le _)), (hmono (Fin.le_last _)).trans hlast⟩
    have key := a8p_case_wass2 hP hS hN2' (fun ab : Fin (n + 1) × Bool => ts ab.1) htsm (realImParts φ)
      (a8p_realIm_cont hφc) (fun ab => a8p_realIm_mem hφ ab) hIF hE2
    rw [← hCw] at key
    refine key.trans (ENNReal.ofReal_le_ofReal ?_)
    have hε : 0 ≤ ε2 N := hE2.ε2_nonneg N hN1
    have hr := a8p_masterRate_nonneg (d := d) (N := N) hε (a8p_q_bounds S hN1).1
      (a8p_sigma_nonneg S N) (hS.energy.pos N hN1).le (hE2.𝔈'_nonneg N hN1)
    have ht0 : 0 ≤ ts (Fin.last n) := h0.trans (hmono (Fin.zero_le _))
    refine a8p_stat_real hCw0 hr ?_ (a8p_Ksum_complex Λ₁ ts hmono φ) zero_le_two le_rfl
      (Finset.sum_nonneg fun a _ => Real.sqrt_nonneg _) ht0 (hCC Cw hCw0 (Or.inr rfl))
    exact Finset.sum_nonneg fun a _ => a8pK_nonneg Λ₁ _ _

theorem main_torus_stat_tendsto_proof (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (S : MainData d), S.s = s → S.T = T →
    ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ),
    TorusStanding S R Rg ν₀ MB Λ VB (PDE.mStar d) C₀ Cc 𝔈 →
    (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (Ψ : ℕ → Set (Torus d → ℝ)), InitialFluctuation S R m₀ Cin ε Ψ →
      Tendsto (fun N => masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N) atTop (𝓝 0)) ∧
    (∀ (m₀ : ℕ) (ε : ℕ → ℝ) (t : ℝ) (p : ℕ) (φ : Fin p → Torus d → ℝ), 1 ≤ p →
      t ∈ Set.Icc (0 : ℝ) T → (∀ a, MemSobolev (PDE.mStar d : ℝ) (φ a)) →
      (∀ a, Continuous (φ a)) →
      InitialFluctuation S R m₀ Cin ε (transportedTests S (fun _ : Fin p => t) φ) →
      Tendsto (fun N => smoothDist 2
        (fluctStatLaw (R N).P (S.sigma N) (R N).X (S.ρ N) (fun _ : Fin p => t) φ)
        (surrogateStatLaw (S.dyn N) (S.ρ N) (S.AN N) (S.qN N) (fun _ : Fin p => t) φ
          (R N).P (R N).η)) atTop (𝓝 0)) := by
  obtain ⟨C₀min, h⟩ := main_torus_stat_proof (d := d) s
  refine ⟨C₀min, fun Rg ν₀ MB Λ T VB Cin C₀ Cc hC S hSs hST R 𝔈 hS => ?_⟩
  obtain ⟨C, ΛT, hC0, hΛT, hmain⟩ := h Rg ν₀ MB Λ T VB Cin C₀ Cc hC
  obtain ⟨-, hb, -, -⟩ := hmain S hSs hST R 𝔈 hS
  have hrate : ∀ (m₀ : ℕ) (ε : ℕ → ℝ) (Ψ : ℕ → Set (Torus d → ℝ)), InitialFluctuation S R m₀ Cin ε Ψ →
      Tendsto (fun N => masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N) atTop (𝓝 0) :=
    fun m₀ ε Ψ hIF => a8p_rate_tendsto S S.hd ε 𝔈 hIF.eps_tendsto hS.energy.small
      (fun N hN => (hS.energy.pos N hN).le)
  refine ⟨hrate, ?_⟩
  intro m₀ ε t p φ hp ht hφ hφc hIF
  have hr := hrate m₀ ε _ hIF
  have hup : Tendsto (fun N => statBound C ΛT t (∑ a, sobolevNorm (PDE.mStar d : ℝ) (φ a))
      (masterRate d (ε N) (S.qN N) (S.sigma N) (𝔈 N) (𝔈 N) N)) atTop (𝓝 0) := by
    have h1 := hr.const_mul (C * Real.exp (ΛT * t) * (∑ a, sobolevNorm (PDE.mStar d : ℝ) (φ a)) *
      (1 + ∑ a, sobolevNorm (PDE.mStar d : ℝ) (φ a)))
    rw [mul_zero] at h1
    refine h1.congr fun N => ?_
    unfold statBound
    ring
  refine squeeze_zero' (Filter.Eventually.of_forall fun N => smoothDist_nonneg _ _ _) ?_ hup
  filter_upwards [Filter.eventually_ge_atTop ⌈C⌉₊] with N hN
  exact hb m₀ ε t p φ hp ht hφ hφc hIF N ((Nat.le_ceil C).trans (by exact_mod_cast hN))

example := (@main_torus_stat_proof : type_of% @HRS.Main.main_torus_stat)

example := (@main_torus_stat_tendsto_proof : type_of% @HRS.Main.main_torus_stat_tendsto)

end Main

end HRS
