import HRS.Main.A9Aux21

/-!
# Packet A9, part 22: Proposition A.9, comparison with the linear field (`main_torus_field`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory

namespace HRS.Main.A9

open HRS HRS.A33 HRS.PDE HRS.Main.A8P HRS.GF HRS.Uniform

variable {d : ℕ}

theorem a9_field_main (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin : ℝ) (C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∃ C ΛT : ℝ, 0 < C ∧ 0 < ΛT ∧
      ∀ (S : MainData d), S.s = s → S.T = T →
      ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ),
        TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈 →
        ∀ (m₀ : ℕ) (ε : ℕ → ℝ), InitialFluctuation S R m₀ Cin ε (fun _ => ∅) →
        ∀ (εf : ℕ → ℝ) (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ))
          (νin : Measure (NegSobolev d (gammaIdx d : ℝ))),
          InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin →
        ∀ t ∈ Set.Icc (0 : ℝ) T,
          (∀ N : ℕ, C ≤ (N : ℝ) →
            ∀ νG : Measure (NegSobolev d (gammaIdx d : ℝ)),
              IsLinearFieldNoise (S.dyn N) (S.ρ N) (S.qN N) t (gammaIdx d : ℝ) νG →
              smoothDist 2
                (particleFieldLaw (R N).P (S.sigma N) (gammaIdx d : ℝ) (R N).X (S.ρ N) t)
                (linearFieldLaw (R N).P (S.dyn N) (S.ρ N) (S.AN N) t (gammaIdx d : ℝ) (ηF N) νG) ≤
              C * Real.exp (ΛT * t) *
                fieldRate d (εf N) (S.qN N) (S.sigma N) (𝔈 N) N) ∧
          ∃ B : ℝ, ∀ N : ℕ, 1 ≤ N →
            ∫⁻ ω, ‖S.sigma N • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
                (empirical ((R N).X (Real.toNNReal t) ω)) (withDensityReal (S.ρ N t))‖ₑ ∂(R N).P ≤
              ENNReal.ofReal B := by
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
  obtain ⟨Ktr, hKtr0, hKtr'⟩ := HRS.A34.a34_transport_unif hd s hs0 hsd Rg MB Λ VB ν₀ T
  obtain ⟨Z0, hZ0⟩ : ∃ x : ℝ, x = ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-((d : ℝ) + 3)) := ⟨_, rfl⟩
  have hZ00 : 0 ≤ Z0 := by
    rw [hZ0]; exact tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos k.1).le _
  obtain ⟨Kb, hKb⟩ : ∃ x : ℝ, x = Real.exp (|Λ₁| * T) * Z0 := ⟨_, rfl⟩
  have hKb0 : 0 ≤ Kb := by rw [hKb]; exact mul_nonneg (Real.exp_pos _).le hZ00
  obtain ⟨c1, hc1⟩ : ∃ x : ℝ, x = (1 / 2) * Cq * cT * |T| * Kb := ⟨_, rfl⟩
  obtain ⟨c2, hc2⟩ : ∃ x : ℝ, x = |T| * Cq * Kb ^ 2 * (2 * d * Ca ^ 2 + Cp) := ⟨_, rfl⟩
  have hc10 : 0 ≤ c1 := by rw [hc1]; positivity
  have hc20 : 0 ≤ c2 := by
    rw [hc2]
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    positivity
  refine ⟨2 + Ktr + c1 + c2, 1, by positivity, one_pos, ?_⟩
  intro S hSs hST R 𝔈 hS m₀ ε hinit εf ηF νin hfield t ht
  subst hSs hST
  have hT0 : 0 < S.T := S.hT
  have hTabs : |S.T| = S.T := abs_of_pos hT0
  have hP : A8Pack d S.s Rg MB Λ VB ν₀ C₀ Ca Λ₁ C₀' Cq Cp cT :=
    ⟨hCa.le, hspec, hcom, hCq.le, hC, hCp0, hCp, hcT0, hcT⟩
  have hS' := a9_standing_mStar hS
  refine ⟨?_, ?_⟩
  · intro N hN νG hνG
    have hN2 : 2 ≤ N := by
      have h2 : (2 : ℝ) ≤ N := le_trans (by linarith) hN
      exact_mod_cast h2
    have hN1 : 1 ≤ N := by omega
    have hεf := hfield.εf_nonneg N hN1
    have h𝔈 := (hS.energy.pos N hN1).le
    have hσ := a8p_sigma_nonneg S N
    obtain ⟨hq0, hq1⟩ := a8p_q_bounds S hN1
    have hn0 : 0 ≤ (N : ℝ) ^ (-(1 : ℝ) / d) := Real.rpow_nonneg (Nat.cast_nonneg N) _
    have hsq : 0 ≤ (𝔈 N) ^ ((1 : ℝ) / 2) := Real.rpow_nonneg h𝔈 _
    have hKtot : ∑' j, a9K d Λ₁ t j ≤ Kb := by
      rw [hKb, hZ0]; exact a9K_tsum_le Λ₁ ht
    refine le_of_forall_pos_le_add fun ε' hε' => ?_
    set c3 : ℝ := 2 * Real.sqrt (2 * S.T) * (d * Ca) with hc3
    have hc30 : 0 ≤ c3 := by
      have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
      positivity
    obtain ⟨q, k, hk, htl⟩ := a9_exists_finite_tail (d := d) Λ₁ t (ε := ε' / (c3 + 1))
      (by positivity)
    have key := a9_field_bound hP hKtr0 hKtr' hS hN2 hfield ht hνG hk hKtot
    have htl0 := a9tail_nonneg (d := d) Λ₁ t k
    have hctl : c3 * a9tail d Λ₁ t k ≤ ε' := by
      calc c3 * a9tail d Λ₁ t k ≤ c3 * (ε' / (c3 + 1)) := mul_le_mul_of_nonneg_left htl hc30
        _ ≤ ε' := by
          rw [mul_div_assoc', div_le_iff₀ (by positivity)]
          linarith
    have hKe : (1 / 2) * Cq * cT * S.T * Kb = c1 := by rw [hc1, hTabs]
    have hKe2 : S.T * Cq * Kb ^ 2 * (2 * d * Ca ^ 2 + Cp) = c2 := by rw [hc2, hTabs]
    rw [hKe, hKe2] at key
    have hexp : 1 ≤ Real.exp (1 * t) := by rw [one_mul]; exact Real.one_le_exp ht.1
    unfold fieldRate
    set X : ℝ := S.qN N * ((𝔈 N) ^ ((1 : ℝ) / 2) + (N : ℝ) ^ (-(1 : ℝ) / d)) with hX
    have hX0 : 0 ≤ X := by positivity
    have hσE : 0 ≤ S.sigma N * 𝔈 N := mul_nonneg hσ h𝔈
    have hfr : 0 ≤ εf N + S.sigma N * 𝔈 N + X := by positivity
    have h1 : Ktr * εf N + c1 * (S.sigma N * 𝔈 N) + c2 * X ≤
        (Ktr + c1 + c2) * (εf N + S.sigma N * 𝔈 N + X) := by
      linarith [mul_nonneg hKtr0 (add_nonneg hσE hX0), mul_nonneg hc10 (add_nonneg hεf hX0),
        mul_nonneg hc20 (add_nonneg hεf hσE)]
    have h2 : (Ktr + c1 + c2) * (εf N + S.sigma N * 𝔈 N + X) ≤
        (2 + Ktr + c1 + c2) * Real.exp (1 * t) * (εf N + S.sigma N * 𝔈 N + X) := by
      have h3 : Ktr + c1 + c2 ≤ (2 + Ktr + c1 + c2) * Real.exp (1 * t) := by
        have : 0 ≤ 2 + Ktr + c1 + c2 := by positivity
        have h4 := mul_le_mul_of_nonneg_left hexp this
        linarith
      exact mul_le_mul_of_nonneg_right h3 hfr
    linarith [key, hctl, h1, h2]
  · obtain ⟨B𝔈, hB𝔈⟩ : ∃ B : ℝ, ∀ N, S.sigma N * 𝔈 N ≤ B := by
      obtain ⟨B, hB⟩ := hS.energy.small.bddAbove_range
      exact ⟨B, fun N => hB ⟨N, rfl⟩⟩
    obtain ⟨c0, hc0⟩ : ∃ x : ℝ, x = Real.sqrt (8 * ∑' k : NonzeroLattice d,
        Lattice.jp k.1 ^ (-(2 * (gammaIdx d : ℝ)))) := ⟨_, rfl⟩
    have hc00 : 0 ≤ c0 := by rw [hc0]; exact Real.sqrt_nonneg _
    have hσ1 := a8p_sigma_nonneg S 1
    have hCd : 0 ≤ (d : ℝ) * Ca := mul_nonneg (Nat.cast_nonneg d) hCa.le
    have hcc : 0 ≤ (1 / 2) * (Cq * cT) * S.T := by positivity
    set Bm : ℝ := max B𝔈 0 with hBm
    have hBm0 : 0 ≤ Bm := le_max_right _ _
    refine ⟨S.sigma 1 * c0 + (Ktr * (1 + Cin ^ 2) +
      ((1 / 2) * (Cq * cT) * S.T * Bm + Real.sqrt (2 * S.T) * (d * Ca)) * Kb), fun N hN => ?_⟩
    have hrest : 0 ≤ Ktr * (1 + Cin ^ 2) +
        ((1 / 2) * (Cq * cT) * S.T * Bm + Real.sqrt (2 * S.T) * (d * Ca)) * Kb := by
      have : 0 ≤ Real.sqrt (2 * S.T) * (d * Ca) := mul_nonneg (Real.sqrt_nonneg _) hCd
      have h2 : 0 ≤ (1 / 2) * (Cq * cT) * S.T * Bm := mul_nonneg hcc hBm0
      have h3 : 0 ≤ Ktr * (1 + Cin ^ 2) := mul_nonneg hKtr0 (by positivity)
      have h4 := mul_nonneg (add_nonneg h2 this) hKb0
      linarith
    by_cases hN1 : N = 1
    · subst hN1
      have hρ := (hS.mean_field.solution 1 le_rfl).density t ht
      haveI : IsProbabilityMeasure (withDensityReal (S.ρ 1 t)) := HRS.isProb_withDensityReal hρ
      calc ∫⁻ ω, ‖S.sigma 1 • NegSobolev.ofMeasureDiff (gammaIdx d : ℝ)
              (empirical ((R 1).X (Real.toNNReal t) ω)) (withDensityReal (S.ρ 1 t))‖ₑ ∂(R 1).P
          ≤ ∫⁻ _ω, ENNReal.ofReal (S.sigma 1 * c0) ∂(R 1).P := by
            refine lintegral_mono fun ω => ?_
            haveI := empirical_isProbabilityMeasure Nat.one_pos ((R 1).X (Real.toNNReal t) ω)
            rw [← ofReal_norm, norm_smul, Real.norm_eq_abs, abs_of_nonneg hσ1]
            refine ENNReal.ofReal_le_ofReal (mul_le_mul_of_nonneg_left ?_ hσ1)
            rw [hc0]
            exact norm_ofMeasureDiff_le a9_gamma_gt _ _
        _ = ENNReal.ofReal (S.sigma 1 * c0) := by simp
        _ ≤ _ := ENNReal.ofReal_le_ofReal (by linarith)
    · have hN2 : 2 ≤ N := by omega
      have hKtot : ∑' j, a9K d Λ₁ t j ≤ Kb := by
        rw [hKb, hZ0]; exact a9K_tsum_le Λ₁ ht
      refine (a9_Z_moment hP hKtr0 hKtr' hS hN2 hfield ht hKtot).trans
        (ENNReal.ofReal_le_ofReal ?_)
      have hN1' : 1 ≤ N := by omega
      have h𝔈 := (hS.energy.pos N hN1').le
      have hσ := a8p_sigma_nonneg S N
      have hle : S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * 𝔈 N) ≤ (1 / 2) * (Cq * cT) * S.T * Bm := by
        have h1 : S.sigma N * ((1 / 2) * (Cq * cT)) * (S.T * 𝔈 N) =
            ((1 / 2) * (Cq * cT) * S.T) * (S.sigma N * 𝔈 N) := by ring
        rw [h1]
        exact mul_le_mul_of_nonneg_left ((hB𝔈 N).trans (le_max_left _ _)) hcc
      have h2 := mul_le_mul_of_nonneg_right
        (add_le_add_right hle (Real.sqrt (2 * S.T) * (d * Ca))) hKb0
      have h3 : 0 ≤ S.sigma 1 * c0 := mul_nonneg hσ1 hc00
      linarith

end HRS.Main.A9
