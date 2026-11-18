import HRS.Main.Lattice39D4
import HRS.Main.A9Final

/-!
# Example A.39: proof of the linearisation conclusion (packet `lat39`)

Relocated proof of `perturbedLattice_linearization` from A.9 (`main_torus_field_proof`) and the D4 lemmas
(`HRS/Main/Lattice39D4.lean`).
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators MeasureTheory BoundedContinuousFunction

namespace HRS

namespace Main

variable {d : ℕ}

theorem perturbedLattice_linearization_proof (s : ℝ) :
    ∃ C₀min : ℝ, ∀ (Rg : PDE.Regime) (ν₀ MB Λ T VB Cin C₀ Cc : ℝ), C₀min ≤ C₀ →
    ∀ (a : Torus d → Euc d), Torus.IsSmooth a →
    ∃ ΛT : ℝ, 0 < ΛT ∧
    ∀ (S : MainData d), S.s = s → S.T = T → S.μ0 = volume → (∀ N : ℕ, S.invβ N = 0) →
    (∀ (N M : ℕ) (t : ℝ), S.ρ N t = S.ρ M t) →
    ∀ (R : ∀ N, Realization d N) (𝔈 : ℕ → ℝ) (m₀ : ℕ) (ε εf : ℕ → ℝ)
      (ηF : ∀ N, (R N).Ω → NegSobolev d (gammaIdx d : ℝ))
      (νin : Measure (NegSobolev d (gammaIdx d : ℝ))) (n₁ : ℕ),
    TorusStanding S R Rg ν₀ MB Λ VB (gammaIdx d) C₀ Cc 𝔈 →
    InitialFluctuation S R m₀ Cin ε (fun _ => ∅) →
    (∀ (N : ℕ) (ω : (R N).Ω),
      ηF N ω = NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x)) →
    InitialFluctuationField S R (gammaIdx d) Cin εf ηF νin →
    (∀ n : ℕ, max 2 n₁ ≤ n → ∀ᵐ ω ∂(R (n ^ d)).P,
      (R (n ^ d)).X₀ ω = perturbedLattice n (S.κ (n ^ d)) a) →
    Tendsto (fun n : ℕ => S.κ (n ^ d)) atTop atTop →
    Tendsto (fun n : ℕ => S.κ (n ^ d) / (n : ℝ)) atTop (𝓝 0) →
    Tendsto (fun n : ℕ => S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)) atTop (𝓝 0) →
    (∃ K : ℝ, ∀ n : ℕ, max 2 n₁ ≤ n →
      εf (n ^ d) ≤ K * ((S.κ (n ^ d))⁻¹ +
        S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) ∧
      𝔈 (n ^ d) ≤ K * (((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1))) →
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
          (NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x)))))
  := by
  obtain ⟨C₀min, hA⟩ := main_torus_field_proof (d := d) s
  refine ⟨C₀min, fun Rg ν₀ MB Λ T VB Cin C₀ Cc hC₀ a ha => ?_⟩
  obtain ⟨C, ΛT, hC, hΛT, hA2⟩ := hA Rg ν₀ MB Λ T VB Cin C₀ Cc hC₀
  refine ⟨ΛT, hΛT, fun S hs hT hμ0 hinv hρ R 𝔈 m₀ ε εf ηF νin n₁ hstand hinit hηF hfield
    hlat hκ1 hκ2 hκ3 hdom => ?_⟩
  have hd1 : 1 ≤ d := S.hd
  have hd0 : d ≠ 0 := by omega
  -- the rate bound
  have hrate : ∃ (K' : ℝ) (n₀ : ℕ), ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ n : ℕ, n₀ ≤ n →
      smoothDist 2
        (particleFieldLaw (R (n ^ d)).P (S.sigma (n ^ d)) (gammaIdx d : ℝ) (R (n ^ d)).X (S.ρ (n ^ d)) t)
        (Measure.dirac (transportField (S.dyn (n ^ d)) (S.ρ (n ^ d)) t (gammaIdx d : ℝ) (NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x)))) ≤
      K' * Real.exp (ΛT * t) *
        ((S.κ (n ^ d))⁻¹ + S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) +
          S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)) := by
    obtain ⟨K, hK⟩ := hdom
    refine ⟨C * (2 * max K 0), max (max 2 n₁) ⌈C⌉₊, fun t ht n hn => ?_⟩
    have hn2 : max 2 n₁ ≤ n := le_trans (le_max_left _ _) hn
    have hnC : ⌈C⌉₊ ≤ n := le_trans (le_max_right _ _) hn
    have hn1 : 1 ≤ n := by have := le_max_left 2 n₁; omega
    have hNn : n ≤ n ^ d := Nat.le_self_pow hd0 n
    have hCN : C ≤ ((n ^ d : ℕ) : ℝ) := by
      calc C ≤ (⌈C⌉₊ : ℝ) := Nat.le_ceil C
        _ ≤ (n : ℝ) := by exact_mod_cast hnC
        _ ≤ ((n ^ d : ℕ) : ℝ) := by exact_mod_cast hNn
    have hN1 : 1 ≤ n ^ d := le_trans hn1 hNn
    obtain ⟨hε, h𝔈⟩ := hK n hn2
    have hκpos : 0 < S.κ (n ^ d) := S.hκ _
    have hNpos : (0 : ℝ) < ((n ^ d : ℕ) : ℝ) := by exact_mod_cast hN1
    have hbr1 : 0 ≤ (S.κ (n ^ d))⁻¹ + S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) := by
      positivity
    have hbr2 : 0 ≤ ((S.κ (n ^ d))⁻¹) ^ 2 + ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1) := by positivity
    have hε' : εf (n ^ d) ≤ max K 0 * ((S.κ (n ^ d))⁻¹ +
        S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ))) :=
      hε.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hbr1)
    have h𝔈' : 𝔈 (n ^ d) ≤ max K 0 * (((S.κ (n ^ d))⁻¹) ^ 2 +
        ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)) :=
      h𝔈.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hbr2)
    obtain ⟨hσ, hAN, hq⟩ := lattice39_scales_of_invβ_zero_proof S (n ^ d) (hinv _)
    have hnoise : IsLinearFieldNoise (S.dyn (n ^ d)) (S.ρ (n ^ d)) (S.qN (n ^ d)) t (gammaIdx d : ℝ)
        (Measure.dirac (0 : NegSobolev d (gammaIdx d : ℝ))) := by
      rw [hq]; exact lattice39_dirac_isLinearFieldNoise_proof _ _ _ _
    have hmain := (hA2 S hs hT R 𝔈 hstand m₀ ε hinit εf ηF νin hfield t ht).1 (n ^ d) hCN _ hnoise
    rw [lattice39_linearFieldLaw_dirac_proof _ _ _ _ _ _ (NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x)) (ηF (n ^ d)) (fun ω => hηF _ ω),
      hAN, one_smul] at hmain
    have hfr := lattice39_fieldRate_le_proof s (S.κ (n ^ d)) (max K 0) (εf (n ^ d)) (𝔈 (n ^ d))
      (n ^ d) hκpos (le_max_right _ _) hN1 hε' h𝔈'
    have hfr' : fieldRate d (εf (n ^ d)) (S.qN (n ^ d)) (S.sigma (n ^ d)) (𝔈 (n ^ d)) (n ^ d) ≤
        2 * max K 0 * ((S.κ (n ^ d))⁻¹ +
          S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) +
          S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)) := by
      rw [hq, hσ]; exact hfr
    have hexp : 0 ≤ Real.exp (ΛT * t) := (Real.exp_pos _).le
    calc _ ≤ C * Real.exp (ΛT * t) * fieldRate d (εf (n ^ d)) (S.qN (n ^ d)) (S.sigma (n ^ d)) (𝔈 (n ^ d)) (n ^ d) :=
          hmain
      _ ≤ C * Real.exp (ΛT * t) * (2 * max K 0 * ((S.κ (n ^ d))⁻¹ +
          S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)) +
          S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1))) :=
          mul_le_mul_of_nonneg_left hfr' (by positivity)
      _ = _ := by ring
  refine ⟨hrate, fun t ht => ?_⟩
  obtain ⟨K', n₀, hK'⟩ := hrate
  -- the rate tends to zero
  have hr0 : Tendsto (fun n : ℕ => (S.κ (n ^ d))⁻¹ + S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^
      (-(2 : ℝ) / (d : ℝ)) + S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (s / (d : ℝ) - 1)) atTop (𝓝 0) := by
    have h1 : Tendsto (fun n : ℕ => (S.κ (n ^ d))⁻¹) atTop (𝓝 0) :=
      tendsto_inv_atTop_zero.comp hκ1
    have h2 : Tendsto (fun n : ℕ => S.κ (n ^ d) * ((n ^ d : ℕ) : ℝ) ^ (-(2 : ℝ) / (d : ℝ)))
        atTop (𝓝 0) := by
      refine squeeze_zero' ?_ ?_ hκ2
      · exact Eventually.of_forall fun n => by have := S.hκ (n ^ d); positivity
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
        exact mul_le_mul_of_nonneg_left hle (S.hκ _).le
    have := (h1.add h2).add hκ3
    simpa using this
  have hdyn : ∀ N : ℕ, S.dyn N = S.dyn 1 := fun N => by
    simp only [MainData.dyn, hinv N, hinv 1]
  have hρ' : ∀ N : ℕ, S.ρ N = S.ρ 1 := fun N => funext (hρ N 1)
  have hd0' : Tendsto (fun n : ℕ => smoothDist 2
      (particleFieldLaw (R ((n + n₀) ^ d)).P (S.sigma ((n + n₀) ^ d)) (gammaIdx d : ℝ) (R ((n + n₀) ^ d)).X
        (S.ρ ((n + n₀) ^ d)) t)
      (Measure.dirac (transportField (S.dyn 1) (S.ρ 1) t (gammaIdx d : ℝ) (NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x))))) atTop (𝓝 0) := by
    have hr := (hr0.comp (tendsto_add_atTop_nat n₀)).const_mul (K' * Real.exp (ΛT * t))
    rw [mul_zero] at hr
    refine squeeze_zero (fun n => smoothDist_nonneg 2 _ _) (fun n => ?_) hr
    have := hK' t ht (n + n₀) (by omega)
    have heq : transportField (S.dyn ((n + n₀) ^ d)) (S.ρ ((n + n₀) ^ d)) t (gammaIdx d : ℝ)
        (NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x)) =
        transportField (S.dyn 1) (S.ρ 1) t (gammaIdx d : ℝ)
        (NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x)) := by rw [hdyn, hρ']
    rw [heq] at this
    simpa [mul_assoc] using this
  have hpp : ∀ n : ℕ, IsProbabilityMeasure
      (particleFieldLaw (R ((n + n₀) ^ d)).P (S.sigma ((n + n₀) ^ d)) (gammaIdx d : ℝ) (R ((n + n₀) ^ d)).X
        (S.ρ ((n + n₀) ^ d)) t) := fun n => A9.a9_particle_prob (gammaIdx d : ℝ) t
  have key := A9.a9_weak_of_dc2
    (fun n : ℕ => particleFieldLaw (R ((n + n₀) ^ d)).P (S.sigma ((n + n₀) ^ d)) (gammaIdx d : ℝ)
      (R ((n + n₀) ^ d)).X (S.ρ ((n + n₀) ^ d)) t)
    (fun _ : ℕ => Measure.dirac (transportField (S.dyn 1) (S.ρ 1) t (gammaIdx d : ℝ) (NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x))))
    (Measure.dirac (transportField (S.dyn 1) (S.ρ 1) t (gammaIdx d : ℝ) (NegSobolev.ofFun (gammaIdx d : ℝ) (fun x => -Torus.div a x))))
    (fun f => tendsto_const_nhds) hd0'
  exact (A9.a9_conv_shift (μ := fun n : ℕ => particleFieldLaw (R (n ^ d)).P (S.sigma (n ^ d)) (gammaIdx d : ℝ)
    (R (n ^ d)).X (S.ρ (n ^ d)) t) n₀).2 key

example := (@perturbedLattice_linearization_proof : type_of% @perturbedLattice_linearization)

end Main

end HRS
