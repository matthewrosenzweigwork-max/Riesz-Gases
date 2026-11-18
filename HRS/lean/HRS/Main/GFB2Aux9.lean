import HRS.Main.GFB2Aux8

/-!
# Packet GFB2, part 9: the pointwise commutator estimate for the remainder (`gf_remainder_pointwise`)
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.GF

open HRS.Uniform

variable {d : ℕ}

theorem gfb2_memSobolev_mono {γ m : ℝ} (hγm : γ ≤ m) {ψ : Torus d → ℝ} (h : MemSobolev m ψ) :
    MemSobolev γ ψ := by
  refine ⟨h.1, ?_⟩
  refine Summable.of_nonneg_of_le (fun k => mul_nonneg (Real.rpow_nonneg (Torus.jp_pos _).le _) (sq_nonneg _))
    (fun k => ?_) h.2
  exact mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one _) (by linarith))
    (sq_nonneg _)

theorem gfb2_sobolevNorm_mono {γ m : ℝ} (hγm : γ ≤ m) {ψ : Torus d → ℝ} (h : MemSobolev m ψ) :
    sobolevNorm γ ψ ≤ sobolevNorm m ψ := by
  unfold sobolevNorm
  refine Real.sqrt_le_sqrt (add_le_add le_rfl ?_)
  exact (gfb2_memSobolev_mono hγm h).2.tsum_le_tsum (fun k =>
    mul_le_mul_of_nonneg_right (Real.rpow_le_rpow_of_exponent_le (Torus.jp_ge_one _) (by linarith))
      (sq_nonneg _)) h.2

theorem gfb2_propagator_isCk (D : DynData d) (ρ : ℝ → Torus d → ℝ) {r t : ℝ} (hr : 0 ≤ r) (hrt : r ≤ t)
    (φ : Torus d → ℝ) : Torus.IsCk 2 (propagator D ρ r t φ) := by
  unfold propagator
  by_cases h : ∃ f, IsClassicalAdjointSolution D ρ t φ f
  · rw [dif_pos h]
    exact h.choose_spec.c2 r ⟨hr, hrt⟩
  · rw [dif_neg h]
    exact Q54c.isCk2_const 0


theorem gf_remainder_pointwise_proof (b : GeneralBounds d) (M : Matrix (Fin d) (Fin d) ℝ) (K : ℝ) :
    ∃ C₀min : ℝ, ∀ C₀ : ℝ, C₀min ≤ C₀ → ∃ C : ℝ, 0 < C ∧
      ∀ S : GeneralSetup d, S.Within { b with C₀ := C₀ } → S.MFHypM M → ∀ N : ℕ, 2 ≤ N →
      ∀ m : ℝ, (S.γ : ℝ) ≤ m →
      ∀ r t : ℝ, 0 ≤ r → r ≤ t → t ≤ S.T → ∀ φ : Torus d → ℝ, Torus.IsCk 2 φ → MemSobolev m φ →
        MemSobolev m (propagator (S.dynM M N) (S.ρ N) r t φ) →
        sobolevNorm m (propagator (S.dynM M N) (S.ρ N) r t φ) ≤ K * sobolevNorm m φ →
      ∀ X : Config d N, X ∉ collisionSet d N →
        |flucInteraction (S.dynM M N) (propagator (S.dynM M N) (S.ρ N) r t φ) X (S.ρ N r)| ≤
          C * sobolevNorm m φ * S.energyCompletion N X r := by
  classical
  by_cases hex : ∃ S₀ : GeneralSetup d, S₀.s = b.s ∧ S₀.γ = b.γ
  · obtain ⟨S₀, hs₀, hγ₀⟩ := hex
    have hd1 : 1 ≤ d := by have := S₀.hd; omega
    have hs0 : 0 ≤ b.s := hs₀ ▸ S₀.hs0
    have hsd : b.s < d := hs₀ ▸ S₀.hsd
    have hγN : 2 * d + 10 < b.γ := hγ₀ ▸ S₀.hγ
    have hγ : (2 * d + 10 : ℝ) < (b.γ : ℝ) := by exact_mod_cast hγN
    obtain ⟨C₀', Cc, hC₀', hCc, hcomm⟩ := HRS.Commutator.commutator_estimate_of_packets hd1 hs0 hsd
    set Λ' : ℝ := max b.Λ 1 with hΛ'
    have hΛ'1 : 1 ≤ Λ' := le_max_right _ _
    obtain ⟨-, C₀m, hC₀m, hm⟩ := oNΛ_le_oN hd1 hs0 hsd C₀' hC₀' Λ' hΛ'1
    obtain ⟨cT, hcT0, hcT⟩ := gfb2_transport_bound hγ M b.s
    refine ⟨C₀m, fun C₀ hC₀ => ⟨1 / 2 * Cc * cT * max K 0 + 1, by positivity, ?_⟩⟩
    intro S hS hMF N hN m hmγ r t hr hrt htT φ hφCk hφMem hψMem hψnorm X hX
    unfold GeneralSetup.Within at hS
    obtain ⟨hs, hT, hγ', hΛ, hβ, hC0, hV⟩ := hS
    have hC0' : S.C₀ = C₀ := hC0
    obtain ⟨hMFN, hReg⟩ := hMF N
    set ψ := propagator (S.dynM M N) (S.ρ N) r t φ with hψ
    have hψCk : Torus.IsCk 2 ψ := gfb2_propagator_isCk _ _ hr hrt φ
    have hmγ' : (b.γ : ℝ) ≤ m := by rw [← hγ']; exact hmγ
    have hψγ : MemSobolev (b.γ : ℝ) ψ := gfb2_memSobolev_mono hmγ' hψMem
    have hTB := hcT ψ hψCk hψγ
    have hrT : r ∈ Set.Icc (0 : ℝ) S.T := ⟨hr, hrt.trans htT⟩
    have hup : ∀ y, S.ρ N r y ≤ Λ' := fun y =>
      ((le_abs_self _).trans ((gfb2_sup_le_cbNorm (hReg r hrT).1 y).trans ((hReg r hrT).2.trans
        (by rw [hΛ]; exact le_max_left _ _))))
    obtain ⟨hOff, hcb⟩ := hcomm Λ' hΛ'1 N hN (S.ρ N r) (hMFN.density r hrT) hup X hX
      (gfb2_v M ψ) _ hTB
    have hflu := gfb2_flucInteraction_eq (S.dynM M N) hψCk X (S.ρ N r) (by
      intro i
      have := hOff.1 i
      simpa [GeneralSetup.dynM, hs] using this)
    have hcb' : |commQuantity d (S.dynM M N).s (gfb2_v M ψ) X (withDensityReal (S.ρ N r))| ≤
        Cc * (cT * sobolevNorm (b.γ : ℝ) ψ) * (rieszEnergy d S.s X (withDensityReal (S.ρ N r)) +
          oNΛ d S.s C₀' Λ' N) := by
      simpa [GeneralSetup.dynM, hs] using hcb
    have hE0 := S.energy_nonneg N hN r hrT X hX
    have hEdef : S.energyCompletion N X r =
        rieszEnergy d S.s X (withDensityReal (S.ρ N r)) + oN d S.s C₀ N := by
      unfold GeneralSetup.energyCompletion; rw [hC0']
    have hoN : oNΛ d S.s C₀' Λ' N ≤ oN d S.s C₀ N := by
      rw [hs]
      exact (hm N hN).trans (Uniform.Q12.q12_oN_mono hC₀ N)
    have hEne : 0 ≤ S.energyCompletion N X r := by
      rw [hEdef]
      unfold GeneralSetup.energyCompletion at hE0
      rw [hC0'] at hE0
      exact hE0
    have hsobm := gfb2_sobolevNorm_mono hmγ' hψMem
    have hsob0 : 0 ≤ sobolevNorm m φ := Real.sqrt_nonneg _
    have hsobψ0 : 0 ≤ sobolevNorm (b.γ : ℝ) ψ := Real.sqrt_nonneg _
    have hKb : sobolevNorm (b.γ : ℝ) ψ ≤ max K 0 * sobolevNorm m φ :=
      hsobm.trans (hψnorm.trans (mul_le_mul_of_nonneg_right (le_max_left _ _) hsob0))
    -- assemble
    rw [hflu, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have h1 : Cc * (cT * sobolevNorm (b.γ : ℝ) ψ) * (rieszEnergy d S.s X (withDensityReal (S.ρ N r)) +
          oNΛ d S.s C₀' Λ' N) ≤ Cc * (cT * (max K 0 * sobolevNorm m φ)) * S.energyCompletion N X r := by
      rw [hEdef]
      have hK'0 : 0 ≤ Cc * (cT * sobolevNorm (b.γ : ℝ) ψ) := by positivity
      calc Cc * (cT * sobolevNorm (b.γ : ℝ) ψ) * (rieszEnergy d S.s X (withDensityReal (S.ρ N r)) +
            oNΛ d S.s C₀' Λ' N)
          ≤ Cc * (cT * sobolevNorm (b.γ : ℝ) ψ) * (rieszEnergy d S.s X (withDensityReal (S.ρ N r)) +
            oN d S.s C₀ N) := mul_le_mul_of_nonneg_left (by linarith) hK'0
        _ ≤ Cc * (cT * (max K 0 * sobolevNorm m φ)) * (rieszEnergy d S.s X (withDensityReal (S.ρ N r)) +
            oN d S.s C₀ N) := by
          refine mul_le_mul_of_nonneg_right ?_ (by rw [← hEdef]; exact hEne)
          exact mul_le_mul_of_nonneg_left (mul_le_mul_of_nonneg_left hKb hcT0) hCc.le
    have h2 : 1 / 2 * |commQuantity d (S.dynM M N).s (gfb2_v M ψ) X (withDensityReal (S.ρ N r))| ≤
        1 / 2 * (Cc * (cT * (max K 0 * sobolevNorm m φ)) * S.energyCompletion N X r) :=
      mul_le_mul_of_nonneg_left (hcb'.trans h1) (by norm_num)
    refine h2.trans ?_
    have hP : 0 ≤ sobolevNorm m φ * S.energyCompletion N X r := mul_nonneg hsob0 hEne
    nlinarith [hP, mul_nonneg (mul_nonneg hCc.le hcT0) (le_max_right K 0 |> fun h => le_trans (le_refl 0) (le_max_right K 0)), hCc, hcT0]
  · refine ⟨0, fun C₀ _ => ⟨1, one_pos, ?_⟩⟩
    intro S hS
    exact absurd ⟨S, hS.1, hS.2.2.1⟩ hex

example := (@gf_remainder_pointwise_proof : type_of% @HRS.GF.gf_remainder_pointwise)

end HRS.GF
