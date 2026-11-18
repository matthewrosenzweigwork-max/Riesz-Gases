import HRS.MD.EQLZVocab
import HRS.MD.EQLZDet
import HRS.MD.EQLZStat
import HRS.MD.EQLZRev
import HRS.MD.EQLZDl

/-!
# EQ-LZ packet LN, part 2: the stationary grid bound

For a stationary `d1_P`-Markov process `Z` (filtration `ℱ`, Markov property for smooth data, `HasFDD` for `π`) and a smooth
`F`, the discrete Lyons-Zheng lemma (`eqlz_dl_proof`) applied to the grid law `Λ = Law(Z_{a+jδ})_j` gives
`E max_j (F(Z_{a+jδ}) - F(Z_a))² ≤ 18 A + 2(m+1) B`, with `A = m · 2δκ∫|∇F|²dπ`, `B = δκ∫|∇F|²dπ`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal
open HRS HRS.MD.EQLZ HRS.MD.EQLZDet

namespace HRS.MD.EQLZLevelCore

variable {n : ℕ}

theorem lzlc_bdd {g : Torus n → ℝ} (hg : Continuous g) : ∃ C : ℝ, ∀ x, |g x| ≤ C := by
  obtain ⟨C, hC⟩ := (isCompact_univ (X := Torus n)).exists_bound_of_continuousOn hg.continuousOn
  exact ⟨C, fun x => by simpa using hC x (Set.mem_univ x)⟩

theorem lzlc_ev {f : Torus n → ℝ} (hf : Continuous f) {ι : Type*} (j : ι) :
    Measurable (fun z : ι → Torus n => f (z j)) :=
  hf.measurable.comp (measurable_pi_apply j)

theorem lzlc_int_bdd {Ω : Type*} [MeasurableSpace Ω] {P : Measure Ω} [IsFiniteMeasure P] {f : Ω → ℝ}
    (hf : Measurable f) (C : ℝ) (hC : ∀ ω, |f ω| ≤ C) : Integrable f P :=
  Integrable.of_bound hf.aestronglyMeasurable C (ae_of_all _ fun ω => by simpa using hC ω)

theorem lzlc_grid_bound (hn : 1 ≤ n) {κ : ℝ} (hκ : 0 < κ) {U : Torus n → ℝ} (hU : Torus.IsSmooth U)
    (hsm : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus n → ℝ, Torus.IsSmooth φ → Torus.IsSmooth (d1_P hn hκ hU t φ))
    (hsemi : ∀ s t : ℝ, 0 ≤ s → 0 ≤ t → ∀ φ : Torus n → ℝ, Torus.IsSmooth φ →
      d1_P hn hκ hU (s + t) φ = d1_P hn hκ hU s (d1_P hn hκ hU t φ))
    (hsymm : ∀ t : ℝ, 0 ≤ t → ∀ φ ψ : Torus n → ℝ, Torus.IsSmooth φ → Torus.IsSmooth ψ →
      ∫ x, ψ x * d1_P hn hκ hU t φ x ∂(d1_gibbsMeasure κ U) =
        ∫ x, φ x * d1_P hn hκ hU t ψ x ∂(d1_gibbsMeasure κ U))
    (hinv : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus n → ℝ, Torus.IsSmooth φ →
      ∫ x, d1_P hn hκ hU t φ x ∂(d1_gibbsMeasure κ U) = ∫ x, φ x ∂(d1_gibbsMeasure κ U))
    (hen : ∀ t : ℝ, 0 ≤ t → ∀ φ : Torus n → ℝ, Torus.IsSmooth φ →
      ∫ x, φ x * (φ x - d1_P hn hκ hU t φ x) ∂(d1_gibbsMeasure κ U) ≤
          t * (κ * ∫ x, ‖Torus.grad φ x‖ ^ 2 ∂(d1_gibbsMeasure κ U)) ∧
        ∫ x, (φ x - d1_P hn hκ hU t φ x) ^ 2 ∂(d1_gibbsMeasure κ U) ≤
          ∫ x, φ x * (φ x - d1_P hn hκ hU t φ x) ∂(d1_gibbsMeasure κ U))
    (hstat : type_of% @HRS.MD.EQLZStat.eqlz_stat_proof) (hrev : type_of% @HRS.MD.EQLZRev.eqlz_rev_proof)
    (hdl : type_of% @HRS.MD.EQLZDl.eqlz_dl_proof)
    {Ω : Type} [mΩ : MeasurableSpace Ω] (P : Measure Ω) [IsProbabilityMeasure P] (ℱ : Filtration ℝ mΩ)
    (Z : ℝ → Ω → Torus n) (hZℱ : ∀ r, Measurable[ℱ r] (Z r))
    (hmarkov : ∀ φ : Torus n → ℝ, Torus.IsSmooth φ → ∀ s t : ℝ, 0 ≤ s → s ≤ t →
      P[fun ω => φ (Z t ω) | ℱ s] =ᵐ[P] fun ω => d1_P hn hκ hU (t - s) φ (Z s ω))
    (hfdd : HasFDD hn hκ hU P Z (d1_gibbsMeasure κ U))
    {F : Torus n → ℝ} (hF : Torus.IsSmooth F) (a δ : ℝ) (ha : 0 ≤ a) (hδ : 0 ≤ δ) (m : ℕ) :
    ∫⁻ ω, ⨆ j : Fin (m + 1), ENNReal.ofReal ((F (Z (a + (j : ℕ) * δ) ω) - F (Z a ω)) ^ 2) ∂P ≤
      ENNReal.ofReal (18 * ((m : ℝ) * (2 * (δ * (κ * ∫ x, ‖Torus.grad F x‖ ^ 2 ∂(d1_gibbsMeasure κ U))))) +
        2 * ((m : ℝ) + 1) * (δ * (κ * ∫ x, ‖Torus.grad F x‖ ^ 2 ∂(d1_gibbsMeasure κ U)))) := by
  set π := d1_gibbsMeasure κ U with hπ
  set I := ∫ x, ‖Torus.grad F x‖ ^ 2 ∂π with hI
  have hZ : ∀ t, 0 ≤ t → Measurable (Z t) := fun t _ => (hZℱ t).mono (ℱ.le t) le_rfl
  obtain ⟨hmarg, hsq⟩ := hstat hn hκ hU hsm hinv P Z hZ hfdd
  have hFc : Continuous F := lzdet_continuous hF
  have hgs : Torus.IsSmooth (d1_P hn hκ hU δ F) := hsm δ hδ F hF
  set g := d1_P hn hκ hU δ F with hg
  have hgc : Continuous g := lzdet_continuous hgs
  have ht : ∀ j : Fin (m + 1), 0 ≤ a + (j : ℕ) * δ := fun j => by positivity
  set G : Ω → Fin (m + 1) → Torus n := fun ω j => Z (a + (j : ℕ) * δ) ω with hG
  have hGm : Measurable G := measurable_pi_iff.2 fun j => hZ _ (ht j)
  set Λ := P.map G with hΛ
  haveI : IsProbabilityMeasure Λ := show IsProbabilityMeasure (P.map G) from inferInstance
  obtain ⟨CF, hCF⟩ := lzlc_bdd hFc
  obtain ⟨Cg, hCg⟩ := lzlc_bdd hgc
  have hFL2 : ∀ j : Fin (m + 1), MemLp (fun z : Fin (m + 1) → Torus n => F (z j)) 2 Λ := fun j =>
    MemLp.of_bound (lzlc_ev hFc j).aestronglyMeasurable CF
      (ae_of_all _ fun z => by simpa using hCF (z j))
  have hrevΛ : Λ.map (fun z i => z (Fin.rev i)) = Λ :=
    hrev hn hκ hU hsm hsemi hsymm hinv P Z hZ hfdd a δ ha hδ m
  -- the martingale hypothesis
  have hmart : ∀ (k : ℕ) (hk : k < m),
      Λ[fun z => F (z ⟨k + 1, by omega⟩) |
          MeasurableSpace.comap (fun z (i : Fin (k + 1)) => z ⟨i, by omega⟩) inferInstance]
        =ᵐ[Λ] fun z => g (z ⟨k, by omega⟩) := by
    intro k hk
    have hpre : Measurable (fun (z : Fin (m + 1) → Torus n) (i : Fin (k + 1)) => z ⟨i, by omega⟩) :=
      measurable_pi_iff.2 fun i => measurable_pi_apply _
    have hle := hpre.comap_le
    -- measurability of the prefix pulled back to `Ω`
    have hsk : 0 ≤ a + (k : ℝ) * δ := by positivity
    have hpreΩ : Measurable[ℱ (a + (k : ℝ) * δ)]
        (fun ω (i : Fin (k + 1)) => Z (a + ((i : ℕ) : ℝ) * δ) ω) := by
      refine (@measurable_pi_iff Ω (Fin (k + 1)) (fun _ => Torus n) (ℱ (a + (k : ℝ) * δ)) _ _).2 fun i => ?_
      refine (hZℱ _).mono (ℱ.mono ?_) le_rfl
      have : (i : ℕ) ≤ k := Nat.lt_succ_iff.1 i.2
      have : ((i : ℕ) : ℝ) ≤ k := by exact_mod_cast this
      nlinarith
    have hFint : Integrable (fun z : Fin (m + 1) → Torus n => F (z ⟨k + 1, by omega⟩)) Λ :=
      lzlc_int_bdd (lzlc_ev hFc _) CF fun z => hCF _
    refine (ae_eq_condExp_of_forall_setIntegral_eq hle hFint ?_ ?_ ?_).symm
    · intro s _ _
      exact (lzlc_int_bdd (lzlc_ev hgc _) Cg fun z => hCg _).integrableOn
    · intro S hS _
      obtain ⟨B, hB, rfl⟩ := hS
      have hSm : MeasurableSet ((fun (z : Fin (m + 1) → Torus n) (i : Fin (k + 1)) => z ⟨i, by omega⟩) ⁻¹' B) :=
        hpre hB
      have hS' : MeasurableSet[ℱ (a + (k : ℝ) * δ)]
          (G ⁻¹' ((fun (z : Fin (m + 1) → Torus n) (i : Fin (k + 1)) => z ⟨i, by omega⟩) ⁻¹' B)) :=
        hpreΩ hB
      rw [hΛ, setIntegral_map hSm (lzlc_ev hgc ⟨k, by omega⟩).aestronglyMeasurable
          hGm.aemeasurable,
        setIntegral_map hSm (lzlc_ev hFc ⟨k + 1, by omega⟩).aestronglyMeasurable
          hGm.aemeasurable]
      have hmk := hmarkov F hF (a + (k : ℝ) * δ) (a + (((k + 1 : ℕ)) : ℝ) * δ) hsk
        (by push_cast; nlinarith)
      have hdiff : a + (((k + 1 : ℕ)) : ℝ) * δ - (a + (k : ℝ) * δ) = δ := by push_cast; ring
      rw [hdiff] at hmk
      have hint : Integrable (fun ω => F (Z (a + (((k + 1 : ℕ)) : ℝ) * δ) ω)) P :=
        lzlc_int_bdd (hFc.measurable.comp (hZ _ (by positivity))) CF fun ω => hCF _
      have hce := setIntegral_condExp (ℱ.le (a + (k : ℝ) * δ)) hint hS'
      have e1 : ∫ ω in G ⁻¹' ((fun (z : Fin (m + 1) → Torus n) (i : Fin (k + 1)) => z ⟨i, by omega⟩) ⁻¹' B),
            g (G ω ⟨k, by omega⟩) ∂P =
          ∫ ω in G ⁻¹' ((fun (z : Fin (m + 1) → Torus n) (i : Fin (k + 1)) => z ⟨i, by omega⟩) ⁻¹' B),
            (P[fun ω => F (Z (a + (((k + 1 : ℕ)) : ℝ) * δ) ω) | ℱ (a + (k : ℝ) * δ)]) ω ∂P := by
        refine (setIntegral_congr_ae (ℱ.le _ _ hS') ?_)
        filter_upwards [hmk] with ω hω _
        rw [hω]
      rw [e1, hce]
    · exact ((hgc.measurable.comp (measurable_pi_apply (Fin.last k))).comp
        (comap_measurable (fun (z : Fin (m + 1) → Torus n) (i : Fin (k + 1)) => z ⟨i, by omega⟩))).aestronglyMeasurable
  set A : ℝ := (m : ℝ) * (2 * (δ * (κ * I))) with hAdef
  set B : ℝ := δ * (κ * I) with hBdef
  have hA : ∑ k : Fin m, ∫ z, (F (z k.succ) - F (z k.castSucc)) ^ 2 ∂Λ ≤ A := by
    have hterm : ∀ k : Fin m, ∫ z, (F (z k.succ) - F (z k.castSucc)) ^ 2 ∂Λ ≤ 2 * (δ * (κ * I)) := by
      intro k
      have hmeas : Measurable fun z : Fin (m + 1) → Torus n => (F (z k.succ) - F (z k.castSucc)) ^ 2 :=
        ((lzlc_ev hFc k.succ).sub (lzlc_ev hFc k.castSucc)).pow_const 2
      rw [hΛ, integral_map hGm.aemeasurable hmeas.aestronglyMeasurable]
      have hk : a + (((k.succ : Fin (m + 1)) : ℕ) : ℝ) * δ = (a + ((k : ℕ) : ℝ) * δ) + δ := by
        simp [Fin.val_succ]; ring
      have h2 := hsq (a + ((k : ℕ) : ℝ) * δ) δ (by positivity) hδ F hF
      have h3 : ∫ ω, (F (G ω k.succ) - F (G ω k.castSucc)) ^ 2 ∂P =
          ∫ ω, (F (Z ((a + ((k : ℕ) : ℝ) * δ) + δ) ω) - F (Z (a + ((k : ℕ) : ℝ) * δ) ω)) ^ 2 ∂P := by
        simp only [hG, hk]
        simp
      rw [h3, h2]
      have := (hen δ hδ F hF).1
      linarith
    calc ∑ k : Fin m, ∫ z, (F (z k.succ) - F (z k.castSucc)) ^ 2 ∂Λ
        ≤ ∑ k : Fin m, 2 * (δ * (κ * I)) := Finset.sum_le_sum fun k _ => hterm k
      _ = A := by
        simp only [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul]
        exact hAdef.symm
  have hB : ∀ j : Fin (m + 1), ∫ z, (F (z j) - g (z j)) ^ 2 ∂Λ ≤ B := by
    intro j
    have hmeas : Measurable fun z : Fin (m + 1) → Torus n => (F (z j) - g (z j)) ^ 2 :=
      ((lzlc_ev hFc j).sub (lzlc_ev hgc j)).pow_const 2
    rw [hΛ, integral_map hGm.aemeasurable hmeas.aestronglyMeasurable]
    have hm2 : Measurable fun x : Torus n => (F x - g x) ^ 2 :=
      (hFc.measurable.sub hgc.measurable).pow_const 2
    have h3 : ∫ ω, (F (G ω j) - g (G ω j)) ^ 2 ∂P = ∫ x, (F x - g x) ^ 2 ∂(P.map (Z (a + (j : ℕ) * δ))) := by
      rw [integral_map (hZ _ (ht j)).aemeasurable hm2.aestronglyMeasurable]
    rw [h3, hmarg _ (ht j)]
    exact ((hen δ hδ F hF).2).trans (hen δ hδ F hF).1
  have key := hdl (E := Torus n) m Λ F g hFc.measurable hgc.measurable hFL2 hrevΛ hmart A B hA hB
  have hmeasΨ : Measurable fun z : Fin (m + 1) → Torus n =>
      ⨆ j : Fin (m + 1), ENNReal.ofReal ((F (z j) - F (z 0)) ^ 2) :=
    Measurable.iSup fun j => ENNReal.measurable_ofReal.comp
      (((lzlc_ev hFc j).sub (lzlc_ev hFc 0)).pow_const 2)
  have hconv : ∫⁻ ω, ⨆ j : Fin (m + 1), ENNReal.ofReal ((F (Z (a + (j : ℕ) * δ) ω) - F (Z a ω)) ^ 2) ∂P =
      ∫⁻ z, ⨆ j : Fin (m + 1), ENNReal.ofReal ((F (z j) - F (z 0)) ^ 2) ∂Λ := by
    rw [hΛ, lintegral_map hmeasΨ hGm]
    simp [hG]
  rw [hconv]
  exact key

end HRS.MD.EQLZLevelCore

end
