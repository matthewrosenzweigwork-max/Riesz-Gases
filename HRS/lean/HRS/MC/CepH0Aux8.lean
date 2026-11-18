import HRS.MC.CepH0Aux2
import HRS.MC.CepH0Aux7
import HRS.MC.CepH0Aux1

/-!
# Packet CEPH0, auxiliary 8: additivity of the Fisher information over disjoint open components
-/

open MeasureTheory Filter Topology
open scoped ENNReal NNReal

noncomputable section

namespace HRS.MC.CepH0

open HRS

variable {d N : ℕ}

theorem h0_ofReal_sum_le {ι : Type*} (s : Finset ι) (x : ι → ℝ) :
    ENNReal.ofReal (∑ c ∈ s, x c) ≤ ∑ c ∈ s, ENNReal.ofReal (x c) := by
  classical
  induction s using Finset.induction_on with
  | empty => simp
  | insert a s ha ih =>
    rw [Finset.sum_insert ha, Finset.sum_insert ha]
    exact (ENNReal.ofReal_add_le).trans (add_le_add_right ih _)

theorem h0_testField_zero : IsFisherTestField (d := d) (N := N) (fun _ => (0 : Fin N → Euc d)) :=
  ⟨contDiff_const, ∅, isCompact_empty, Set.empty_disjoint _, fun _ _ => rfl⟩

theorem h0F_zero (D : DynData d) : h0F (N := N) D (fun _ => (0 : Fin N → Euc d)) = fun _ => 0 := by
  funext X
  simp [h0F, configDiv]

abbrev H0A (d N : ℕ) := {ζ : Config d N → (Fin N → Euc d) // IsFisherTestField ζ}

theorem h0_pick (D : DynData d) (ν : Measure (Config d N)) [IsFiniteMeasure ν]
    (a : H0A d N) :
    ∃ b : H0A d N,
      Integrable (h0F D b.1) ν ∧ 0 ≤ ∫ X, h0F D b.1 X ∂ν ∧
        ENNReal.ofReal (∫ X, h0F D a.1 X ∂ν) = ENNReal.ofReal (∫ X, h0F D b.1 X ∂ν) := by
  by_cases h : Integrable (h0F D a.1) ν ∧ 0 ≤ ∫ X, h0F D a.1 X ∂ν
  · exact ⟨a, h.1, h.2, rfl⟩
  · refine ⟨⟨_, h0_testField_zero⟩, ?_, ?_, ?_⟩
    · simp only [h0F_zero]; exact integrable_zero _ _ _
    · simp [h0F_zero]
    · simp only [h0F_zero, integral_zero]
      by_cases hi : Integrable (h0F D a.1) ν
      · have : ∫ X, h0F D a.1 X ∂ν < 0 := by
          by_contra hn
          exact h ⟨hi, not_lt.mp hn⟩
        simp [ENNReal.ofReal_of_nonpos this.le]
      · simp [integral_undef hi]

theorem h0_fisher_mix_le {ι : Type*} [Fintype ι] (D : DynData d) (ν : ι → Measure (Config d N))
    [∀ c, IsProbabilityMeasure (ν c)] (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) :
    fisherInfo D N (h0mix p ν) ≤ ∑ c, ENNReal.ofReal (p c) * fisherInfo D N (ν c) := by
  rw [h0_fisherInfo_eq]
  refine iSup₂_le fun ζ hζ => ?_
  by_cases hI : Integrable (h0F D ζ) (h0mix p ν)
  · have hpiece : ∀ c, Integrable (h0F D ζ) (ENNReal.ofReal (p c) • ν c) :=
      fun c => hI.mono_measure (h0_smul_le_mix p ν c)
    have e : ∫ X, h0F D ζ X ∂(h0mix p ν) =
        ∑ c, ∫ X, h0F D ζ X ∂(ENNReal.ofReal (p c) • ν c) :=
      integral_finset_sum_measure (fun c _ => hpiece c)
    simp_rw [integral_smul_measure, ENNReal.toReal_ofReal (hp0 _), smul_eq_mul] at e
    rw [e]
    refine (h0_ofReal_sum_le _ _).trans (Finset.sum_le_sum fun c _ => ?_)
    rw [ENNReal.ofReal_mul (hp0 c)]
    refine mul_le_mul_right ?_ _
    rw [h0_fisherInfo_eq]
    exact le_iSup₂ (f := fun (ζ : Config d N → (Fin N → Euc d)) (_ : IsFisherTestField ζ) =>
      ENNReal.ofReal (∫ X, h0F D ζ X ∂(ν c))) ζ hζ
  · rw [integral_undef hI]; simp

theorem h0_fisher_mix_ge {ι : Type*} [Fintype ι] (D : DynData d) (C : ι → Set (Config d N))
    (hCo : ∀ c, IsOpen (C c)) (hCd : Pairwise fun c c' => Disjoint (C c) (C c'))
    (hCc : (⋃ c, C c) = (collisionSet d N)ᶜ)
    (ν : ι → Measure (Config d N)) [∀ c, IsProbabilityMeasure (ν c)]
    (hν : ∀ c, ν c (C c)ᶜ = 0) (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    ∑ c, ENNReal.ofReal (p c) * fisherInfo D N (ν c) ≤ fisherInfo D N (h0mix p ν) := by
  classical
  haveI : Nonempty (H0A d N) := ⟨⟨_, h0_testField_zero⟩⟩
  have hfc : ∀ c, fisherInfo D N (ν c) = ⨆ ζ : H0A d N, ENNReal.ofReal (∫ X, h0F D ζ.1 X ∂(ν c)) := by
    intro c
    rw [h0_fisherInfo_eq, iSup_subtype']
  calc ∑ c, ENNReal.ofReal (p c) * fisherInfo D N (ν c)
      = ∑ c, ⨆ ζ : H0A d N, ENNReal.ofReal (p c) * ENNReal.ofReal (∫ X, h0F D ζ.1 X ∂(ν c)) := by
        refine Finset.sum_congr rfl fun c _ => ?_
        rw [hfc c, ENNReal.mul_iSup]
    _ ≤ ⨆ a : ι → H0A d N, ∑ c, ENNReal.ofReal (p c) * ENNReal.ofReal (∫ X, h0F D (a c).1 X ∂(ν c)) :=
        h0_sum_iSup_le (A := fun _ : ι => H0A d N) Finset.univ (fun c (ζ : H0A d N) =>
          ENNReal.ofReal (p c) * ENNReal.ofReal (∫ X, h0F D ζ.1 X ∂(ν c)))
    _ ≤ fisherInfo D N (h0mix p ν) := by
        refine iSup_le fun a => ?_
        choose b hbint hbnn hbeq using fun c => h0_pick D (ν c) (a c)
        obtain ⟨hgl, hgeq⟩ := h0_glue C hCo hCd hCc (fun c => (b c).1) (fun c => (b c).2)
        set ζ : Config d N → (Fin N → Euc d) := fun X => ∑ c, (C c).indicator (b c).1 X with hζdef
        have hae : ∀ c, ∀ᵐ X ∂(ν c), h0F D ζ X = h0F D (b c).1 X := by
          intro c
          have : ∀ᵐ X ∂(ν c), X ∈ C c := by
            rw [ae_iff]; exact hν c
          filter_upwards [this] with X hX
          exact h0F_congr_of_eq_on D (hCo c) (fun Y hY => hgeq c Y hY) hX
        have hint : ∀ c, Integrable (h0F D ζ) (ν c) := fun c => (hbint c).congr (Filter.EventuallyEq.symm (hae c))
        have hpiece : ∀ c, Integrable (h0F D ζ) (ENNReal.ofReal (p c) • ν c) :=
          fun c => (hint c).smul_measure ENNReal.ofReal_ne_top
        have e : ∫ X, h0F D ζ X ∂(h0mix p ν) =
            ∑ c, ∫ X, h0F D ζ X ∂(ENNReal.ofReal (p c) • ν c) :=
          integral_finset_sum_measure (fun c _ => hpiece c)
        simp_rw [integral_smul_measure, ENNReal.toReal_ofReal (hp0 _), smul_eq_mul] at e
        have e2 : ∀ c, ∫ X, h0F D ζ X ∂(ν c) = ∫ X, h0F D (b c).1 X ∂(ν c) :=
          fun c => integral_congr_ae (hae c)
        simp_rw [e2] at e
        calc ∑ c, ENNReal.ofReal (p c) * ENNReal.ofReal (∫ X, h0F D (a c).1 X ∂(ν c))
            = ∑ c, ENNReal.ofReal (p c * ∫ X, h0F D (b c).1 X ∂(ν c)) := by
              refine Finset.sum_congr rfl fun c _ => ?_
              rw [hbeq c, ENNReal.ofReal_mul (hp0 c)]
          _ = ENNReal.ofReal (∫ X, h0F D ζ X ∂(h0mix p ν)) := by
              rw [e, ENNReal.ofReal_sum_of_nonneg (fun c _ => mul_nonneg (hp0 c) (hbnn c))]
          _ ≤ _ := by
              rw [h0_fisherInfo_eq]
              exact le_iSup₂ (f := fun (ζ : Config d N → (Fin N → Euc d)) (_ : IsFisherTestField ζ) =>
                ENNReal.ofReal (∫ X, h0F D ζ X ∂(h0mix p ν))) ζ hgl

theorem h0_fisher_mix {ι : Type*} [Fintype ι] (D : DynData d) (C : ι → Set (Config d N))
    (hCo : ∀ c, IsOpen (C c)) (hCd : Pairwise fun c c' => Disjoint (C c) (C c'))
    (hCc : (⋃ c, C c) = (collisionSet d N)ᶜ)
    (ν : ι → Measure (Config d N)) [∀ c, IsProbabilityMeasure (ν c)]
    (hν : ∀ c, ν c (C c)ᶜ = 0) (p : ι → ℝ) (hp0 : ∀ c, 0 ≤ p c) (hp1 : ∑ c, p c = 1) :
    fisherInfo D N (h0mix p ν) = ∑ c, ENNReal.ofReal (p c) * fisherInfo D N (ν c) :=
  le_antisymm (h0_fisher_mix_le D ν p hp0) (h0_fisher_mix_ge D C hCo hCd hCc ν hν p hp0 hp1)

end HRS.MC.CepH0
