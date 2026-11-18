import HRS.MC.S7PIG1Int
import HRS.MC.S7PICMain
import HRS.MC.S7PIDefs

/-!
# Packet piG, part G2: `s7_PIG_J_measure` (the cumulative covariance path `s ↦ 𝒥_η((0,s])`)

`Jc s :=` the tensor of PI-D (`s7_PI_D_J_exists_assembly_proof`) for `(0,s]`; `Jc b - Jc a` is an `IsJValue`-tensor of `(a,b]`
by additivity of the set integral (the integrand is integrable, `S7PIG1_integrand_integrable`); `jPair` is `h.choose`,
and `h.choose = Jc b - Jc a` by PI-C (`s7_PI_C_J_unique_proof`).
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.Sec7.S7PIG1

open HRS HRS.Sec7 HRS.MC.Sec7 HRS.MC.Sec7.PI

set_option maxSynthPendingDepth 3

variable {d : ℕ}

/-- additivity of `IsJValue` over adjacent intervals starting at `0` -/
theorem S7PIG1_isJValue_sub (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T)
    (zr : ℝ → NegSobolev d (2 * (d : ℝ) + 6)) (hzr : Measurable zr) (M : ℝ)
    (hM : ∀ u ∈ Set.Icc (0 : ℝ) T, ‖zr u‖ ≤ M) (Jc : ℝ → TensorDual (PathSpace d m T) 2)
    (hJ : ∀ s : ℝ, 0 ≤ s → s ≤ T → IsJValue R.D R.ρ m T
      (fun u => NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k)) (Set.Ioc 0 s) (Jc s))
    (a b : ℝ) (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T) :
    IsJValue R.D R.ρ m T (fun u => NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k))
      (Set.Ioc a b) (Jc b - Jc a) := by
  obtain ⟨hmb, hevb⟩ := hJ b (ha.trans hab) hb
  obtain ⟨hma, heva⟩ := hJ a ha (hab.trans hb)
  have hsub : Jc b - Jc a ∈ projTensor (PathSpace d m T) 2 := Submodule.sub_mem _ hmb hma
  refine ⟨hsub, ?_⟩
  intro ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂
  rw [sub_apply, hevb ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂,
    heva ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
  have hint := S7PIG1_integrand_integrable R (2 * (d : ℝ) + 6) rfl m hm T hT zr hzr M hM ta tb hta htb φa φb
    hφa hφb
  set f : ℝ → ℝ := fun u => NegSobolev.eval
    (NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k) : NegSobolev d m)
    (fun x => inner ℝ (Torus.grad (propagator R.D R.ρ u ta φa) x)
      (Torus.grad (propagator R.D R.ρ u tb φb) x)) with hf
  set K : Set ℝ := Set.Icc 0 (min ta tb) with hK
  have hKm : MeasurableSet K := measurableSet_Icc
  have h1 : IntegrableOn f (Set.Ioc 0 a ∩ K) :=
    hint.mono_set (Set.inter_subset_inter_left _ (Set.Ioc_subset_Ioc_right (hab.trans hb)))
  have h2 : IntegrableOn f (Set.Ioc a b ∩ K) :=
    hint.mono_set (Set.inter_subset_inter_left _ (Set.Ioc_subset_Ioc ha hb))
  have hu : Set.Ioc 0 b ∩ K = (Set.Ioc 0 a ∩ K) ∪ (Set.Ioc a b ∩ K) := by
    rw [← Set.union_inter_distrib_right, Set.Ioc_union_Ioc_eq_Ioc ha hab]
  have hd : Disjoint (Set.Ioc 0 a ∩ K) (Set.Ioc a b ∩ K) := by
    refine Set.disjoint_left.2 fun x hx hx' => ?_
    exact absurd hx.1.2 (not_le.2 hx'.1.1)
  rw [hu, setIntegral_union hd (measurableSet_Ioc.inter hKm) h1 h2]
  ring

theorem s7_PIG_J_measure_proof (R : Regime d) (m : ℝ) (hm : 3 * (d : ℝ) + 8 < m) (T : ℝ) (hT : 0 < T) :
    ∃ C : ℝ, ∀ (zr : ℝ → NegSobolev d (2 * (d : ℝ) + 6)), Measurable zr → ∀ M : ℝ,
      (∀ u ∈ Set.Icc (0 : ℝ) T, ‖zr u‖ ≤ M) →
      ∃ Jc : ℝ → TensorDual (PathSpace d m T) 2, Jc 0 = 0 ∧
        (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T →
          IsJValue R.D R.ρ m T (fun u => NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k))
            (Set.Ioc a b) (Jc b - Jc a) ∧ ‖Jc b - Jc a‖ ≤ C * M * (b - a) ∧
          ∀ M' : PathSpace d m T [×2]→L[ℝ] ℝ,
            jPair R.D R.ρ m T (fun u => NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k))
              (Set.Ioc a b) M' = (Jc b - Jc a) M') := by
  classical
  obtain ⟨C, hC⟩ := HRS.MC.Sec7.S7PIDS.s7_PI_D_J_exists_assembly_proof R (2 * (d : ℝ) + 6) rfl m hm T hT
  refine ⟨C, fun zr hzr M hM => ?_⟩
  have hex : ∀ s : ℝ, ∃ J : TensorDual (PathSpace d m T) 2, 0 ≤ s → s ≤ T →
      IsJValue R.D R.ρ m T (fun u => NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k))
        (Set.Ioc 0 s) J ∧ ‖J‖ ≤ C * M * (s - 0) := by
    intro s
    by_cases hs : 0 ≤ s ∧ s ≤ T
    · obtain ⟨J, hJ1, hJ2⟩ := hC zr hzr M hM 0 s le_rfl hs.1 hs.2
      exact ⟨J, fun _ _ => ⟨hJ1, hJ2⟩⟩
    · exact ⟨0, fun h1 h2 => absurd ⟨h1, h2⟩ hs⟩
  choose Jc hJc using hex
  have hJ : ∀ s : ℝ, 0 ≤ s → s ≤ T →
      IsJValue R.D R.ρ m T (fun u => NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k))
        (Set.Ioc 0 s) (Jc s) := fun s h1 h2 => (hJc s h1 h2).1
  refine ⟨Jc, ?_, fun a b ha hab hb => ?_⟩
  · have h := (hJc 0 le_rfl hT.le).2
    rw [sub_self, mul_zero] at h
    exact norm_le_zero_iff.1 h
  · have hIs := S7PIG1_isJValue_sub R m hm T hT zr hzr M hM Jc hJ a b ha hab hb
    obtain ⟨J', hJ'1, hJ'2⟩ := hC zr hzr M hM a b ha hab hb
    have hEq : J' = Jc b - Jc a :=
      HRS.MC.Sec7.S7PIC.s7_PI_C_J_unique_proof R m T _ _ _ _ hJ'1 hIs
    refine ⟨hIs, hEq ▸ hJ'2, fun M' => ?_⟩
    have hex' : ∃ J, IsJValue R.D R.ρ m T
        (fun u => NegSobolev.ofSeq m (fun k => NegSobolev.fourierCoeff (zr u) k)) (Set.Ioc a b) J := ⟨_, hIs⟩
    unfold jPair
    rw [dif_pos hex']
    have := HRS.MC.Sec7.S7PIC.s7_PI_C_J_unique_proof R m T _ _ _ _ hex'.choose_spec hIs
    rw [this]

end HRS.MC.Sec7.S7PIG1

end
