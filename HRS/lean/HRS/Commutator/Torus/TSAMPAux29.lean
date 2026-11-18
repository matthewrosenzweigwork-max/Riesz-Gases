import HRS.Commutator.Torus.TSAMPAux28

/-!
# T-SAMP helpers, part 29: `vhi_cell_sampling_T`
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators FourierTransform

namespace HRS.Commutator.TorusNote

open HRS

variable {d : ℕ}

lemma tsamp_Pgt_ae_conv (hd : 1 ≤ d) {α : ℝ} {η : ℝ} (hη : 0 < η) (hη1 : η ≤ 1)
    {Kα : Torus d → ℝ} (hKαi : Integrable Kα)
    (hKαc : ∀ k : Lattice d, Torus.fcoef Kα k = ((if k = 0 then 0 else
      (1 - Whole.chi (η • Lattice.toEuc k)) * (2 * Real.pi * Lattice.enorm k) ^ (-α) : ℝ) : ℂ))
    {v : Torus d → Euc d} {L : ℝ} (hL : 0 ≤ L) (hLip : IsLipschitzVF L v)
    {w' : Torus d → Euc d} (hwi : ∀ i, Integrable fun x => w' x i) (hrep' : IsFracDeriv α v w')
    (i : Fin d) :
    (fun x => PgtT η v x i) =ᵐ[volume] tsampConv Kα (fun x => w' x i) := by
  have hA : Integrable (tsampConv Kα (fun x => w' x i)) := by
    rw [tsamp_conv_real]; exact text_integrable_conv hKαi (hwi i)
  have hPgtc : Continuous (PgtT η v) := by
    obtain ⟨C, hC, hb⟩ := tsamp_vhi_bounded_core (d := d) hd
    exact (hb η hη hη1 v L hL hLip).1
  have hPi : Integrable (fun x => PgtT η v x i) :=
    ((EuclideanSpace.proj i : Euc d →L[ℝ] ℝ).continuous.comp hPgtc).integrable_of_hasCompactSupport
      (HasCompactSupport.of_compactSpace _)
  have := text_ae_eq_zero_of_fcoef
    (g := fun x => PgtT η v x i - tsampConv Kα (fun x => w' x i) x) (hPi.sub hA) (fun k => by
    rw [text_fcoef_sub hPi hA, tsamp_fcoef_Pgt hd hη hη1 hL hLip i k, tsamp_conv_real,
      text_fcoef_conv hKαi (hwi i), hKαc k, hrep' i k]
    by_cases hk : k = 0
    · have h0 : Lattice.toEuc (0 : Lattice d) = 0 := by ext j; simp [Lattice.toEuc]
      have hc : Whole.chi (η • Lattice.toEuc (0 : Lattice d)) = 1 := by
        rw [h0, smul_zero]; exact Whole.cmxFB_chi_one (by simp)
      subst hk
      rw [hc]; simp
    · have hten : 0 < 2 * Real.pi * Lattice.enorm k := by
        have := HRS.one_le_enorm k hk
        positivity
      simp only [hk, if_false]
      have h3 : (2 * Real.pi * Lattice.enorm k) ^ (-α) * (2 * Real.pi * Lattice.enorm k) ^ α = 1 := by
        rw [← Real.rpow_add hten]; simp
      have h4 : ((((1 - Whole.chi (η • Lattice.toEuc k)) *
          (2 * Real.pi * Lattice.enorm k) ^ (-α) : ℝ)) : ℂ) *
          (((2 * Real.pi * Lattice.enorm k) ^ α : ℝ) : ℂ) =
          (((1 - Whole.chi (η • Lattice.toEuc k) : ℝ)) : ℂ) := by
        rw [← Complex.ofReal_mul]
        congr 1
        calc (1 - Whole.chi (η • Lattice.toEuc k)) * (2 * Real.pi * Lattice.enorm k) ^ (-α) *
              (2 * Real.pi * Lattice.enorm k) ^ α
            = (1 - Whole.chi (η • Lattice.toEuc k)) * ((2 * Real.pi * Lattice.enorm k) ^ (-α) *
              (2 * Real.pi * Lattice.enorm k) ^ α) := by ring
          _ = _ := by rw [h3, mul_one]
      push_cast at h4 ⊢
      linear_combination (-(Torus.fcoef (fun x => v x i) k)) * h4)
  filter_upwards [this] with x hx
  simpa [sub_eq_zero] using hx

end HRS.Commutator.TorusNote
