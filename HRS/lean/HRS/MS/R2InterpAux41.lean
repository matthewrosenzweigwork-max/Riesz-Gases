import HRS.MS.R2InterpAux40
import HRS.MS.CovMeasAux30

/-!
# S10.2 (worker S102), part 41 (packet G2): the cut-off of an admissible field and the interval value
-/

noncomputable section

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators

namespace HRS.MS.R2Interp

open HRS HRS.Whole

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {Pw : ℝ}

/-- The cut-off of a time-dependent functional to the time interval `(a,b]`. -/
def s102_cut (a b : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) : ℝ → (Euc d → ℝ) → ℝ :=
  fun u => if u ∈ Ioc a b then z u else 0

theorem s102_cut_apply (a b : ℝ) (z : ℝ → (Euc d → ℝ) → ℝ) (u : ℝ) (f : Euc d → ℝ) :
    s102_cut a b z u f = (Ioc a b).indicator (fun u => z u f) u := by
  unfold s102_cut
  by_cases h : u ∈ Ioc a b <;> simp [h]

theorem s102_dualNormE_zero (r : ℕ) (Pw : ℝ) : dualNormE (d := d) r Pw 0 = 0 := by
  simp [dualNormE]

theorem s102_cut_dualNorm_le {a b : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ} {M : ℝ≥0∞} (hM : ∀ u, dualNormE r Pw (z u) ≤ M)
    (u : ℝ) : dualNormE r Pw (s102_cut a b z u) ≤ (Ioc a b).indicator (fun _ => M) u := by
  unfold s102_cut
  by_cases h : u ∈ Ioc a b
  · simp only [h, if_true, indicator_of_mem]; exact hM u
  · simp [h, s102_dualNormE_zero]

theorem s102_cut_L1F {a b : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ} (hz : IsR2L1F r Pw T z) {M : ℝ≥0∞}
    (hM : ∀ u ∈ Icc (0 : ℝ) T, dualNormE r Pw (z u) ≤ M) (hMt : M * ENNReal.ofReal (b - a) < ⊤) :
    IsR2L1F r Pw T (s102_cut a b z) := by
  obtain ⟨h1, h2, h3⟩ := hz
  refine ⟨fun u hu => ?_, fun f hf => ?_, ?_⟩
  · by_cases hab : u ∈ Ioc a b
    · simpa [s102_cut, hab] using h1 u hu
    · refine ⟨fun f g _ _ => by simp [s102_cut, hab], fun c f _ => by simp [s102_cut, hab], 0, fun f _ => ?_⟩
      simp [s102_cut, hab]
  · have : (fun u => s102_cut a b z u f) = (Ioc a b).indicator (fun u => z u f) := by
      funext u; exact s102_cut_apply a b z u f
    rw [this]
    exact (h2 f hf).indicator measurableSet_Ioc
  · refine lt_of_le_of_lt (lintegral_mono_ae ?_) (?_ : ∫⁻ u in Icc (0 : ℝ) T, (Ioc a b).indicator (fun _ => M) u < ⊤)
    · filter_upwards [ae_restrict_mem measurableSet_Icc] with u hu
      have hM' : ∀ u, dualNormE r Pw (if u ∈ Icc (0 : ℝ) T then z u else 0) ≤ M := fun u => by
        by_cases hu : u ∈ Icc (0 : ℝ) T
        · simp [hu, hM u hu]
        · simp [hu, s102_dualNormE_zero]
      by_cases hab : u ∈ Ioc a b
      · simp only [indicator_of_mem hab]
        simpa [s102_cut, hab, hu] using hM' u
      · simp [s102_cut, hab, s102_dualNormE_zero]
    · rw [lintegral_indicator_const measurableSet_Ioc, Measure.restrict_apply measurableSet_Ioc]
      refine lt_of_le_of_lt (mul_le_mul' le_rfl (measure_mono inter_subset_left)) ?_
      rwa [Real.volume_Ioc]

theorem s102_cut_meas {a b : ℝ} {z : ℝ → (Euc d → ℝ) → ℝ} (hz : R2JIntegrandMeas C m T z) :
    R2JIntegrandMeas C m T (s102_cut a b z) := by
  intro ta tb φa φb ha hb hta htb
  have := (hz ta tb φa φb ha hb hta htb).indicator (measurableSet_Ioc (a := a) (b := b))
  refine this.congr (Filter.Eventually.of_forall fun u => ?_)
  exact (s102_cut_apply a b z u _).symm

theorem s102_cut_JValue {z : ℝ → (Euc d → ℝ) → ℝ} {a b : ℝ} (ha : 0 ≤ a) (hb : b ≤ T)
    {J : TensorDual (OscPath d m T) 2} (hJ : IsR2JValue C m T z (Ioc a b) J) :
    IsR2JValue C m T (s102_cut a b z) (Ioc 0 T) J := by
  refine ⟨hJ.1, fun ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂ => ?_⟩
  rw [hJ.2 ta tb φa φb l₁ l₂ hφa hφb hta htb hl₁ hl₂]
  congr 1
  have e : ∀ (g : ℝ → Euc d → ℝ) (S : Set ℝ), ∫ u in S, s102_cut a b z u (g u) =
      ∫ u in S, (Ioc a b).indicator (fun u => z u (g u)) u := fun g S => by
    congr 1; funext u; exact s102_cut_apply a b z u (g u)
  rw [e, setIntegral_indicator measurableSet_Ioc]
  refine setIntegral_congr_set ?_
  have : Ioc 0 T ∩ Icc 0 (min ta tb) ∩ Ioc a b = Ioc a b ∩ Icc 0 (min ta tb) := by
    ext u
    simp only [mem_inter_iff, mem_Ioc, mem_Icc]
    constructor
    · rintro ⟨⟨_, h2⟩, h3⟩; exact ⟨h3, h2⟩
    · rintro ⟨h3, h2⟩; exact ⟨⟨⟨by linarith [h3.1], by linarith [h3.2]⟩, h2⟩, h3⟩
  rw [this]

end HRS.MS.R2Interp

end
