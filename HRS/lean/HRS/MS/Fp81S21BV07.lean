import HRS.MS.Fp81S21BV06

/-! A finite-partition lower-semicontinuity bound for variation. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Set Filter
open scoped ENNReal Topology
namespace HRS.Fp81.S21
variable {E : Type*} [NormedAddCommGroup E]

theorem fp81s21_eVariationOn_le_of_tendsto {ι : Type*} {p : Filter ι} [NeBot p]
    {F : ι → ℝ → E} {f : ℝ → E} {s : Set ℝ} {C : ℝ≥0∞}
    (hlim : ∀ x ∈ s, Tendsto (fun i => F i x) p (𝓝 (f x)))
    (hbound : ∀ᶠ i in p, eVariationOn (F i) s ≤ C) :
    eVariationOn f s ≤ C := by
  by_contra hn
  have hgt : C < eVariationOn f s := lt_of_not_ge hn
  have hev := eVariationOn.lowerSemicontinuous_aux hlim hgt
  have hempty : ∀ᶠ i in p, False := by
    filter_upwards [hev, hbound] with i hi hj
    exact (not_lt_of_ge hj) hi
  obtain ⟨_, hfalse⟩ := hempty.exists
  exact hfalse

#print axioms fp81s21_eVariationOn_le_of_tendsto
end HRS.Fp81.S21
end
