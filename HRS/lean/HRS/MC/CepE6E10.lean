import HRS.MC.CepE6E9

/-!
# Packet CEPE6E, file 10: small measure-theoretic helpers for the assembly
-/

open MeasureTheory Filter Topology Set
open scoped ENNReal NNReal BigOperators RealInnerProductSpace

noncomputable section

namespace HRS.MC.CepE6E

open HRS HRS.MC.Cepa HRS.MC.CepE6D

variable {Ω : Type*} [mΩ : MeasurableSpace Ω] {P : Measure Ω} {N : ℕ}

theorem cepe6e_meas_lint {Y : ℝ → Ω → Ch N} (hY : Measurable fun p : Ω × ℝ => Y (max p.2 0) p.1)
    {G : Ch N → ℝ≥0∞} (hG : Measurable G) (T : ℝ) :
    Measurable fun ω => ∫⁻ s in Icc (0 : ℝ) T, G (Y s ω) := by
  have h2 := (hG.comp hY).lintegral_prod_right' (ν := volume.restrict (Icc (0 : ℝ) T))
  have : (fun ω => ∫⁻ s in Icc (0 : ℝ) T, G (Y s ω)) =
      fun ω => ∫⁻ s in Icc (0 : ℝ) T, G (Y (max s 0) ω) := by
    funext ω
    exact setLIntegral_congr_fun measurableSet_Icc (fun s hs => by simp only [max_eq_left hs.1])
  rw [this]
  exact h2

theorem cepe6e_liminf_bound {X u : ℕ → ℝ≥0∞} {c0 s B : ℝ≥0∞} (hs : s ≠ ⊤)
    (hX : limsup X atTop ≤ B) (hu : ∀ i, u i ≤ c0 + s * X i) :
    liminf u atTop ≤ c0 + s * B := by
  calc liminf u atTop ≤ limsup u atTop := liminf_le_limsup
    _ ≤ limsup (fun i => c0 + s * X i) atTop :=
        limsup_le_limsup (Eventually.of_forall hu)
    _ = c0 + limsup (fun i => s * X i) atTop :=
        limsup_const_add atTop (fun i => s * X i) c0 (by isBoundedDefault) (by isBoundedDefault)
    _ = c0 + s * limsup X atTop := by rw [ENNReal.limsup_const_mul_of_ne_top hs]
    _ ≤ c0 + s * B := by gcongr

theorem cepe6e_ennreal_div {V : ℝ≥0∞} {c K r : ℝ} (hc : 0 < c) (hK : 0 ≤ K) (hcK : c * K = r)
    (h : ENNReal.ofReal c * V ≤ ENNReal.ofReal r) : V ≤ ENNReal.ofReal K := by
  rw [← hcK, ENNReal.ofReal_mul hc.le] at h
  exact (ENNReal.mul_le_mul_iff_right (a := ENNReal.ofReal c) (by simpa using hc)
    ENNReal.ofReal_ne_top).1 h

theorem cepe6e_enorm_sq_le {m r : ℝ} (hr : 0 < r) (h : ‖m‖ₑ ^ 2 < ENNReal.ofReal r) :
    |m| ≤ Real.sqrt r := by
  rw [Real.enorm_eq_ofReal_abs, ← ENNReal.ofReal_pow (abs_nonneg _),
    ENNReal.ofReal_lt_ofReal_iff hr] at h
  exact Real.abs_le_sqrt (by rw [← sq_abs]; exact h.le)

end HRS.MC.CepE6E
