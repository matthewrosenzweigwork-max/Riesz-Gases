import HRS.Commutator.Torus.LEIBTAux23

/-!
# LEIB-T helpers, part 24: the abstract `ℝ≥0∞` algebra of one step of the transference
-/

noncomputable section

open MeasureTheory Filter Topology Metric Set
open scoped ENNReal NNReal BigOperators

namespace HRS.Commutator.TorusNote

lemma leibt_step_alg {XH XF Xg XG Xf a A₁ B₁ A₂ B₂ Cl κ₁ κ₂ κ₃ κ₄ sF sG sH P Pf Pg Qg Qf : ℝ≥0∞}
    (ha0 : a ≠ 0) (haT : a ≠ ⊤) (hab₁ : a = A₁ * B₁) (hab₂ : a = A₂ * B₂)
    (H1 : a * XH ≤ P + sH * a) (H2 : P ≤ Cl * (Pf * Qg + Pg * Qf))
    (H3 : Pf ≤ κ₁ * A₁ * XF + sF * A₁) (H4 : Qg ≤ κ₂ * B₁ * Xg)
    (H5 : Pg ≤ κ₃ * A₂ * XG + sG * A₂) (H6 : Qf ≤ κ₄ * B₂ * Xf) :
    XH ≤ Cl * ((κ₁ * XF + sF) * (κ₂ * Xg) + (κ₃ * XG + sG) * (κ₄ * Xf)) + sH := by
  have h : a * XH ≤ a * (Cl * ((κ₁ * XF + sF) * (κ₂ * Xg) + (κ₃ * XG + sG) * (κ₄ * Xf)) + sH) := by
    calc a * XH ≤ P + sH * a := H1
      _ ≤ Cl * (Pf * Qg + Pg * Qf) + sH * a := by gcongr
      _ ≤ Cl * ((κ₁ * A₁ * XF + sF * A₁) * (κ₂ * B₁ * Xg) +
            (κ₃ * A₂ * XG + sG * A₂) * (κ₄ * B₂ * Xf)) + sH * a := by gcongr
      _ = Cl * ((A₁ * B₁) * ((κ₁ * XF + sF) * (κ₂ * Xg)) +
            (A₂ * B₂) * ((κ₃ * XG + sG) * (κ₄ * Xf))) + sH * a := by ring
      _ = a * (Cl * ((κ₁ * XF + sF) * (κ₂ * Xg) + (κ₃ * XG + sG) * (κ₄ * Xf)) + sH) := by
          rw [← hab₁, ← hab₂]; ring
  exact (ENNReal.mul_le_mul_iff_right ha0 haT).1 h

end HRS.Commutator.TorusNote
