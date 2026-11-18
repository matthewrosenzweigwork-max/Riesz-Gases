import HRS.Sections.ScrnAux41

/-!
# Packet SCRN, part 42: the Lindeberg term for the transported mesoscopic tests

`scrn_lind_final`: `∫ ‖f(y) - m‖³ dy ≤ 2 p (C ℓ^{-d/2}) · (p C²)`.
-/

noncomputable section

open MeasureTheory Filter Topology ProbabilityTheory Set
open scoped ENNReal NNReal BigOperators ComplexConjugate

namespace HRS

open HRS.Main.A8P PDE

variable {d : ℕ}

local notation "ℝ^" p => EuclideanSpace ℝ (Fin p)

theorem scrn_GB_sup {s ℓ θ C : ℝ} {g : Torus d → ℝ} (h : ScrnGB d s ℓ θ g C) (y : Torus d) :
    |g y| ≤ C * ℓ ^ (-((d : ℝ) / 2)) := by
  have h0 := h.d0 (Torus.rep y)
  rw [norm_iteratedFDeriv_zero] at h0
  simpa [Torus.lift, Torus.mk_rep] using h0

theorem scrn_GB_l2 {s ℓ θ C : ℝ} {g : Torus d → ℝ} (h : ScrnGB d s ℓ θ g C)
    (hg : Continuous g) : ∫ y, g y ^ 2 ∂(volume : Measure (Torus d)) ≤ C ^ 2 := by
  have hP := scrn_parseval_re hg hg
  have e : ∀ k : Lattice d, (conj (coeffOf g k) * coeffOf g k).re = ‖coeffOf g k‖ ^ 2 := by
    intro k
    rw [Complex.conj_mul', ← Complex.ofReal_pow, Complex.ofReal_re]
  have hP' : HasSum (fun k : Lattice d => ‖coeffOf g k‖ ^ 2) (∫ y, g y * g y) := by
    convert hP using 1
    funext k; exact (e k).symm
  have := hP'.tsum_eq
  have e2 : ∫ y, g y ^ 2 ∂(volume : Measure (Torus d)) = ∫ y, g y * g y := by
    congr 1; funext y; ring
  rw [e2, ← this]
  exact h.l2b

theorem scrn_lind_final {s : ℝ} {hs0 : 0 ≤ s} {hsd : s < d} {β : ℝ} {hβ : 0 < β} {p : ℕ}
    {ℓ lamS CG : ℝ} (hℓ : 0 < ℓ) (hCG : 0 ≤ CG) {ts : Fin p → ℝ} {ψ : Fin p → Torus d → ℝ}
    {f : Fin p → ℝ → Torus d → ℝ} (htr : ScrnTr d hs0 hsd hβ ℓ lamS CG ts ψ f) :
    ∫ y, ‖scrnFvec f y - ∫ y', scrnFvec f y' ∂(volume : Measure (Torus d))‖ ^ 3
        ∂(volume : Measure (Torus d)) ≤
      2 * p * (CG * ℓ ^ (-((d : ℝ) / 2))) * (p * CG ^ 2) := by
  have h0 : ∀ a, ts a ∈ Set.Icc 0 (ts a) := fun a => ⟨htr.ts0 a, le_rfl⟩
  have hz : ∀ a, (0 : ℝ) ∈ Set.Icc 0 (ts a) := fun a => ⟨le_rfl, htr.ts0 a⟩
  exact scrn_lind f htr.fcont (A := CG * ℓ ^ (-((d : ℝ) / 2)))
    (mul_nonneg hCG (Real.rpow_nonneg hℓ.le _))
    (fun a y => scrn_GB_sup (htr.gb a 0 (hz a)) y)
    (fun a => scrn_GB_l2 (htr.gb a 0 (hz a)) (htr.fcont a))

end HRS
