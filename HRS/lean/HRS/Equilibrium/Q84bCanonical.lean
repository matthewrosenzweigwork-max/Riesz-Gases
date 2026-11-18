/-
# HRS.Equilibrium.Q84bCanonical — packet Q84b: canonicity clause of Lemma 4.15

`q84b_canonical`: for every kernel `ψ` with the conclusions of Proposition 4.13
(`IsPairCorrector`), the triple kernel `G_ψ` is canonical: for `x ≠ y` it is `μ`-integrable in the
third variable with integral zero (source lines 4886-4893).

Route (`Q:eq:pair-projection-T`).  By `q84a_Tsum_eq` the symmetrised `T`-sum is a sum of three
absolutely integrable gradient-difference terms and six force terms.  The `z`-integral of
* `⟨∇g(x-z), ∇_xψ(x,y) - ∇_zψ(z,y)⟩ρ(z)` is `F_μ(x)·∇_xψ(x,y) - Jop ψ(·,y)(x)`
  (`q84b_Jop_eq`, the local cancellation form of `Jop`, at `d = 2` a principal value);
* `∇_xψ(x,z)ρ(z)` is `0` (`q84b_grad_slice_mean`, canonicity of `ψ` differentiated under the
  integral sign, using the singular size bounds);
and the integration by parts `μ[Jop ψ(·,b)] = -∫ F_μ·∇_xψ(x,b) μ(dx)` (`q84b_Jop_mean`, by the
antisymmetry of `∇g` and Fubini) identifies the centring constants of `𝒥ψ`.
-/
import HRS.Equilibrium.Q84bAuxM

open MeasureTheory Filter Topology

noncomputable section

namespace HRS.Q84b

variable {d : ℕ} {s : ℝ}

theorem q84b_canonical (hd : 2 ≤ d) (hcrit : s = (d : ℝ) / 2) (β : ℝ) (hβ : 0 < β)
    (V : Torus d → ℝ) (hV : Torus.IsSmooth V) (ρ : Torus d → ℝ)
    (hρ : IsThermalDensity (periodicRiesz d s) V β ρ) (hρs : SmoothPosDensity ρ) :
    ∀ (f : Torus d → ℝ) (K₁ : ℝ) (ψ : Torus d → Torus d → ℝ), Torus.IsSmooth f →
      IsPairCorrector d s V β ρ f K₁ ψ → IsCanonicalTriple (withDensityReal ρ) (Gpsi d s ρ ψ) := by
  intro f K₁ ψ _ hψ x y hxy
  have hdR : (2 : ℝ) ≤ d := by exact_mod_cast hd
  have hs0 : 0 ≤ s := by rw [hcrit]; linarith
  have hsd : s < d := by rw [hcrit]; linarith
  have hd0 : 0 < d := by omega
  have hρ1 : Torus.IsCk 1 ρ := Q84a.q84a_contDiff_one hρs.smooth
  have hρc : Continuous ρ := HRS.PDE.MFAux.continuous_of_isCk hρ1
  have hρm : Measurable ρ := hρc.measurable
  have hρ0 : ∀ z, 0 ≤ ρ z := fun z => (hρs.pos z).le
  obtain ⟨Bρ, hBρ0, hBρ⟩ := HRS.KernelGrad.isCk_bounded hρ1
  obtain ⟨M, hM0, hM⟩ := Q84a.q84a_force_bound hβ hV hρ hρs
  have hPs : PsiSize s K₁ ψ := hψ.size
  have hsym : IsSymmPair ψ := hψ.symm
  have hmeasψ : Measurable (Function.uncurry ψ) := hψ.measurable
  have hρint : Integrable ρ :=
    hρc.integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
  have hρone : ∫ z, ρ z = 1 := hρs.density.integral_one
  have hyx : y ≠ x := fun h => hxy h.symm
  -- canonicity of `ψ` and of `𝒥ψ`, in terms of volume integrals
  have hcan : ∀ a, Integrable (fun z => ρ z * ψ a z) ∧ ∫ z, ρ z * ψ a z = 0 := by
    intro a
    obtain ⟨h1, h2⟩ := hψ.canonical a
    exact ⟨(q84b_integrable_mu_iff hρm hρ0).1 h1, by
      rw [← integral_withDensityReal_eq ρ hρm hρ0]; exact h2⟩
  have hJcan : ∀ a, Integrable (fun z => ρ z * Jpair d s ρ ψ a z) ∧
      ∫ z, ρ z * Jpair d s ρ ψ a z = 0 := by
    intro a
    obtain ⟨h1, h2⟩ := hψ.jpair_canonical a
    exact ⟨(q84b_integrable_mu_iff hρm hρ0).1 h1, by
      rw [← integral_withDensityReal_eq ρ hρm hρ0]; exact h2⟩
  set F := forceField d s ρ with hF
  have hFm : Measurable F := q84b_measurable_forceField ρ
  have hG1 : ∀ a : Torus d, Integrable (fun z => gradFst ψ a z) :=
    fun a => q84b_gradFst_snd_integrable hd hcrit hPs a
  have hG2 : ∀ b : Torus d, Integrable (fun z => gradFst ψ z b) :=
    fun b => q84b_gradFst_integrable hd hcrit hPs b
  set c1 : ℝ := inner ℝ (F x) (gradFst ψ x y) with hc1
  set c2 : ℝ := inner ℝ (F y) (gradFst ψ y x) with hc2
  set c3 : Euc d := periodicRieszGrad d s (x - y) with hc3
  -- the terms with a constant vector
  have hQ3 : ∀ (a : Torus d) (c : Euc d), Integrable (fun z => ρ z * inner ℝ c (gradFst ψ a z)) :=
    fun a c => q84b_int_mul_inner (hG1 a) hρm hBρ c
  have hQ3v : ∀ (a : Torus d) (c : Euc d), ∫ z, ρ z * inner ℝ c (gradFst ψ a z) = 0 :=
    fun a c => q84b_grad_slice_mean hd hcrit hρ1 hPs hmeasψ hcan a c
  -- the force terms with `F z`
  have hQ4 : ∀ b : Torus d, Integrable (fun z => ρ z * inner ℝ (F z) (gradFst ψ z b)) := by
    intro b
    refine Integrable.mono' ((hG2 b).norm.const_mul (Bρ * M)) ?_ (Eventually.of_forall fun z => ?_)
    · exact (hρm.mul (Measurable.inner hFm (q84b_measurable_gradFst ψ b))).aestronglyMeasurable
    · rw [norm_mul, Real.norm_eq_abs]
      calc |ρ z| * ‖inner ℝ (F z) (gradFst ψ z b)‖ ≤ Bρ * (M * ‖gradFst ψ z b‖) :=
            mul_le_mul (hBρ z) ((norm_inner_le_norm _ _).trans
              (mul_le_mul_of_nonneg_right (hM z) (norm_nonneg _))) (norm_nonneg _) hBρ0
        _ = Bρ * M * ‖gradFst ψ z b‖ := by ring
  set ex : ℝ := ∫ z, ρ z * inner ℝ (F z) (gradFst ψ z x) with hex
  set ey : ℝ := ∫ z, ρ z * inner ℝ (F z) (gradFst ψ z y) with hey
  -- the gradient-difference terms `P1`, `P2`
  obtain ⟨hRk1, hJy⟩ := q84b_Jop_eq hd hs0 hsd hβ hV hρ hρs (f := fun w => ψ w y) (a := x) (b := y)
    hxy (q84b_slice_smooth hPs y) (hG2 y).norm
  obtain ⟨hRk2, hJx⟩ := q84b_Jop_eq hd hs0 hsd hβ hV hρ hρs (f := fun w => ψ w x) (a := y) (b := x)
    hyx (q84b_slice_smooth hPs x) (hG2 x).norm
  set P1 : Torus d → ℝ := fun z => ρ z * inner ℝ (periodicRieszGrad d s (x - z))
    (gradFst ψ x y - gradFst ψ z y) with hP1
  set P2 : Torus d → ℝ := fun z => ρ z * inner ℝ (periodicRieszGrad d s (y - z))
    (gradFst ψ y x - gradFst ψ z x) with hP2
  have hP1e : ∀ z, P1 z = -(q84b_Rk ρ s (fun w => ψ w y) x (x - z)) := by
    intro z
    simp only [hP1, q84b_Rk, sub_sub_cancel, inner_sub_right, gradFst]
    ring
  have hP2e : ∀ z, P2 z = -(q84b_Rk ρ s (fun w => ψ w x) y (y - z)) := by
    intro z
    simp only [hP2, q84b_Rk, sub_sub_cancel, inner_sub_right, gradFst]
    ring
  have hP1i : Integrable P1 := ((hRk1.comp_sub_left x).neg).congr
    (Eventually.of_forall fun z => (hP1e z).symm)
  have hP2i : Integrable P2 := ((hRk2.comp_sub_left y).neg).congr
    (Eventually.of_forall fun z => (hP2e z).symm)
  set Jy : ℝ := Jop d s ρ (fun w => ψ w y) x with hJydef
  set Jx : ℝ := Jop d s ρ (fun w => ψ w x) y with hJxdef
  have hJy' : Jy = c1 + ∫ u, q84b_Rk ρ s (fun w => ψ w y) x u := hJy
  have hJx' : Jx = c2 + ∫ u, q84b_Rk ρ s (fun w => ψ w x) y u := hJx
  have hP1v : ∫ z, P1 z = c1 - Jy := by
    have : ∫ z, P1 z = -∫ u, q84b_Rk ρ s (fun w => ψ w y) x u := by
      rw [integral_congr_ae (Eventually.of_forall hP1e), integral_neg,
        integral_sub_left_eq_self (fun u => q84b_Rk ρ s (fun w => ψ w y) x u) volume x]
    rw [this, hJy']; ring
  have hP2v : ∫ z, P2 z = c2 - Jx := by
    have : ∫ z, P2 z = -∫ u, q84b_Rk ρ s (fun w => ψ w x) y u := by
      rw [integral_congr_ae (Eventually.of_forall hP2e), integral_neg,
        integral_sub_left_eq_self (fun u => q84b_Rk ρ s (fun w => ψ w x) y u) volume y]
    rw [this, hJx']; ring
  -- the centring constants of `𝒥ψ`
  have hMy := (q84b_Jop_mean hd hcrit hβ hV hρ hρs hPs y).2
  have hMx := (q84b_Jop_mean hd hcrit hβ hV hρ hρs hPs x).2
  have hJxy : Jpair d s ρ ψ x y = (Jy + ey) + (Jx + ex) := by
    have e1 : (fun w => ψ x w) = fun w => ψ w x := funext fun w => hsym x w
    simp only [Jpair, projMean, pair]
    rw [e1, integral_withDensityReal_eq ρ hρm hρ0, integral_withDensityReal_eq ρ hρm hρ0, hMy, hMx]
    simp only [hJydef, hJxdef, hey, hex]
    ring
  -- the pointwise decomposition of `ρ G_ψ`
  set R1 : Torus d → ℝ := fun z => -P1 z - P2 z with hR1
  set R2 : Torus d → ℝ := fun z => ρ z * inner ℝ c3 (gradFst ψ y z) -
    ρ z * inner ℝ c3 (gradFst ψ x z) with hR2
  set R3 : Torus d → ℝ := fun z => ρ z * inner ℝ (F x) (gradFst ψ x z) +
    ρ z * inner ℝ (F y) (gradFst ψ y z) with hR3
  set R4 : Torus d → ℝ := fun z => ρ z * inner ℝ (F z) (gradFst ψ z x) +
    ρ z * inner ℝ (F z) (gradFst ψ z y) with hR4
  set R5 : Torus d → ℝ := fun z => ρ z * (c1 + c2) with hR5
  set R6 : Torus d → ℝ := fun z => ρ z * Jpair d s ρ ψ x y + ρ z * Jpair d s ρ ψ x z +
    ρ z * Jpair d s ρ ψ y z with hR6
  have hpt : ∀ z, ρ z * Gpsi d s ρ ψ x y z =
      (1 / 3) * (R1 z + R2 z + R3 z + R4 z + R5 z) - (1 / 3) * R6 z := by
    intro z
    unfold Gpsi
    rw [Q84a.q84a_Tsum_eq hsd hsym x y z]
    simp only [hR1, hR2, hR3, hR4, hR5, hR6, hP1, hP2, inner_sub_right]
    ring
  have hnP1 : Integrable (fun z => -P1 z) := hP1i.neg
  have hR1i : Integrable R1 := hnP1.sub hP2i
  have hR2i : Integrable R2 := (hQ3 y c3).sub (hQ3 x c3)
  have hR3i : Integrable R3 := (hQ3 x (F x)).add (hQ3 y (F y))
  have hR4i : Integrable R4 := (hQ4 x).add (hQ4 y)
  have hR5i : Integrable R5 := hρint.mul_const (c1 + c2)
  have hρJ : Integrable (fun z => ρ z * Jpair d s ρ ψ x y) := hρint.mul_const _
  have hA6 : Integrable (fun z => ρ z * Jpair d s ρ ψ x y + ρ z * Jpair d s ρ ψ x z) :=
    hρJ.add (hJcan x).1
  have hR6i : Integrable R6 := hA6.add (hJcan y).1
  have hR1v : ∫ z, R1 z = (-(c1 - Jy)) - (c2 - Jx) := by
    simp only [hR1]
    rw [integral_sub hnP1 hP2i, integral_neg, hP1v, hP2v]
  have hR2v : ∫ z, R2 z = 0 := by
    simp only [hR2]
    rw [integral_sub (hQ3 y c3) (hQ3 x c3), hQ3v, hQ3v]; simp
  have hR3v : ∫ z, R3 z = 0 := by
    simp only [hR3]
    rw [integral_add (hQ3 x (F x)) (hQ3 y (F y)), hQ3v, hQ3v]; simp
  have hR4v : ∫ z, R4 z = ex + ey := by
    simp only [hR4]
    rw [integral_add (hQ4 x) (hQ4 y)]
  have hR5v : ∫ z, R5 z = c1 + c2 := by
    simp only [hR5]
    rw [integral_mul_const, hρone, one_mul]
  have hR6v : ∫ z, R6 z = Jpair d s ρ ψ x y := by
    simp only [hR6]
    rw [integral_add hA6 (hJcan y).1, integral_add hρJ (hJcan x).1, integral_mul_const, hρone,
      (hJcan x).2, (hJcan y).2]
    ring
  have h12 : Integrable (fun z => R1 z + R2 z) := hR1i.add hR2i
  have h123 : Integrable (fun z => R1 z + R2 z + R3 z) := h12.add hR3i
  have h1234 : Integrable (fun z => R1 z + R2 z + R3 z + R4 z) := h123.add hR4i
  have hAi : Integrable (fun z => R1 z + R2 z + R3 z + R4 z + R5 z) := h1234.add hR5i
  have hAv : ∫ z, (R1 z + R2 z + R3 z + R4 z + R5 z) =
      ((-(c1 - Jy)) - (c2 - Jx)) + 0 + 0 + (ex + ey) + (c1 + c2) := by
    rw [integral_add h1234 hR5i, integral_add h123 hR4i, integral_add h12 hR3i,
      integral_add hR1i hR2i, hR1v, hR2v, hR3v, hR4v, hR5v]
  have hGi : Integrable (fun z => ρ z * Gpsi d s ρ ψ x y z) :=
    ((hAi.const_mul (1 / 3)).sub (hR6i.const_mul (1 / 3))).congr
      (Eventually.of_forall fun z => (hpt z).symm)
  refine ⟨(q84b_integrable_mu_iff hρm hρ0).2 hGi, ?_⟩
  rw [integral_withDensityReal_eq ρ hρm hρ0, integral_congr_ae (Eventually.of_forall hpt),
    integral_sub (hAi.const_mul (1 / 3)) (hR6i.const_mul (1 / 3)), integral_const_mul,
    integral_const_mul, hAv, hR6v, hJxy]
  ring

end HRS.Q84b
