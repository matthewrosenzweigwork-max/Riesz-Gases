import HRS.MC.SEdgeVocab
import HRS.MC.SEdgeB2a
import HRS.MC.SEdgeB2b
import HRS.MC.SEdgeB3
import HRS.MC.SEdgeB4a
import HRS.Equilibrium.QuadraticLimit.GibbsAuxG

/-!
# Packet B4b: moments of the quadratic remainder (relocated proof of `sed_B4b_energy`)

With `Y_N = N mE(h_v) + J/2` (`J = iint h_v`): `E_{mu^N} Y_N^2 <= 3 ||h_v||_2^2` (`q08_energy_L2`), and the
Holder transfer B4a (`r = 2` for the mean, `r = 4/3` for the exponent `3/2`) moves it to `Q_{N,beta}`.
Note `B_N = Y_N - E_Q Y_N`.
-/

open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators

noncomputable section

namespace HRS.MC.SEdge.B4b

open HRS.Sec7

/-- `sed_Q` is a probability measure (`N ≥ 1`, `β ≥ 0`). -/
theorem b4b_isProb {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ}
    (hβ : 0 ≤ β) {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) (N : ℕ) (hN : 1 ≤ N) :
    IsProbabilityMeasure (sed_Q d s N β ρ) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  rcases hβ.eq_or_lt with h0 | hpos
  · subst h0
    have : sed_Q d s N 0 ρ = Measure.pi fun _ : Fin N => withDensityReal ρ :=
      HRS.MC.SEdge.B4a.b4a_gibbs_zero _ _ _
    rw [this]
    infer_instance
  · obtain ⟨e, he⟩ := HRS.MC.SEdge.B3.sed_B3_onb_proof (by omega : 1 ≤ d) hρ
    obtain ⟨c, hc⟩ := HRS.MC.SEdge.B4a.b4a_exists_c hd hs0 hs
    let D : HRS.Q08.Q08Data d :=
      { s := s, β := β, ρ := ρ, c := c, B := 0, h := fun _ _ => 0, e := e, p := 0,
        φ := fun a => a.elim0, hd := hd, hs0 := hs0, hs := hs, hβ := hpos, hρ := hρ,
        hc := hc, hmeas := measurable_const, hsymm := fun _ _ => rfl,
        hB := fun x y _ => by simp, he := he,
        hφ := fun a => a.elim0 }
    exact HRS.Q08.q08_gibbs_isProb D N hN

/-- `Y_N = N mE(h_v) + J/2`. -/
def b4b_Y (d : ℕ) (s : ℝ) (ρ : Torus d → ℝ) (v : Fin d → Torus d → ℝ) (N : ℕ)
    (X : Config d N) : ℝ :=
  (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ) +
    (1 / 2) * ∫ x, ∫ y, Q66.q66_hv d s v x y ∂(withDensityReal ρ) ∂(withDensityReal ρ)

/-- Data of the `L^2` energy bound. -/
theorem b4b_L2 {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2)
    {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ) {v : Fin d → Torus d → ℝ}
    (hv : ∀ j, Torus.IsSmooth (v j)) (N : ℕ) (hN : 1 ≤ N) :
    Measurable (b4b_Y d s ρ v N) ∧
      MemLp (b4b_Y d s ρ v N) 2 (Measure.pi fun _ : Fin N => withDensityReal ρ) ∧
      ∫ X, b4b_Y d s ρ v N X ^ 2 ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) ≤
        3 * ∫ x, ∫ y, Q66.q66_hv d s v x y ^ 2 ∂(withDensityReal ρ) ∂(withDensityReal ρ) := by
  haveI : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  obtain ⟨B, c, hc, hB⟩ := HRS.MC.SEdge.B2a.b2a_main hd hs0 hs hv
  have hsd : s < (d : ℝ) := by
    have : (0 : ℝ) ≤ d := by positivity
    linarith
  have hvc : ∀ j, Continuous (v j) := fun j => HRS.StaticLimitAux.continuous_of_smooth (hv j)
  obtain ⟨e, he⟩ := HRS.MC.SEdge.B3.sed_B3_onb_proof (by omega : 1 ≤ d) hρ
  let D : HRS.Q08.Q08Data d :=
    { s := s, β := 1, ρ := ρ, c := c, B := B, h := Q66.q66_hv d s v, e := e, p := 0,
      φ := fun a => a.elim0, hd := hd, hs0 := hs0, hs := hs, hβ := one_pos, hρ := hρ,
      hc := hc, hmeas := Q66.q66_hv_measurable hsd hvc,
      hsymm := Q66.q66_hv_symm hsd v, hB := hB, he := he,
      hφ := fun a => a.elim0 }
  have hk := HRS.MC.SEdge.B2b.sed_B2b_hs_proof hd hs0 hs hρ hv
  refine ⟨?_, ?_, ?_⟩
  · exact (measurable_const.mul (HRS.Q08.q08_measurable_energy D N)).add measurable_const
  · exact HRS.Q08.q08gl_Z_memLp D.μ D.h D.hmeas hk D.hsymm N hN
  · have := HRS.Q08.q08_energy_L2 D.μ D.h D.hmeas D.hsymm hk N hN
    exact this

section Main

variable {d : ℕ} {s : ℝ} (hd : 2 ≤ d) (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {β : ℝ} (hβ : 0 ≤ β)
  {ρ : Torus d → ℝ} (hρ : SmoothPosDensity ρ)
include hd hs0 hs hβ hρ

theorem sed_B4b_energy_proof {v : Fin d → Torus d → ℝ} (hv : ∀ j, Torus.IsSmooth (v j)) :
    (∀ N : ℕ, 1 ≤ N → Integrable
      (fun X : Config d N => modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))
      (sed_Q d s N β ρ)) ∧
    ∃ C : ℝ, ∀ N : ℕ, 1 ≤ N →
      |∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ) ∂(sed_Q d s N β ρ)| ≤ C ∧
      ∫ X, |sed_B d s ρ β v X| ^ (3 / 2 : ℝ) ∂(sed_Q d s N β ρ) ≤ C := by
  haveI hP : IsProbabilityMeasure (withDensityReal ρ) := HRS.MC.SEdge.B3.b3_prob hρ
  set J : ℝ := ∫ x, ∫ y, Q66.q66_hv d s v x y ∂(withDensityReal ρ) ∂(withDensityReal ρ) with hJ
  set K : ℝ := 3 * ∫ x, ∫ y, Q66.q66_hv d s v x y ^ 2 ∂(withDensityReal ρ) ∂(withDensityReal ρ)
    with hK
  have hK0 : 0 ≤ K := by
    rw [hK]
    exact mul_nonneg (by norm_num) (integral_nonneg fun x => integral_nonneg fun y => sq_nonneg _)
  obtain ⟨C2, hC2, T2⟩ := HRS.MC.SEdge.B4a.sed_B4a_transfer_proof hd hs0 hs hβ hρ (r := 2)
    (by norm_num)
  obtain ⟨C43, hC43, T43⟩ := HRS.MC.SEdge.B4a.sed_B4a_transfer_proof hd hs0 hs hβ hρ (r := 4 / 3)
    (by norm_num)
  set A : ℝ := C2 * K ^ (1 / 2 : ℝ) with hAdef
  have hA0 : 0 ≤ A := mul_nonneg hC2 (Real.rpow_nonneg hK0 _)
  set A' : ℝ := C43 * (2 * K + 2 * A ^ 2) ^ (1 / (4 / 3 : ℝ)) with hA'def
  have hA'0 : 0 ≤ A' := mul_nonneg hC43 (Real.rpow_nonneg (by positivity) _)
  have main : ∀ N : ℕ, 1 ≤ N →
      Integrable (fun X : Config d N => modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ))
        (sed_Q d s N β ρ) ∧
      |∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ) ∂(sed_Q d s N β ρ)|
        ≤ A + |J| / 2 ∧
      ∫ X, |sed_B d s ρ β v X| ^ (3 / 2 : ℝ) ∂(sed_Q d s N β ρ) ≤ A' := by
    intro N hN
    haveI hG : IsProbabilityMeasure (sed_Q d s N β ρ) := b4b_isProb hd hs0 hs hβ hρ N hN
    haveI hPP : IsProbabilityMeasure (Measure.pi fun _ : Fin N => withDensityReal ρ) := by
      infer_instance
    obtain ⟨hYm, hYL, hYint⟩ := b4b_L2 hd hs0 hs hρ hv N hN
    set Y : Config d N → ℝ := b4b_Y d s ρ v N with hYdef
    have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
    have hYsq : ∫⁻ X, ENNReal.ofReal (Y X ^ 2) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) ≤
        ENNReal.ofReal K := by
      rw [← ofReal_integral_eq_lintegral_ofReal hYL.integrable_sq
        (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
      exact ENNReal.ofReal_le_ofReal hYint
    -- Step A: r = 2
    have hA : ∫⁻ X, ENNReal.ofReal |Y X| ∂(sed_Q d s N β ρ) ≤ ENNReal.ofReal A := by
      have h1 := T2 N hN (fun X => ENNReal.ofReal |Y X|) hYm.abs.ennreal_ofReal
      have h2 : ∫⁻ X, (ENNReal.ofReal |Y X|) ^ (2 : ℝ) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ)
          = ∫⁻ X, ENNReal.ofReal (Y X ^ 2) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) := by
        refine lintegral_congr fun X => ?_
        rw [ENNReal.ofReal_rpow_of_nonneg (abs_nonneg _) (by norm_num), Real.rpow_two, sq_abs]
      rw [h2] at h1
      refine h1.trans ?_
      calc ENNReal.ofReal C2 * (∫⁻ X, ENNReal.ofReal (Y X ^ 2)
            ∂(Measure.pi fun _ : Fin N => withDensityReal ρ)) ^ (1 / (2 : ℝ))
          ≤ ENNReal.ofReal C2 * (ENNReal.ofReal K) ^ (1 / (2 : ℝ)) := by gcongr
        _ = ENNReal.ofReal A := by
          rw [hAdef, ENNReal.ofReal_mul hC2, ENNReal.ofReal_rpow_of_nonneg hK0 (by norm_num)]
    have hGY : Integrable Y (sed_Q d s N β ρ) := by
      refine ⟨hYm.aestronglyMeasurable, ?_⟩
      unfold HasFiniteIntegral
      simp_rw [Real.enorm_eq_ofReal_abs]
      exact lt_of_le_of_lt hA ENNReal.ofReal_lt_top
    have hYabs : ∫ X, |Y X| ∂(sed_Q d s N β ρ) ≤ A := by
      have := ofReal_integral_eq_lintegral_ofReal hGY.abs
        (Filter.Eventually.of_forall fun _ => abs_nonneg _)
      rw [← this] at hA
      exact (ENNReal.ofReal_le_ofReal_iff hA0).1 hA
    set c : ℝ := ∫ X, Y X ∂(sed_Q d s N β ρ) with hc
    have hcA : |c| ≤ A := (abs_integral_le_integral_abs).trans hYabs
    have hmE : ∀ X, modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ) =
        (N : ℝ)⁻¹ * (Y X - J / 2) := by
      intro X
      simp only [hYdef, b4b_Y, hJ]
      field_simp
      ring
    have hNmE : ∀ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ) =
        Y X - J / 2 := by
      intro X
      rw [hmE X]
      field_simp
    have hint1 : Integrable (fun X : Config d N =>
        modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)) (sed_Q d s N β ρ) := by
      have : (fun X : Config d N => modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)) =
          fun X => (N : ℝ)⁻¹ * (Y X - J / 2) := funext hmE
      rw [this]
      exact (hGY.sub (integrable_const _)).const_mul _
    have hint2 : ∫ X, (N : ℝ) * modulatedEnergy (Q66.q66_hv d s v) X (withDensityReal ρ)
        ∂(sed_Q d s N β ρ) = c - J / 2 := by
      simp_rw [hNmE]
      rw [integral_sub hGY (integrable_const _)]
      simp [hc]
    have hB : ∀ X, sed_B d s ρ β v X = Y X - c := by
      intro X
      unfold sed_B
      have h3 : ∫ Z, modulatedEnergy (Q66.q66_hv d s v) Z (withDensityReal ρ)
          ∂(sed_Q d s N β ρ) = (N : ℝ)⁻¹ * (c - J / 2) := by
        rw [← hint2, integral_const_mul]
        field_simp
      rw [h3, mul_sub, hNmE X]
      field_simp
      ring
    refine ⟨hint1, ?_, ?_⟩
    · rw [hint2]
      calc |c - J / 2| ≤ |c| + |J / 2| := abs_sub _ _
        _ ≤ A + |J| / 2 := by
          rw [abs_div]
          norm_num
          linarith
    · -- Step D: r = 4/3
      have hsq : ∫⁻ X, ENNReal.ofReal ((Y X - c) ^ 2)
          ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) ≤ ENNReal.ofReal (2 * K + 2 * A ^ 2) := by
        have hi : Integrable (fun X => (Y X - c) ^ 2)
            (Measure.pi fun _ : Fin N => withDensityReal ρ) := by
          have := (hYL.sub (memLp_const c)).integrable_sq
          simpa using this
        rw [← ofReal_integral_eq_lintegral_ofReal hi
          (Filter.Eventually.of_forall fun _ => sq_nonneg _)]
        refine ENNReal.ofReal_le_ofReal ?_
        have hdom : Integrable (fun X => 2 * Y X ^ 2 + 2 * c ^ 2)
            (Measure.pi fun _ : Fin N => withDensityReal ρ) :=
          (hYL.integrable_sq.const_mul 2).add (integrable_const _)
        calc ∫ X, (Y X - c) ^ 2 ∂(Measure.pi fun _ : Fin N => withDensityReal ρ)
            ≤ ∫ X, (2 * Y X ^ 2 + 2 * c ^ 2) ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) :=
              integral_mono hi hdom (fun X => by nlinarith [sq_nonneg (Y X + c)])
          _ = 2 * ∫ X, Y X ^ 2 ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) + 2 * c ^ 2 := by
              rw [integral_add (hYL.integrable_sq.const_mul 2) (integrable_const _),
                integral_const_mul]
              simp
          _ ≤ 2 * K + 2 * A ^ 2 := by
              have : c ^ 2 ≤ A ^ 2 := by
                rw [← sq_abs c]
                exact pow_le_pow_left₀ (abs_nonneg _) hcA 2
              have := hYint
              nlinarith
      have hf : Measurable (fun X => ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ))) :=
        ((hYm.sub_const c).abs.pow_const _).ennreal_ofReal
      have h1 := T43 N hN _ hf
      have h2 : ∫⁻ X, (ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ))) ^ (4 / 3 : ℝ)
          ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) =
          ∫⁻ X, ENNReal.ofReal ((Y X - c) ^ 2)
            ∂(Measure.pi fun _ : Fin N => withDensityReal ρ) := by
        refine lintegral_congr fun X => ?_
        rw [ENNReal.ofReal_rpow_of_nonneg (Real.rpow_nonneg (abs_nonneg _) _) (by norm_num),
          ← Real.rpow_mul (abs_nonneg _)]
        have : (3 / 2 : ℝ) * (4 / 3) = (2 : ℕ) := by norm_num
        rw [this, Real.rpow_natCast, sq_abs]
      rw [h2] at h1
      have h3 : ∫⁻ X, ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ)) ∂(sed_Q d s N β ρ) ≤
          ENNReal.ofReal A' := by
        refine h1.trans ?_
        calc ENNReal.ofReal C43 * (∫⁻ X, ENNReal.ofReal ((Y X - c) ^ 2)
              ∂(Measure.pi fun _ : Fin N => withDensityReal ρ)) ^ (1 / (4 / 3 : ℝ))
            ≤ ENNReal.ofReal C43 * (ENNReal.ofReal (2 * K + 2 * A ^ 2)) ^ (1 / (4 / 3 : ℝ)) := by
              gcongr
          _ = ENNReal.ofReal A' := by
              rw [hA'def, ENNReal.ofReal_mul hC43,
                ENNReal.ofReal_rpow_of_nonneg (by positivity) (by norm_num)]
      have h4 : ∫ X, |sed_B d s ρ β v X| ^ (3 / 2 : ℝ) ∂(sed_Q d s N β ρ) =
          (∫⁻ X, ENNReal.ofReal (|Y X - c| ^ (3 / 2 : ℝ)) ∂(sed_Q d s N β ρ)).toReal := by
        simp_rw [hB]
        exact integral_eq_lintegral_of_nonneg_ae
          (Filter.Eventually.of_forall fun X => Real.rpow_nonneg (abs_nonneg _) _)
          ((hYm.sub_const c).abs.pow_const _).aestronglyMeasurable
      rw [h4]
      exact ENNReal.toReal_le_of_le_ofReal hA'0 h3
  refine ⟨fun N hN => (main N hN).1, max (A + |J| / 2) A', fun N hN => ?_⟩
  obtain ⟨-, h2, h3⟩ := main N hN
  exact ⟨h2.trans (le_max_left _ _), h3.trans (le_max_right _ _)⟩

end Main


end HRS.MC.SEdge.B4b
