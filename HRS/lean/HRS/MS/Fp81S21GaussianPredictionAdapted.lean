import HRS.MS.Fp81S21Gaussian35Selection
import HRS.MS.Fp81S21PredMap10
import HRS.MS.Fp81S21Uniform2
import HRS.MS.Fp81S21SLin

/-! Packet 36A: continuous clipped predictions on the retained canonical source.
This file proves the continuity/physical-identity part only. Adaptedness is a
separate obligation. The V1 radius is chart-uniform, so all retained selections
remain after the radius. No canonical family or history is replaced. -/
set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Topology Set
open scoped ENNReal
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.R2Interp HRS.MS.CovMeas

/-- Continuous versions of the *retained* canonical coefficients, with
simultaneous compact-test agreement with the retained physical realization. -/
theorem fp81s21_gaussian_prediction_retained_version (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ Q : fp81s21_Gaussian35Selection p R, ∀ H : ℝ, 0 < H →
      ∃ X : Q.src.G0.Ω → C(Icc (0 : ℝ) H, r26t6_Coeff),
        Measurable X ∧ MemLp X 2 Q.src.G0.P ∧
        (∀ t : Icc (0 : ℝ) H,
          (fun ω => X ω t) =ᵐ[Q.src.G0.P] fp81s21_gaussian35_qG Q t) ∧
        ∀ᵐ ω ∂Q.src.G0.P, ∀ t : Icc (0 : ℝ) H, ∀ f, IsR2Test f →
          fp81s21_chartAction Q.E (X ω t) f = OscDual.eval (Q.src.G0.Z t ω) f := by
  obtain ⟨δ₀, hδ₀, hhalf, hv⟩ := fp81s21_gaussian_physical_continuous_version p
  refine ⟨δ₀, hδ₀, hhalf, ?_⟩
  intro δ hδ hδle R Q H hH
  obtain ⟨M2, M6, _, _, hvH⟩ := hv δ hδ hδle R Q.Es Q.E
  obtain ⟨D, _, hvG⟩ := hvH H hH
  obtain ⟨qs, _, _, hweak, _, hstart⟩ := hvG Q.src.G0
  obtain ⟨X, hXm, hX2, hsec, _⟩ := hstart 0 le_rfl
  have hcan := (Q.canon.payload Q.src.G0).coefficients.weak_momentRep
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) p.d]
  have hret : ∀ t : Icc (0 : ℝ) H,
      (fun ω => X ω t) =ᵐ[Q.src.G0.P] fp81s21_gaussian35_qG Q t := by
    intro t
    have he := fp81s21_MomentRep_eq_ae hP Q.E Q.src.G0.P
      (fun u ω f => OscDual.eval (Q.src.G0.Z u ω) f)
      (fp81s21_gaussian35_qG Q)
      (fun u ω => fp81s21_gaussian_chartEmbed p Q.Es Q.E (qs u ω))
      Q.MUG M2 hcan hweak t t.property.1
    filter_upwards [hsec t, he] with ω hx hq
    simp only [zero_add] at hx
    exact hx.trans hq.symm
  obtain ⟨_, _, _, hphys⟩ := fp81s21_gaussian_V2_G_selected p R Q.Es Q.E
    Q.src.G0 0 H le_rfl hH Q.MUG (Q.canon.q Q.src.G0) Q.εG
    (Q.canon.payload Q.src.G0) M2
    (fun u ω => fp81s21_gaussian_chartEmbed p Q.Es Q.E (qs u ω)) hweak X hXm hsec
  exact ⟨X, hXm, hX2, hret, by simpa only [zero_add] using hphys⟩

/-- The continuous clipped prediction and its exact fixed-cutoff, fixed-time
physical identity. This is the first two construction steps of 36A; it does
not assert the as-yet separate past-measurable representative clause. -/
theorem fp81s21_gaussian_prediction_continuous_physical (p : Parameters) :
    ∃ δ₀ : ℝ, 0 < δ₀ ∧ δ₀ ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ₀ → ∀ R : Trajectory p δ,
      ∀ Q : fp81s21_Gaussian35Selection p R, ∀ a : ℝ, 0 ≤ a →
      ∃ Y : Q.src.G0.Ω → C(Icc (0 : ℝ) (a + p.T), Window p),
        Measurable Y ∧ MemLp Y 2 Q.src.G0.P ∧
        ∀ r : Icc (0 : ℝ) (a + p.T), ∀ τ : Icc (0 : ℝ) p.T,
        ∀ᵐ ω ∂Q.src.G0.P,
          OscPath.at' (Y ω r) τ =
            r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ)
              (a + τ) (min (r : ℝ) (a + τ))
              (fp81s21_chartAction Q.E
                (fp81s21_gaussian35_qG Q (min (r : ℝ) (a + τ)) ω)) := by
  obtain ⟨δv, hδv, hhalf, hv⟩ := fp81s21_gaussian_prediction_retained_version p
  obtain ⟨δd, hδd, _, hd⟩ := fp81s21_uniform_orbit_amplitudes p
  refine ⟨min δv δd, lt_min hδv hδd, (min_le_left _ _).trans hhalf, ?_⟩
  intro δ hδ hδle R Q a ha
  have hH : 0 < a + p.T := add_pos_of_nonneg_of_pos ha p.hT
  obtain ⟨X, hXm, hX2, hsec, _⟩ :=
    hv δ hδ (hδle.trans (min_le_left _ _)) R Q (a + p.T) hH
  obtain ⟨Co, co, _, _, hD⟩ := hd δ hδ (hδle.trans (min_le_right _ _)) R
  have hP : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    nlinarith [Nat.cast_nonneg (α := ℝ) p.d]
  obtain ⟨L, _, hL⟩ := fp81s21_recentPred_exists hP (hD (a + p.T) hH)
    (fp81s21_S102Lin p R (a + p.T)) Q.E
    (b := 0) (θ := a) (S := p.T) (H := a + p.T)
    le_rfl ha p.hT.le le_rfl (by simp)
  refine ⟨fun ω => L (X ω), L.continuous.measurable.comp hXm,
    L.comp_memLp' hX2, ?_⟩
  intro r τ
  let s := fp81s21_predSource ha r τ
  filter_upwards [hsec s] with ω hω
  have he := hL (X ω) r τ
  simp only [zero_add] at he
  change OscPath.at' (L (X ω) r) τ =
    r2Vprop (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) (a + τ) (s : ℝ)
      (fp81s21_chartAction Q.E (X ω s)) at he
  rw [hω] at he
  exact he

#print axioms fp81s21_gaussian_prediction_retained_version
#print axioms fp81s21_gaussian_prediction_continuous_physical
end HRS.Fp81.S21
end
