import HRS.MS.R2InterpAux67
import HRS.MS.R2InterpAux75

/-!
# S10.2 (worker S102), part 68: reduction of the path interpolation to the particle-side inputs

`S102Part` collects exactly the statements about the particle system that the deterministic/Itô machinery of Aux1-67 needs (none is assumed in a frozen
statement; each is a packet to be proved from `hreal`, `hlaw`, `hinv`): the drift structure and covariance paths (M1/M2), the path facts (M3), and the
Itô-process representation (F5).  `s102_main_of_part` derives the conclusion of `r2_path_interpolation` from them.
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ} {Pw : ℝ}

set_option maxSynthPendingDepth 3 in
/-- The particle-side inputs of the path interpolation. -/
def S102Part (C : WholeCoeff d) (m T : ℝ) (r : ℕ) (Pw sQ : ℝ) (μ : Measure (Euc d)) (hT : 0 < T) {N : ℕ} {Ω : Type}
    {mΩ : MeasurableSpace Ω} (P : Measure Ω) (X : ℝ≥0 → Ω → EucConfig d N) (ℱ : Filtration ℝ mΩ)
    (W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ) : Prop :=
  IsBrownianFiltration P ℱ W' ∧
  ∃ (Mb : Ω → ℝ → ℝ) (Vf : Ω → ℝ),
    (∀ᵐ ζ ∂P, S102Drift C m T r Pw (fun u => r2QuadField sQ μ P X u ζ) (Mb ζ)) ∧
    Integrable (fun ζ => ∫ u in Ioc 0 T, Mb ζ u) P ∧
    (∀ᵐ ζ ∂P, ContinuousOn (s102_Y C m T P X ζ) (Icc 0 T)) ∧
    Integrable Vf P ∧
    (∀ᵐ ζ ∂P, ∃ (Jc : ℝ → TensorDual (OscPath d m T) 2), Jc 0 = 0 ∧
      (∀ a b : ℝ, 0 ≤ a → a ≤ b → b ≤ T → IsR2JValue C m T (s102_etaf μ X ζ) (Ioc a b) (Jc b - Jc a)) ∧
      BoundedVariationOn Jc (Icc 0 T) ∧ (eVariationOn Jc (Icc 0 T)).toReal ≤ Vf ζ) ∧
    AEMeasurable (fun ζ => zetaPathW m T 0 P X ζ) P ∧
    AEMeasurable (fun ζ => s102_y0 C m T P X ζ) P ∧
    (∀ L : ℕ, ∀ᵐ ζ ∂P, ∀ i j, IntegrableOn
      (s102_hh2 C m (s102_tauk hT L) (s102_alk L) (s102_etaf μ X ζ) i j) (Icc 0 T)) ∧
    (∀ (L : ℕ) (Φ : OscPath d m T → ℝ), MemCb 5 Φ →
      AEStronglyMeasurable (fun ζ => ∫ u in Ioc 0 T, s102_cylA C m T sQ μ P X (s102_tauk hT L) (s102_alk L)
        (fun x => Φ (s102_Lam T L x)) ζ u) P ∧
      AEStronglyMeasurable (fun ζ => ∫ u in Ioc 0 T, s102_cylJ C m T μ P X (s102_tauk hT L) (s102_alk L)
        (fun x => Φ (s102_Lam T L x)) ζ u) P) ∧
    ∀ L : ℕ, S102ItoRep C m T sQ μ hT L P X ℱ W'

set_option maxSynthPendingDepth 3 in
/-- The conclusion of `r2_path_interpolation` from the standing assumptions and the particle-side inputs. -/
theorem s102_main_of_part (hs : S102Std C m T r c) (hd : 1 ≤ d) (hP0 : 0 ≤ Pw) (hr : (d : ℝ) / 2 + 1 < r)
    (hP : (d : ℝ) < 2 * Pw) (hlin : S102Lin C m T) (hT : 0 < T) (sQ : ℝ) (μ : Measure (Euc d))
    (hμ : ∀ u ∈ Icc (0 : ℝ) T, ∀ g : Euc d → ℝ, HRS.Whole.pair μ g = ∫ x, g x * C.ρ u x)
    (Mρ : ℝ) (hρmom : ∀ u ∈ Icc (0 : ℝ) T, Integrable (fun x => C.ρ u x * jbracket x ^ (2 * Pw)) ∧
      ∫ x, C.ρ u x * jbracket x ^ (2 * Pw) ≤ Mρ)
    (γ : ℝ → Measure (OscPath d m T)) (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {N : ℕ} (hN : 0 < N) {Ω : Type} {mΩ : MeasurableSpace Ω} (P : Measure Ω) [IsProbabilityMeasure P]
    (X : ℝ≥0 → Ω → EucConfig d N) {ℱ : Filtration ℝ mΩ} {W' : ℝ≥0 → Ω → (Fin N × Fin d) → ℝ}
    (hpart : S102Part C m T r Pw sQ μ hT P X ℱ W') {Φ : OscPath d m T → ℝ} (hΦ : MemCb 5 Φ) :
    S102Concl C m T sQ μ γ P X Φ (ContinuousLinearMap.id ℝ (OscPath d m T)) := by
  classical
  obtain ⟨hW, Mb, Vf, hdr, hMint, hY, hVf, hJc, hzW, hy, hzi, hmeas, hrep⟩ := hpart
  have hρint : ∀ u ∈ Icc (0 : ℝ) T, Integrable (C.ρ u) := fun u _ => by rw [hs.hstat u]; exact hs.hint
  have hρnn : ∀ u ∈ Icc (0 : ℝ) T, ∀ x, 0 ≤ C.ρ u x := fun u _ x => by rw [hs.hstat u]; exact hs.hnn x
  have hG : ∀ L : ℕ, S102GramInt C m hT L := fun L => s102_gramInt hs hT L
  set γ' : ℝ → Measure (OscPath d m T) := fun u => if u ∈ Icc (0 : ℝ) T then γ u else Measure.dirac 0 with hγ'def
  have hγγ' : ∀ u ∈ Icc (0 : ℝ) T, γ u = γ' u := fun u hu => by
    show γ u = if u ∈ Icc (0 : ℝ) T then γ u else Measure.dirac 0
    rw [if_pos hu]
  have hγ'p : ∀ u, IsProbabilityMeasure (γ' u) := fun u => by
    by_cases hu : u ∈ Icc (0 : ℝ) T
    · have := (hγ u hu).1.1
      rw [← hγγ' u hu]
      exact this.toIsProbabilityMeasure
    · show IsProbabilityMeasure (if u ∈ Icc (0 : ℝ) T then γ u else Measure.dirac 0)
      rw [if_neg hu]
      infer_instance
  have hγ' : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ' u) := fun u hu => by
    rw [← hγγ' u hu]
    exact hγ u hu
  have hLP : S102LipProj γ' (fun L => s102_Pj T hT L) :=
    s102_lipProj hd hP0 hr hP hs.hD hlin hT hs.hν Mρ hρint hρnn hρmom hG γ' hγ'p hγ'
  refine s102_G6 hd hP0 hr hP hs.hD hlin hT hs.hν Mρ hρint hρnn hρmom hG sQ μ γ hγ P X hΦ Mb hdr hMint hY Vf hVf
    hJc hzW hy (fun L => ?_)
  refine s102_Concl_congr hT.le sQ μ (fun u hu => (hγγ' u hu).symm) P X Φ _ ?_
  exact s102_cyl_concl hs hP hlin hT L sQ μ hμ γ' hγ'p hγ' hLP hN P X hW (hrep L) hΦ Mb hdr hMint hY Vf hVf hJc
    (hzi L) (hmeas L Φ hΦ).1 (hmeas L Φ hΦ).2
    (Eventually.of_forall fun ζ => by rw [s102_hE1]) hzW hy

end HRS.MS.R2Interp

end
