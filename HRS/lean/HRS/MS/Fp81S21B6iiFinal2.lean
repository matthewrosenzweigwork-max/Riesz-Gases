import HRS.MS.Fp81S21B6iiFinal
import HRS.MS.Fp81S21B6iiEmp4
import HRS.MS.Fp81S21B6iiWeighted
import HRS.MS.Fp81S21B6iiDrift3
import HRS.MS.Fp81S21EmpFour
import HRS.MS.Fp81S21WeightedGenUncond2
import HRS.MS.Fp81S21MovingAllInputs
import HRS.MS.Fp81S21HilbertMart5
import HRS.MS.Fp81S21MartBdg3
import HRS.MS.ProClosureS111WeightedChart

set_option autoImplicit false
set_option maxHeartbeats 400000
noncomputable section
open Classical MeasureTheory Filter Set
open scoped ENNReal RealInnerProductSpace
namespace HRS.Fp81.S21
open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.R26T6 HRS.MS.ProClosureS111

/-- The B8 drift and the B6-ii vector drift are definitionally identical. -/
theorem fp81s21_b6ii_empFourDrift_eq_vectorDrift
    {Ω : Type*} [MeasurableSpace Ω] (N : ℕ)
    (L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff)
    (qs qB0 : ℝ → Ω → r26t6_Coeff) :
    fp81s21_empFour_drift N L qs qB0 =
      fp81s21_b6ii_vectorDrift N L qs qB0 := by
  rfl

/-- The unconditional simultaneous-time B6-ii equation for the physical
particle. The charts are selected once, and the representatives and the B6-i
martingale are selected before the shift and terminal horizon. -/
theorem fp81s21_b6ii (p : Parameters) :
    ∃ CL : ℝ, 0 ≤ CL ∧
    ∃ Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4),
    ∃ E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2),
    ∃ δ0 : ℝ, 0 < δ0 ∧ δ0 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ0 → ∀ R : Trajectory p δ,
        ∃ M2 M6 Cm : ℝ, 0 ≤ M2 ∧ 0 ≤ M6 ∧ 0 ≤ Cm ∧
        ∃ L : ℝ → r26t6_Coeff →L[ℝ] r26t6_Coeff,
          Measurable (fun z : ℝ × r26t6_Coeff => L z.1 z.2) ∧
          (∀ u : ℝ, 0 ≤ u → ‖L u‖ ≤ CL) ∧
          ∀ N : ℕ, 2 ≤ N → ∀ A : Particle R N,
            ∃ Fp : FilteredParticle A,
            ∃ qsη qB0 : ℝ → A.Ω → r26t6_Coeff,
            ∃ m : ℝ → A.Ω → r26t6_Coeff,
              fp81s21_MomentRep Es A.P
                (fp81s21_particleEmpField R N A) qsη M2 ∧
              fp81s21_MomentRep E A.P
                (fp81s21_particleQuadRawField R N A) qB0 M2 ∧
              (Measurable (Function.uncurry qsη) ∧
                Measurable (Function.uncurry qB0) ∧
                fp81s21_Six A.P qsη M6 ∧
                fp81s21_Six A.P qB0 M6) ∧
              Measurable (Function.uncurry m) ∧
              IsHilbertItoIntegral A.P Fp.ℱ Fp.Wc
                (fp81s21_b6i_gradientNoise p E A Fp) m ∧
              (∀ T : ℝ, IsHSIntegrand A.P Fp.ℱ T
                (fp81s21_b6i_gradientNoise p E A Fp)) ∧
              (∀ H : ℝ, 0 < H → ∀ a : ℝ, 0 ≤ a →
                ∀ s t : Icc (0 : ℝ) H,
                  MemLp (fun ω => m (a + t) ω - m (a + s) ω) 4 A.P ∧
                  (∫ ω, ‖m (a + t) ω - m (a + s) ω‖ ^ 4 ∂A.P) ≤
                    Cm * |(t : ℝ) - s| ^ 2) ∧
              ∀ a : ℝ, 0 ≤ a → ∀ H : ℝ, 0 < H →
                ∀ᵐ ω ∂A.P,
                  IntegrableOn
                    (fun v => fp81s21_b6ii_vectorDrift N L qsη qB0 (a + v) ω)
                    (Icc 0 H) ∧
                  ∀ s t : Icc (0 : ℝ) H, s ≤ t →
                    fp81s21_gaussian_chartEmbed p Es E (qsη (a + t) ω) -
                        fp81s21_gaussian_chartEmbed p Es E (qsη (a + s) ω) =
                      (∫ v in Icc (s : ℝ) (t : ℝ),
                        fp81s21_b6ii_vectorDrift N L qsη qB0 (a + v) ω) +
                        m (a + t) ω - m (a + s) ω := by
  obtain ⟨δB3, hδB3, hδB3half, CL, hCL, hB3⟩ :=
    fp81s21_b3_contract p
  have hdpos : 0 < p.d :=
    Nat.lt_of_lt_of_le (by decide : 0 < 2) p.hd
  have hPEs : (p.d : ℝ) < 2 * ((p.d : ℝ) + 4) := by
    have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    linarith
  have hPE : (p.d : ℝ) < 2 * ((p.d : ℝ) + 2) := by
    have hd : (0 : ℝ) ≤ p.d := Nat.cast_nonneg _
    linarith
  let Es : r26t6_WeightedChart p.d (2 * p.d + 6) ((p.d : ℝ) + 4) :=
    Classical.choice (physical_weighted_chart hdpos hPEs)
  let E : r26t6_WeightedChart p.d (2 * p.d + 8) ((p.d : ℝ) + 2) :=
    Classical.choice (physical_weighted_chart hdpos hPE)
  obtain ⟨δEmp, hδEmp, hδEmphalf, hEmp⟩ :=
    fp81s21_particleCoeffMoments_embedded_common p Es
  obtain ⟨δRef, hδRef, hδRefhalf, hRef⟩ :=
    fp81s21_emp_reference_data p Es
  obtain ⟨δB7, hδB7, hδB7half, hB7All⟩ :=
    fp81s21_b7_shiftedFourthIncrements p E
  obtain ⟨δMoving, hδMoving, hδMovinghalf, hMoving⟩ :=
    fp81s21_moving_inputs_all p
  let δ0 : ℝ := min δEmp (min δRef (min δB3 (min δB7 δMoving)))
  have hδ0 : 0 < δ0 := by
    dsimp [δ0]
    exact lt_min hδEmp (lt_min hδRef (lt_min hδB3 (lt_min hδB7 hδMoving)))
  have hδ0half : δ0 ≤ 1 / 2 := by
    dsimp [δ0]
    exact (min_le_left _ _).trans hδEmphalf
  have hδ0Emp : δ0 ≤ δEmp := by
    dsimp [δ0]
    exact min_le_left _ _
  have hδ0Ref : δ0 ≤ δRef := by
    dsimp [δ0]
    exact (min_le_right _ _).trans (min_le_left _ _)
  have hδ0B3 : δ0 ≤ δB3 := by
    dsimp [δ0]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans (min_le_left _ _))
  have hδ0B7 : δ0 ≤ δB7 := by
    dsimp [δ0]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_left _ _)))
  have hδ0Moving : δ0 ≤ δMoving := by
    dsimp [δ0]
    exact (min_le_right _ _).trans ((min_le_right _ _).trans
      ((min_le_right _ _).trans (min_le_right _ _)))
  refine ⟨CL, hCL, Es, E, δ0, hδ0, hδ0half, ?_⟩
  intro δ hδ hδle R
  have hδEmp' : δ ≤ δEmp := hδle.trans hδ0Emp
  have hδRef' : δ ≤ δRef := hδle.trans hδ0Ref
  have hδB3' : δ ≤ δB3 := hδle.trans hδ0B3
  have hδB7' : δ ≤ δB7 := hδle.trans hδ0B7
  have hδMoving' : δ ≤ δMoving := hδle.trans hδ0Moving
  obtain ⟨M2, M6, hM2, hM6, hEmpNA⟩ := hEmp δ hδ hδEmp' R
  obtain ⟨L, hL, hLbound, hB3all⟩ := hB3 δ hδ hδB3' R Es E
  obtain ⟨Cm, hCm, hB7NA⟩ := hB7All δ hδ hδB7' R
  have hgen : ∀ u : ℝ, 0 ≤ u → ∀ f : Euc p.d → ℝ,
      IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f →
      IsR2WeightedTest (2 * p.d + 6) ((p.d : ℝ) + 4)
        (generatorW (r26t3_coeff R) u f) := by
    intro u hu f hf
    exact (hB3all u hu 0 f hf).1
  have hadj : ∀ u : ℝ, 0 ≤ u → ∀ z f,
      IsR2WeightedTest (2 * p.d + 8) ((p.d : ℝ) + 2) f →
      fp81s21_chartAction E (L u z) f =
        fp81s21_chartAction Es z (generatorW (r26t3_coeff R) u f) := by
    intro u hu z f hf
    exact (hB3all u hu z f hf).2.2
  refine ⟨M2, M6, Cm, hM2, hM6, hCm, L, hL, hLbound, ?_⟩
  intro N hN A
  let Fp : FilteredParticle A := Classical.choice (r26t3_filtered_particle A)
  have hηmem : fp81s21_particleEmpField R N A ∈
      ({fp81s21_particleEmpField R N A,
        fp81s21_particleQuadRawField R N A,
        fp81s21_particleQuadField R N A} :
        Set (ℝ → A.Ω → (Euc p.d → ℝ) → ℝ)) := by simp
  obtain ⟨qsη, hηrep, hηsix, hηembed, hηembedSix, hηfirst, hηcommonFun⟩ :=
    hEmpNA E N hN A (fp81s21_particleEmpField R N A) hηmem
  have hcommon := (hηcommonFun rfl).2
  have hBmem : fp81s21_particleQuadRawField R N A ∈
      ({fp81s21_particleEmpField R N A,
        fp81s21_particleQuadRawField R N A,
        fp81s21_particleQuadField R N A} :
        Set (ℝ → A.Ω → (Euc p.d → ℝ) → ℝ)) := by simp
  obtain ⟨qsB, hBEsRep, hBsix, hBrep, hBembedSix, hBfirst, hBcommon⟩ :=
    hEmpNA E N hN A (fp81s21_particleQuadRawField R N A) hBmem
  let qB0 : ℝ → A.Ω → r26t6_Coeff :=
    fun u ω => fp81s21_gaussian_chartEmbed p Es E (qsB u ω)
  obtain ⟨μ, hμ, hmom, hμmeas⟩ := hRef δ hδ hδRef' R
  have hmomR : ∀ u : ℝ, 0 ≤ u →
      Integrable (fun x : Euc p.d => jbracket x ^ ((p.d : ℝ) + 4))
        (r26t3_mu R u) := by
    intro u hu
    rw [← hμ u hu]
    exact hmom u
  have hU3 := fp81s21_emp_MomentRep_weighted_action p R N hN A Es hηrep hmomR
  obtain ⟨m, hmdata, hB7m⟩ := hB7NA N hN A Fp
  rcases hmdata with ⟨hm, hZ, hIto, hHM, hzero, hformula, hcoord⟩
  have hB7out : ∀ H : ℝ, 0 < H → ∀ a : ℝ, 0 ≤ a →
      ∀ s t : Icc (0 : ℝ) H,
        MemLp (fun ω => m (a + t) ω - m (a + s) ω) 4 A.P ∧
        (∫ ω, ‖m (a + t) ω - m (a + s) ω‖ ^ 4 ∂A.P) ≤
          Cm * |(t : ℝ) - s| ^ 2 := by
    intro H hH a ha s t
    simpa using hB7m H hH a ha (s : ℝ) (t : ℝ) s.property t.property
  have hδhalf : δ ≤ 1 / 2 := hδle.trans hδ0half
  refine ⟨Fp, qsη, qB0, m, hηrep, ?_, ?_, hm, hIto, hZ, hB7out, ?_⟩
  · exact hBrep
  · exact ⟨hηrep.1, hBrep.1, hηsix, hBembedSix⟩
  · intro a ha H hH
    have hb : 0 ≤ a + H := add_nonneg ha hH.le
    obtain ⟨c, hstd, hphysicalAll⟩ :=
      hMoving δ hδ hδMoving' R (a + H) hb
    have hphysical := hphysicalAll N hN A
    have hU2 := fp81s21_b6ii_raw_hU2 p R hN A Fp E a H ha hH
      hδ hδhalf hphysical
    have hU5 := fp81s21_b6ii_product_drift R N hN A Es E qsη qB0
      M2 CL a H L hL hM2 hLbound hδ hδhalf ha hH hηrep hBrep hgen hadj hU3
    exact fp81s21_b6ii_vector_assembly p R N A Fp Es E qsη qB0 m L
      hcommon hIto hZ a H ha hH hU2 hU5.1 hU5.2

#print axioms fp81s21_b6ii
#print axioms fp81s21_b6ii_empFourDrift_eq_vectorDrift
end HRS.Fp81.S21
end
