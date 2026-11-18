import HRS.MS.R2InterpAux55
import HRS.MC.S7PIHC12

/-!
# S10.2 (worker S102), part 56 (packet F6, heat part): the `C^{1,2}` extension on a piece
-/

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators MatrixOrder Matrix

namespace HRS.MS.R2Interp

open HRS HRS.Whole HRS.MS.CovMeas HRS.MC.Sec7.PI

variable {d : ℕ} {C : WholeCoeff d} {m T : ℝ} {r : ℕ} {c : MultiIndex d → ℝ}

theorem s102_c12 (hs : S102Std C m T r c) (hT : 0 < T) (L : ℕ)
    (γ : ℝ → Measure (OscPath d m T)) (hγ : ∀ u ∈ Icc (0 : ℝ) T, IsR2FutureGaussian C m T u (γ u))
    {a b : ℝ} (ha : 0 ≤ a) (hab : a ≤ b) (hb : b ≤ T)
    (hno : ∀ k : Fin (s102_q d L), ¬ (a < s102_tk hT L k ∧ s102_tk hT L k < b))
    {G : EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ} (hG4 : MemCb 4 G) :
    ∃ f : ℝ → EuclideanSpace ℝ (Fin (s102_q d L)) → ℝ, HRS.IsC12On T Set.univ f ∧
      (∀ r ∈ Icc a b, f r = gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G r) ∧
      ∀ r ∈ Ioc a b, ∀ c, derivWithin (fun s => f s c) (Icc 0 T) r =
        -(1 / 2) * ∑ i, ∑ j, s102_rateM C m hT L r i j *
          iteratedFDeriv ℝ 2 (gaussHeat (s102_obsCov C m (s102_tauk hT L) (s102_alk L)) G r) c
            ![EuclideanSpace.single i 1, EuclideanSpace.single j 1] := by
  have hbT : b ∈ Icc (0 : ℝ) T := ⟨ha.trans hab, hb⟩
  have hGi := s102_gramInt hs hT L
  obtain ⟨f, hf, hfeq, hfd⟩ := HRS.MC.Sec7.S7PIH.s7_PIH_heat_c12_proof' (q := s102_q d L) a b T ha hab hb hT
    (s102_Ar C m hT L b) (s102_obsCov C m (s102_tauk hT L) (s102_alk L))
    (fun i j => by
      by_cases h : b ≤ min (s102_tk hT L i) (s102_tk hT L j)
      · have hsub : Icc a b ⊆ Icc 0 (min (s102_tk hT L i) (s102_tk hT L j)) := Icc_subset_Icc ha h
        have := ((s102_gram_cont hT L hs.hcls (C.ρ 0) hs.hint hs.hstat i j).mono hsub).const_mul (2 * C.ν)
        refine this.congr fun v _ => ?_
        simp only [s102_Ar, Matrix.of_apply, if_pos h]
      · simp only [s102_Ar, Matrix.of_apply, if_neg h, mul_zero]
        exact continuousOn_const)
    (fun v hv => s102_Ar_psd hs hT L hv ha hb)
    (s102_obs_law C (hγ b hbT) (s102_tauk hT L) (s102_alk L)).1
    (fun u hu i j => by
      have h := s102_obsCov_eq_rate hT L hGi (ha.trans hu.1) hu.2 hb i j
      rw [h]
      congr 1
      refine setIntegral_congr_fun measurableSet_Ioc fun v hv => ?_
      have := s102_Ar_eq_rate (C := C) (m := m) hT L (a := a) (b := b) (v := v) ⟨hu.1.trans_lt hv.1, hv.2⟩ hno
      show s102_rateM C m hT L v i j = s102_Ar C m hT L b v i j
      rw [this])
    G hG4
  refine ⟨f, hf, hfeq, fun r hr c => ?_⟩
  rw [hfd r ⟨hr.1.le, hr.2⟩ c]
  have := s102_Ar_eq_rate (C := C) (m := m) hT L (a := a) (b := b) (v := r) hr hno
  rw [this]

end HRS.MS.R2Interp

end
