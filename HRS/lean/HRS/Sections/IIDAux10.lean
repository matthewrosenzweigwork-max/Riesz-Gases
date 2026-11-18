import HRS.Sections.IIDAux9

/-!
# IID helper chain, part 10: assembly of the i.i.d. comparison (first part of Proposition 5.9).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

section Assembly

open HRS.InitialDataAux

variable {d : ℕ}

lemma S_le_Z {m : ℝ} (hm : (d : ℝ) < 2 * m) (T : Finset (NonzeroLattice d)) :
    ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m)) ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) :=
  (summable_jp_rpow (d := d) m hm).sum_le_tsum T
    (fun k _ => Real.rpow_nonneg (Torus.jp_pos _).le _)

lemma Z_nonneg {m : ℝ} : 0 ≤ ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) :=
  tsum_nonneg fun k => Real.rpow_nonneg (Torus.jp_pos _).le _

lemma tailR_box_le {m : ℝ} {Ct : ℝ} {L : ℕ}
    (hCt : ∑' k : NonzeroLattice d, (if k ∈ boxT d L then 0 else Lattice.jp k.1 ^ (-(2 * m))) ≤
      Ct * (L : ℝ) ^ ((d : ℝ) - 2 * m)) :
    tailR d m (boxT d L) ≤ 2 * (Ct * (L : ℝ) ^ ((d : ℝ) - 2 * m)) := by
  unfold tailR
  have : ∀ k : NonzeroLattice d, (if k ∈ boxT d L then (0 : ℝ) else 2 * Lattice.jp k.1 ^ (-(2 * m))) =
      2 * (if k ∈ boxT d L then 0 else Lattice.jp k.1 ^ (-(2 * m))) := by
    intro k; split_ifs <;> simp
  simp_rw [this]
  rw [tsum_mul_left]
  linarith

/-- The three bounds, for one `N`, from the box rates. -/
theorem iid_comparison_aux (hd : 2 ≤ d) (m : ℝ) (hm : (d : ℝ) / 2 < m) (c : ℝ) (hc : 0 < c) :
    ∃ Cm : ℝ, 0 ≤ Cm ∧ ∀ ρ : Torus d → ℝ, IsProbDensity ρ → (∀ x, c ≤ ρ x) →
      ∀ γ : Measure (NegSobolev d m),
      IsCenteredGaussianWithCov m γ (iidCov (withDensityReal ρ)) →
      ∀ N : ℕ, 1 ≤ N →
        smoothDist 2 (law (Measure.pi fun _ : Fin N => withDensityReal ρ)
            (fun X : Config d N => etaE m X (withDensityReal ρ))) γ ≤
          Cm * (N : ℝ) ^ (-((m - (d : ℝ) / 2) / (2 * m))) ∧
        wassersteinE 1 (law (Measure.pi fun _ : Fin N => withDensityReal ρ)
            (fun X : Config d N => etaE m X (withDensityReal ρ))) γ ≤
          ENNReal.ofReal (Cm * (Real.log (Real.exp 1 * N) / Real.sqrt N) ^
            ((m - (d : ℝ) / 2) / (m + (d : ℝ) / 2))) ∧
        wassersteinE 2 (law (Measure.pi fun _ : Fin N => withDensityReal ρ)
            (fun X : Config d N => etaE m X (withDensityReal ρ))) γ ≤
          ENNReal.ofReal (Cm * ((Real.log (Real.exp 1 * N) / Real.sqrt N) ^
            ((m - (d : ℝ) / 2) / (m + (d : ℝ) / 2))) ^ ((1 : ℝ) / 3)) := by
  have hm2 : (d : ℝ) < 2 * m := by
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  set Z : ℝ := ∑' k : NonzeroLattice d, Lattice.jp k.1 ^ (-(2 * m)) with hZ
  have hZ0 : 0 ≤ Z := Z_nonneg
  obtain ⟨Ct, hCt0, hCt⟩ := tail_boxT_le (d := d) hm2
  obtain ⟨C2, hC2, h2⟩ := rate_smooth hd hm hZ0 hCt0
  obtain ⟨C1, hC1, h1⟩ := rate_W hd hm hZ0 hCt0
  set M : ℝ := 1632 * Z ^ 2 + 1 with hM
  have hM0 : 0 < M := by positivity
  set C3 : ℝ := Real.sqrt (2 * M ^ ((1 : ℝ) / 3)) * (C1 + 1) ^ ((1 : ℝ) / 3) with hC3
  refine ⟨max (max C2 (C1 + 1)) C3, by positivity, ?_⟩
  intro ρ hρ hρc γ hγ N hN
  haveI : IsProbabilityMeasure γ := by haveI := hγ.1.1; infer_instance
  haveI : IsProbabilityMeasure (withDensityReal ρ) := isProb_withDensityReal hρ
  have hη : (fun X : Config d N => etaE m X (withDensityReal ρ)) = fld m N (withDensityReal ρ) := rfl
  rw [hη]
  have hN0 : (0 : ℝ) < N := by exact_mod_cast hN
  have hN1 : (1 : ℝ) ≤ N := by exact_mod_cast hN
  obtain ⟨L, hL1, hL⟩ := h2 N hN
  obtain ⟨L', hL1', hL'⟩ := h1 N hN
  set e2 : ℝ := (N : ℝ) ^ (-((m - (d : ℝ) / 2) / (2 * m))) with he2
  set Λ : ℝ := Real.log (Real.exp 1 * N) with hΛ
  have hΛ1 : 1 ≤ Λ := by
    rw [hΛ, Real.log_mul (Real.exp_pos 1).ne' hN0.ne', Real.log_exp]
    have : 0 ≤ Real.log N := Real.log_nonneg hN1
    linarith
  set j : ℝ := (Λ / Real.sqrt N) ^ ((m - (d : ℝ) / 2) / (m + (d : ℝ) / 2)) with hj
  have hj0 : 0 < j := Real.rpow_pos_of_pos (div_pos (by linarith) (Real.sqrt_pos.2 hN0)) _
  have he20 : 0 ≤ e2 := Real.rpow_nonneg hN0.le _
  have hmax1 : C2 ≤ max (max C2 (C1 + 1)) C3 := (le_max_left _ _).trans (le_max_left _ _)
  have hmax2 : C1 + 1 ≤ max (max C2 (C1 + 1)) C3 := (le_max_right _ _).trans (le_max_left _ _)
  have hmax3 : C3 ≤ max (max C2 (C1 + 1)) C3 := le_max_right _ _
  have hCB' : CB ((Measure.pi fun _ : Fin N => withDensityReal ρ).map (fld m N (withDensityReal ρ))) γ
      ((C1 + 1) * j) M := by
    have hCB := CB_T hm2 hc hρ hρc hγ (boxT d L') hN hj0
    obtain ⟨π, hπ, hp, a, b⟩ := hCB
    refine ⟨π, hπ, hp, a.trans (ENNReal.ofReal_le_ofReal ?_), b.trans (ENNReal.ofReal_le_ofReal ?_)⟩
    · have hS := S_le_Z hm2 (boxT d L')
      have hcard : ((boxT d L').card : ℝ) ≤ (((2 * L' + 1) ^ d : ℕ) : ℝ) := by
        exact_mod_cast card_boxT_le L'
      have ht := tailR_box_le (hCt L' hL1')
      have hle : Real.sqrt (8 * (∑ k ∈ boxT d L', Lattice.jp k.1 ^ (-(2 * m))) / N) *
          (((boxT d L').card : ℝ) * Λ + 2) + 2 * Real.sqrt (tailR d m (boxT d L')) ≤
          Real.sqrt (8 * Z / N) * ((((2 * L' + 1) ^ d : ℕ) : ℝ) * Λ + 2) +
            2 * Real.sqrt (2 * (Ct * (L' : ℝ) ^ ((d : ℝ) - 2 * m))) := by
        gcongr
      nlinarith [hL', hle]
    · nlinarith [sq_nonneg Z]
  refine ⟨?_, ?_, ?_⟩
  · -- smooth distance
    have hd2 := iid_T_d2 hm2 hc hρ hρc hγ (boxT d L) hN
    refine hd2.trans ?_
    refine le_trans ?_ ((hL).trans (mul_le_mul_of_nonneg_right hmax1 he20))
    have hS := S_le_Z hm2 (boxT d L)
    have hcard : ((boxT d L).card : ℝ) ≤ (((2 * L + 1) ^ d : ℕ) : ℝ) := by
      exact_mod_cast card_boxT_le L
    have ht := tailR_box_le (hCt L hL1)
    gcongr
  · refine hCB'.w1.trans (ENNReal.ofReal_le_ofReal ?_)
    exact (mul_le_mul_of_nonneg_right hmax2 hj0.le)
  · refine (hCB'.w2 (by positivity) hM0).trans (ENNReal.ofReal_le_ofReal ?_)
    have hJ0 : 0 < (C1 + 1) * j := by positivity
    have hj3 : 0 ≤ j ^ ((1 : ℝ) / 3) := Real.rpow_nonneg hj0.le _
    have e1 : Real.sqrt (2 * M ^ ((1 : ℝ) / 3) * (((C1 + 1) * j) ^ ((1 : ℝ) / 3)) ^ 2) =
        C3 * j ^ ((1 : ℝ) / 3) := by
      rw [Real.sqrt_mul (by positivity), Real.sqrt_sq (by positivity), Real.mul_rpow (by positivity) hj0.le, hC3]
      ring
    rw [e1]
    exact mul_le_mul_of_nonneg_right hmax3 hj3


end Assembly

end HRS.IID
