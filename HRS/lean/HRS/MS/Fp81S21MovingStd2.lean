import HRS.MS.Fp81S21MovingStd
import HRS.MS.ProClosureS111OrbitSummable
import HRS.MS.R2WinOrbAux11

/-!
# HRS S2.1(iii): moving trajectory orbit summability and standard data

The common-radius modewise orbit estimates and terminal-time regularity give the
`S101Data` input for the moving interpolation package.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set Classical
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R26T3 HRS.MS.CovMeas
open HRS.MS.R2WinOrb HRS.MS.R2WinOrbNL HRS.MS.R2WinErr

private theorem fp81s21_moving_orbit_summable
    (p : Parameters) {δ H Co co : ℝ} (R : Trajectory p δ)
    (hH : 0 < H)
    (hclaims : S103nOrbitClaims p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁) :
    R2OrbitSummable (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H
      (2 * p.d + 8) := by
  let C : WholeCoeff p.d := r26t3_coeff R
  let K : ℕ := 4 * p.d + 42
  let r : ℕ := 2 * p.d + 8
  let phi : MultiIndex p.d → Euc p.d → ℝ :=
    fun α => oscTestFun (wholeSpaceIndex p.d : ℝ) α
  have hrK : r + 1 ≤ K := by dsimp [r, K]; omega
  have hA : ∀ α : MultiIndex p.d, 0 ≤ |Co| * s103_b p.d α := by
    intro α
    exact mul_nonneg (abs_nonneg _) (s103_b_nonneg α)
  have hsup0 : ∀ α : MultiIndex p.d, ∀ t : ℝ, 0 ≤ t →
      R2OrbitSup C K t (phi α) (|Co| * s103_b p.d α) := by
    intro α t ht
    have hraw := hclaims R.ε R.ψ R.ρ R.admissible R.resulting α t ht
    have hmono : Co * s103_b p.d α ≤ |Co| * s103_b p.d α :=
      mul_le_mul_of_nonneg_right (le_abs_self Co) (s103_b_nonneg α)
    exact HRS.MS.R2WinOrb.s103_orbitSup_mono hraw.1 hmono
  have hsup1 : ∀ α : MultiIndex p.d, ∀ t : ℝ, 0 ≤ t →
      R2OrbitSup C K t (generatorW C t (phi α)) (|Co| * s103_b p.d α) := by
    intro α t ht
    have hraw := hclaims R.ε R.ψ R.ρ R.admissible R.resulting α t ht
    have hmono : Co * s103_b p.d α ≤ |Co| * s103_b p.d α :=
      mul_le_mul_of_nonneg_right (le_abs_self Co) (s103_b_nonneg α)
    exact HRS.MS.R2WinOrb.s103_orbitSup_mono hraw.2.2.1 hmono
  have horb : ∀ α : MultiIndex p.d, S104nOrbit C (phi α) H := by
    intro α
    exact s104b_orbit_of_termRegGen hterm R.admissible R.resulting α H hH.le
  have hU : ∀ α : MultiIndex p.d, ∀ v ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc v H,
      ContDiff ℝ K (propagatorW C v t (phi α)) ∧
      r2CbNormE K (propagatorW C v t (phi α)) ≤
        ENNReal.ofReal (|Co| * s103_b p.d α) := by
    intro α v hv t ht
    have htH : t ∈ Icc (0 : ℝ) H := ⟨hv.1.trans ht.1, ht.2⟩
    obtain ⟨f, hf⟩ := (horb α).ex0 t htH
    have hcanonical := HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩
    have hc := (hsup0 α t htH.1) (fun z => propagatorW C z t (phi α)) hcanonical
      v ⟨hv.1, ht.1⟩
    exact hc
  have hG : ∀ α : MultiIndex p.d, ∀ v ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc v H,
      ContDiff ℝ K (propagatorW C v t (generatorW C t (phi α))) ∧
      r2CbNormE K (propagatorW C v t (generatorW C t (phi α))) ≤
        ENNReal.ofReal (|Co| * s103_b p.d α) := by
    intro α v hv t ht
    have htH : t ∈ Icc (0 : ℝ) H := ⟨hv.1.trans ht.1, ht.2⟩
    obtain ⟨f, hf⟩ := (horb α).ex1 t htH
    have hcanonical := HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩
    have hc := (hsup1 α t htH.1)
      (fun z => propagatorW C z t (generatorW C t (phi α))) hcanonical
      v ⟨hv.1, ht.1⟩
    exact hc
  have hder : ∀ α : MultiIndex p.d, ∀ v ∈ Icc (0 : ℝ) H,
      ∀ t ∈ Icc v H, ∀ x,
      HasDerivWithinAt (fun z => propagatorW C v z (phi α) x)
        (propagatorW C v t (generatorW C t (phi α)) x) (Icc v H) t := by
    intro α v hv t ht x
    let Fa : ℝ → Euc p.d → ℝ := fun τ => propagatorW C v (v + τ) (phi α)
    let Fb : ℝ → Euc p.d → ℝ := fun τ =>
      propagatorW C v (v + τ) (generatorW C (v + τ) (phi α))
    have hvT : v ∈ Icc (0 : ℝ) H := hv
    have hτ : t - v ∈ Icc (0 : ℝ) (H - v) := by constructor <;> linarith [ht.1, ht.2]
    have hcdA : ∀ τ ∈ Icc (0 : ℝ) (H - v),
        ContDiff ℝ (0 : WithTop ℕ∞) (Fa τ) := by
      intro τ hτ'
      have hz : v + τ ∈ Icc (0 : ℝ) H := by constructor <;> linarith [hv.1, hτ'.1, hτ'.2]
      obtain ⟨f, hf⟩ := (horb α).ex0 (v + τ) hz
      have hc := (HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩).c2 v
        ⟨hv.1, by linarith [hτ'.1]⟩
      exact hc.of_le (by norm_num)
    have hcdB : ∀ τ ∈ Icc (0 : ℝ) (H - v),
        ContDiff ℝ (0 : WithTop ℕ∞) (Fb τ) := by
      intro τ hτ'
      have hz : v + τ ∈ Icc (0 : ℝ) H := by constructor <;> linarith [hv.1, hτ'.1, hτ'.2]
      obtain ⟨f, hf⟩ := (horb α).ex1 (v + τ) hz
      have hc := (HRS.MS.Fcau.propagatorW_isClassical ⟨f, hf⟩).c2 v
        ⟨hv.1, by linarith [hτ'.1]⟩
      exact hc.of_le (by norm_num)
    have hdiff : ∀ τ ∈ Icc (0 : ℝ) (H - v), ∀ ε : ℝ, 0 < ε →
        ∃ η : ℝ, 0 < η ∧ ∀ h : ℝ, h ≠ 0 → |h| < η →
          τ + h ∈ Icc (0 : ℝ) (H - v) → ∀ y : Euc p.d,
            ‖iteratedFDeriv ℝ 0
              (fun z => h⁻¹ * (Fa (τ + h) z - Fa τ z) - Fb τ z) y‖ ≤ ε := by
      intro τ hτ' ε hε
      obtain ⟨η, hη, hq⟩ := (horb α).diff01 v hvT τ hτ' ε hε
      refine ⟨η, hη, fun h hne hlt hτh y => ?_⟩
      exact hq h hne hlt hτh 0 (by norm_num) y
    have hderτ := HRS.MS.R2WinOrb.s103_hasDeriv_val hcdA hcdB hdiff x
      (t - v) hτ
    have hshift : HasDerivWithinAt (fun z : ℝ => z - v) 1 (Icc v H) t :=
      ((hasDerivAt_id t).sub_const v).hasDerivWithinAt
    have hmaps : MapsTo (fun z : ℝ => z - v) (Icc v H) (Icc (0 : ℝ) (H - v)) := by
      intro z hz
      constructor <;> linarith [hz.1, hz.2]
    have hcomp := hderτ.comp t hshift hmaps
    have hcomp' : HasDerivWithinAt (fun z => Fa (z - v) x)
        (Fb (t - v) x) (Icc v H) t := by
      simpa [Function.comp_def] using hcomp
    have heq : ∀ z ∈ Icc v H, Fa (z - v) x = propagatorW C v z (phi α) x := by
      intro z hz
      dsimp [Fa]
      congr 1
      ring
    have heq' : ∀ z ∈ Icc v H, propagatorW C v z (phi α) x = Fa (z - v) x := by
      intro z hz
      exact (heq z hz).symm
    have hactual := hcomp'.congr_of_mem heq' ht
    have htarget : Fb (t - v) x = propagatorW C v t (generatorW C t (phi α)) x := by
      dsimp [Fb]
      congr 2 <;> ring
    exact hactual.congr_deriv htarget
  have hEqDeriv : ∀ α : MultiIndex p.d, ∀ v ∈ Icc (0 : ℝ) H,
      ∀ t ∈ Icc v H, v < H →
      (fun x => derivWithin (fun z => propagatorW C v z (phi α) x) (Icc v H) t) =
        propagatorW C v t (generatorW C t (phi α)) := by
    intro α v hv t ht hvH
    funext x
    exact (hder α v hv t ht x).derivWithin (uniqueDiffOn_Icc hvH t ht)
  have hEqZero : ∀ α : MultiIndex p.d, ∀ v ∈ Icc (0 : ℝ) H,
      ∀ t ∈ Icc v H, v = H → t = H →
      (fun x => derivWithin (fun z => propagatorW C v z (phi α) x) (Icc v H) t) =
        (fun _ => (0 : ℝ)) := by
    intro α v hv t ht hvH htH
    funext x
    apply derivWithin_zero_of_not_accPt
    rw [hvH, htH, Icc_self, accPt_principal_iff_clusterPt]
    simp [ClusterPt]
  have hreg : ∀ α : MultiIndex p.d, ∀ v ∈ Icc (0 : ℝ) H, ∀ t ∈ Icc v H,
      ContDiff ℝ (r + 1) (propagatorW C v t (phi α)) ∧
      (∀ x, DifferentiableWithinAt ℝ
        (fun z => propagatorW C v z (phi α) x) (Icc v H) t) ∧
      ContDiff ℝ (r + 1)
        (fun x => derivWithin (fun z => propagatorW C v z (phi α) x) (Icc v H) t) := by
    intro α v hv t ht
    have htH : t ∈ Icc (0 : ℝ) H := ⟨hv.1.trans ht.1, ht.2⟩
    refine ⟨(hU α v hv t ht).1.of_le (by exact_mod_cast hrK), ?_, ?_⟩
    · intro x
      exact (hder α v hv t ht x).differentiableWithinAt
    · by_cases hvH : v < H
      · rw [hEqDeriv α v hv t ht hvH]
        exact (hG α v hv t ht).1.of_le (by exact_mod_cast hrK)
      · have hvEq : v = H := le_antisymm hv.2 (le_of_not_gt hvH)
        have htEq : t = H := le_antisymm ht.2 (hvEq ▸ ht.1)
        rw [hEqZero α v hv t ht hvEq htEq]
        exact contDiff_const
  have hDnorm : ∀ α : MultiIndex p.d, ∀ v ∈ Icc (0 : ℝ) H,
      ∀ t ∈ Icc v H,
      r2CbNormE K
        (fun x => derivWithin (fun z => propagatorW C v z (phi α) x) (Icc v H) t) ≤
        ENNReal.ofReal (|Co| * s103_b p.d α) := by
    intro α v hv t ht
    by_cases hvH : v < H
    · rw [hEqDeriv α v hv t ht hvH]
      exact (hG α v hv t ht).2
    · have hvEq : v = H := le_antisymm hv.2 (le_of_not_gt hvH)
      have htEq : t = H := le_antisymm ht.2 (hvEq ▸ ht.1)
      rw [hEqZero α v hv t ht hvEq htEq]
      simp [r2CbNormE]
  refine ⟨hreg, ?_⟩
  have hsq : Summable (fun α : MultiIndex p.d => (|Co| * s103_b p.d α) ^ 2) := by
    have hs := (HRS.MS.ProClosureS111.stationary_weight_square_summable
      (by have := p.hd; omega : 1 ≤ p.d)).mul_left (|Co| ^ 2)
    convert hs using 1 <;> ext α <;> simp [mul_pow]
  refine lt_of_le_of_lt (ENNReal.tsum_le_tsum fun α => ?_) (hsq.mul_left 2).tsum_ofReal_lt_top
  refine iSup_le fun v => iSup_le fun hv => iSup_le fun t => iSup_le fun ht => ?_
  have hu := (HRS.MS.ProClosureS111.weightedSup_zero_le_r2CbNormE hrK _).trans
    (hU α v hv t ht).2
  have hd := (HRS.MS.ProClosureS111.weightedSup_zero_le_r2CbNormE hrK _).trans
    (hDnorm α v hv t ht)
  calc _ ≤ ENNReal.ofReal (|Co| * s103_b p.d α) ^ 2 +
        ENNReal.ofReal (|Co| * s103_b p.d α) ^ 2 := by gcongr
    _ = ENNReal.ofReal (2 * (|Co| * s103_b p.d α) ^ 2) := by
      simp only [pow_two, ← ENNReal.ofReal_mul (hA α)]
      rw [← ENNReal.ofReal_add (mul_nonneg (hA α) (hA α))
        (mul_nonneg (hA α) (hA α))]
      congr 1
      ring

/-- The moving orbit claims and common-radius terminal regularity produce the missing
`S101Data` field. The coefficient weights are the square-summable modewise orbit envelope. -/
theorem fp81s21_moving_s101data_of_common
    (p : Parameters) {δ H Co co : ℝ} (R : Trajectory p δ)
    (hH : 0 < H)
    (hclaims : S103nOrbitClaims p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁ Co co)
    (hterm : S104bTermRegGen p.d p.s p.a p.β R.ρβ δ p.c₁ p.C₁) :
    ∃ c : MultiIndex p.d → ℝ,
      S101Data (r26t3_coeff R) (wholeSpaceIndex p.d : ℝ) H (2 * p.d + 8) c := by
  obtain ⟨c, hc⟩ := HRS.MS.CovMeas.s101_data_of_horb (by have := p.hd; omega)
    (fp81s21_moving_orbit_summable p R hH hclaims hterm)
  exact ⟨c, hc⟩

#print axioms fp81s21_moving_s101data_of_common

end HRS.Fp81.S21

end
