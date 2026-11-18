import HRS.MS.Fp81S21QwinUniform
import HRS.MS.S21F_S05
import HRS.MS.QsfAsm10
import HRS.MS.S21A_Orb
import HRS.MS.R2IidPathAux1
import HRS.MS.WsInitGAux6

set_option autoImplicit false
set_option linter.unusedSectionVars false
set_option maxHeartbeats 400000
noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

namespace HRS.Fp81.S21

open HRS (Euc cbNorm MemCb)
open HRS.Whole
open HRS.MS.R26T3
open HRS.MS.S21
open HRS.MS.R2WinOrbNL
open HRS.MS.R2WinErr

/-- The raw shifted qwin observation vector. It is deliberately distinct from the response vector. -/
def fp81s21_cosRecon_obsVec {p : Parameters} {δ : ℝ}
    (R : Trajectory p δ) (a : ℝ) (x : Euc p.d) : SeqL2 :=
  SeqL2.ofSeq (fun j => r26t3_qwin R a j x)

private theorem fp81s21_cosRecon_cos_eq (T : ℝ) (n : ℕ) (u : ℝ) :
    r26t3_cosine T n u = r2CosBasis T n u := by
  unfold r26t3_cosine r2CosBasis
  split_ifs with hn
  · simp [hn, one_div]
  · rfl

private theorem fp81s21_cosRecon_weight_eq (n : ℕ) :
    s11p_kap n = s21f_w n := by
  unfold HRS.Whole.s11p_kap HRS.MS.R26T3.s21f_w
  congr 1
  norm_num

private theorem fp81s21_cosRecon_shifted_scalar_of_data
    {p : Parameters} {δ : ℝ} (R : Trajectory p δ) (a : ℝ) (ha : 0 ≤ a)
    (hq : IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a))
    (hcont : ∀ α : MultiIndex p.d, ∀ x : Euc p.d,
      ContinuousOn (fun v => r26t3_U R 0 (a + v)
        (oscTestFun (wholeSpaceIndex p.d) α) x) (Set.Icc (0 : ℝ) p.T))
    (u : Set.Icc (0 : ℝ) p.T) (α : MultiIndex p.d) (x : Euc p.d) :
    HasSum (fun n => r26t3_cosine p.T n u * s21f_w n *
      r26t3_qwin R a ((r26t3_feature_enum p.d).symm (n, α)) x)
      (r26t3_U R 0 (a + (u : ℝ)) (oscTestFun (wholeSpaceIndex p.d) α) x) := by
  let σ := r26t3_feature_enum p.d
  let b : ℕ → ℝ := fun n => r26t3_qwin R a (σ.symm (n, α)) x
  have hinj : Function.Injective (fun n : ℕ => σ.symm (n, α)) := by
    intro n m h
    have hp : (n, α) = (m, α) := by simpa [σ] using congrArg σ h
    exact congrArg Prod.fst hp
  have hsub : Summable (fun n : ℕ => cbNorm (r26t3_J p.d)
      (r26t3_qwin R a (σ.symm (n, α)))) := hq.2.comp_injective hinj
  have hsub2 : Summable (fun n : ℕ => 2 * cbNorm (r26t3_J p.d)
      (r26t3_qwin R a (σ.symm (n, α)))) := hsub.mul_left 2
  have hb : Summable b := by
    apply Summable.of_norm_bounded hsub2
    intro n
    rw [Real.norm_eq_abs]
    have hsup := HRS.MS.Tc5.tc5_cb_sup_le (hq.1 (σ.symm (n, α))) x
    rw [Real.norm_eq_abs] at hsup
    have hnonneg := HRS.MS.Tc5.tc5_cb_nonneg (r26t3_J p.d)
      (r26t3_qwin R a (σ.symm (n, α)))
    change |r26t3_qwin R a (σ.symm (n, α)) x| ≤
      2 * cbNorm (r26t3_J p.d) (r26t3_qwin R a (σ.symm (n, α)))
    linarith
  have hcos : ∀ n v, r26t3_cosine p.T n v = r2CosBasis p.T n v :=
    fp81s21_cosRecon_cos_eq p.T
  have hpow (n : ℕ) : (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) =
      (1 + (n : ℝ) ^ 2) ^ (3 / 8 : ℝ) := by congr 1 <;> norm_num
  have hbn : ∀ n, b n = (1 + (n : ℝ) ^ 2) ^ ((3 : ℝ) / 8) *
      ∫ v in Set.Icc (0 : ℝ) p.T, r2CosBasis p.T n v *
        r26t3_U R 0 (a + v) (oscTestFun (wholeSpaceIndex p.d) α) x := by
    intro n
    simp [b, r26t3_qwin, σ, hcos, hpow]
  have hg : ContinuousOn (fun v : ℝ =>
      r26t3_U R 0 (a + v) (oscTestFun (wholeSpaceIndex p.d) α) x)
      (Set.Icc (0 : ℝ) p.T) := hcont α x
  have hexpand := HRS.Whole.s11p_cos_expand p.hT
    (fun v => r26t3_U R 0 (a + v) (oscTestFun (wholeSpaceIndex p.d) α) x)
    hg b hb hbn (u : ℝ) u.2
  have hterms : ∀ n, s11p_kap n * r2CosBasis p.T n (u : ℝ) * b n =
      r26t3_cosine p.T n u * s21f_w n *
        r26t3_qwin R a (σ.symm (n, α)) x := by
    intro n
    rw [fp81s21_cosRecon_weight_eq, hcos]
    simp only [b]
    ring
  simpa only [σ, hterms] using hexpand

/-- A single radius gives the shifted scalar cosine reconstruction and the raw observation
vector estimates. The envelope is selected before the shift and point. -/
theorem fp81s21_cosRecon_radius (p : Parameters) :
    ∃ δ26 : ℝ, 0 < δ26 ∧ δ26 ≤ 1 / 2 ∧
      ∀ δ : ℝ, 0 < δ → δ ≤ δ26 → ∀ R : Trajectory p δ,
        ∃ Cobs : ℝ, 0 ≤ Cobs ∧ ∀ a : ℝ, 0 ≤ a →
          IsSummableFeatureFamily (r26t3_J p.d) (r26t3_qwin R a) ∧
          featureSum (r26t3_J p.d) (r26t3_qwin R a) ≤
            Cobs * (∑' j : ℕ, r26t3_feature_weight p.d j) ∧
          (∀ x : Euc p.d,
            Memℓp (fun j => r26t3_qwin R a j x) 2 ∧
            (∀ j, SeqL2.coord (fp81s21_cosRecon_obsVec R a x) j = r26t3_qwin R a j x) ∧
            ‖fp81s21_cosRecon_obsVec R a x‖ ≤
              2 * featureSum (r26t3_J p.d) (r26t3_qwin R a)) ∧
          (∀ u : Set.Icc (0 : ℝ) p.T, ∀ α : MultiIndex p.d, ∀ x : Euc p.d,
            HasSum (fun n => r26t3_cosine p.T n u * s21f_w n *
              r26t3_qwin R a ((r26t3_feature_enum p.d).symm (n, α)) x)
              (r26t3_U R 0 (a + (u : ℝ)) (oscTestFun (wholeSpaceIndex p.d) α) x)) := by
  obtain ⟨δc, Co, co, hδc, hδchalf, _hco, hcommon⟩ := fp81s21_common_radius p
  obtain ⟨δf, hδf, hδfhalf, hfam⟩ := fp81s21_qwin_uniform p
  obtain ⟨δs, hδs, hδshalf, hsum⟩ := fp81s21_qwin_featureSum_uniform p
  let δ26 := min δc (min δf δs)
  have hδ26 : 0 < δ26 := by
    dsimp [δ26]
    exact lt_min hδc (lt_min hδf hδs)
  have hδ26half : δ26 ≤ 1 / 2 := by
    dsimp [δ26]
    exact (min_le_left _ _).trans hδchalf
  refine ⟨δ26, hδ26, hδ26half, fun δ hδ hδle R => ?_⟩
  have hδc' : δ ≤ δc := hδle.trans (show δ26 ≤ δc by exact min_le_left _ _)
  have hδf' : δ ≤ δf := hδle.trans (show δ26 ≤ δf by
    dsimp [δ26]; exact (min_le_right _ _).trans (min_le_left _ _))
  have hδs' : δ ≤ δs := hδle.trans (show δ26 ≤ δs by
    dsimp [δ26]; exact (min_le_right _ _).trans (min_le_right _ _))
  obtain ⟨Cobs, hCobs, hsumR⟩ := hsum δ hδ hδs' R
  obtain ⟨Cfam, hCfam, hfamR⟩ := hfam δ hδ hδf' R
  obtain ⟨horbit, _hhex, hterm, _hwindow⟩ := hcommon δ hδ hδc' R.ρβ R.thermal
  refine ⟨Cobs, hCobs, fun a ha => ?_⟩
  obtain ⟨hfamily, _hbound⟩ := hfamR a ha
  have hB := hsumR a ha
  have hT0 : 0 ≤ a + p.T := by linarith [ha, p.hT.le]
  have hOrbit : ∀ α : MultiIndex p.d, S104nOrbit (r26t3_coeff R)
      (oscTestFun (wholeSpaceIndex p.d) α) (a + p.T) := by
    intro α
    exact HRS.MS.R2WinErr.s104b_orbit_of_termRegGen hterm
      R.admissible R.resulting α (a + p.T) hT0
  have hcontGlobal : ∀ α : MultiIndex p.d, ∀ x : Euc p.d,
      ContinuousOn (fun t => propagatorW (r26t3_coeff R) 0 t
        (oscTestFun (wholeSpaceIndex p.d) α) x) (Set.Icc (0 : ℝ) (a + p.T)) := by
    intro α x
    exact HRS.MS.S21A.s21a_cont_of_diff hT0 (hOrbit α) x
  have hcont : ∀ α : MultiIndex p.d, ∀ x : Euc p.d,
      ContinuousOn (fun v => r26t3_U R 0 (a + v)
        (oscTestFun (wholeSpaceIndex p.d) α) x) (Set.Icc (0 : ℝ) p.T) := by
    intro α x
    have hc := hcontGlobal α x
    have hmap : Set.MapsTo (fun v : ℝ => a + v) (Set.Icc (0 : ℝ) p.T)
        (Set.Icc (0 : ℝ) (a + p.T)) := by
      intro v hv
      exact ⟨by linarith [ha, hv.1], by linarith [hv.2]⟩
    have hc' := hc.comp (continuousOn_const.add continuousOn_id) hmap
    simpa [Function.comp_def, r26t3_U, r26t3_coeff] using hc'
  refine ⟨hfamily, hB, ?_, ?_⟩
  · intro x
    have hmem : Memℓp (fun j => r26t3_qwin R a j x) 2 := by
      rw [memℓp_gen_iff (by norm_num)]
      have hcb0 : ∀ j, 0 ≤ cbNorm (r26t3_J p.d) (r26t3_qwin R a j) :=
        fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
      have hb : Summable (fun j => 2 * cbNorm (r26t3_J p.d) (r26t3_qwin R a j)) :=
        hfamily.2.mul_left 2
      have hsquare := S45.s45_summable_sq
        (fun j => mul_nonneg (by norm_num) (hcb0 j)) hb
      refine Summable.of_nonneg_of_le (fun j => by positivity) (fun j => ?_) hsquare
      simp only [ENNReal.toReal_ofNat, Real.rpow_two, Real.norm_eq_abs]
      have hsup := HRS.MS.Tc5.tc5_cb_sup_le (hfamily.1 j) x
      rw [Real.norm_eq_abs] at hsup
      have hpoint : |r26t3_qwin R a j x| ≤
          2 * cbNorm (r26t3_J p.d) (r26t3_qwin R a j) := by
        nlinarith [hcb0 j]
      exact pow_le_pow_left₀ (abs_nonneg _) hpoint 2
    have hcoord : ∀ j, SeqL2.coord (fp81s21_cosRecon_obsVec R a x) j =
        r26t3_qwin R a j x := by
      intro j
      exact S45.s45_coord_ofSeq hmem j
    have hbound : ∀ j, |SeqL2.coord (fp81s21_cosRecon_obsVec R a x) j| ≤
        2 * cbNorm (r26t3_J p.d) (r26t3_qwin R a j) := by
      intro j
      rw [hcoord j]
      have hsup := HRS.MS.Tc5.tc5_cb_sup_le (hfamily.1 j) x
      rw [Real.norm_eq_abs] at hsup
      nlinarith [HRS.MS.Tc5.tc5_cb_nonneg (r26t3_J p.d) (r26t3_qwin R a j)]
    have hnorm := S45.s45_norm_le_tsum (z := fp81s21_cosRecon_obsVec R a x)
      (hfamily.2.mul_left 2) hbound
    rw [tsum_mul_left] at hnorm
    exact ⟨hmem, hcoord, hnorm⟩
  · intro u α x
    exact fp81s21_cosRecon_shifted_scalar_of_data R a ha hfamily hcont u α x

/-- The synthesis operator is the normalized `s21gPhi`; its norm is bounded by `s11p_cJ`. -/
theorem fp81s21_cosRecon_synthesis_norm (p : Parameters) :
    ‖s21gPhi (r26t3_feature_enum p.d) p.hT
      ((wholeSpaceIndex p.d : ℕ) : ℝ)‖ ≤ s11p_cJ p.T :=
  s21gPhi_norm_le (r26t3_feature_enum p.d) p.hT _

#print axioms fp81s21_cosRecon_radius
#print axioms fp81s21_cosRecon_synthesis_norm

end HRS.Fp81.S21

end
