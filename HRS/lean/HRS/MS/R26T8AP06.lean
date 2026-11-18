import HRS.MS.R26T8AP06d12
import HRS.MS.R26T8AP06d1
import HRS.MS.R26T8AP06d2

/-!
# S8.2 local Newton layer, packet T8A.P06: negative conormal orders, `C^k` extension across the diagonal
Assembly: `midPair F` is `C^k` off `z = 0` with continuous extensions of all joint jets (`r26t8a_joint_ext`), hence the restriction of a `C^k` function
(`r26t8a_extend_C`); `Fext x y = Phi ((x+y)/2, x-y)`.  Joint-jet bounds: `r26t8a_joint_bound_off` off the diagonal, extended by density and continuity;
the change of variables costs `|L|^j`.  Uniqueness: `r26t8a_unique_ext`.
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.R26T8A
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.Wad

theorem r26t8a_p06_exists_cutoff (d : ℕ) : ∃ chi : Euc d → ℝ, NewtonCutoff chi := by
  let b : ContDiffBump (0 : Euc d) := ⟨1, 2, one_pos, one_lt_two⟩
  refine ⟨fun z => (b z + b (-z)) / 2, ?_, ?_, ?_, ?_, ?_⟩
  · exact (b.contDiff.add (b.contDiff.comp contDiff_neg)).div_const 2
  · intro z; simp [add_comm]
  · intro z
    have h1 := b.nonneg' z
    have h2 := b.nonneg' (-z)
    have h3 := b.le_one (x := z)
    have h4 := b.le_one (x := -z)
    constructor <;> linarith
  · intro z hz
    have h1 : b z = 1 := b.one_of_mem_closedBall (by simpa using hz)
    have h2 : b (-z) = 1 := b.one_of_mem_closedBall (by simpa using hz)
    simp [h1, h2]
  · intro z hz
    have h1 : b z = 0 := b.zero_of_le_dist (by simpa using hz)
    have h2 : b (-z) = 0 := b.zero_of_le_dist (by simpa using hz)
    simp [h1, h2]

theorem r26t8a_p06_dense_U {d : ℕ} (hd : 1 ≤ d) : Dense {w : Euc d × Euc d | w.2 ≠ 0} := by
  obtain ⟨e, he⟩ := r26t8a_unit_vec hd
  have he0 : e ≠ 0 := norm_ne_zero_iff.1 (by rw [he]; norm_num)
  have hcover := r26t8a_halfspace_cover e he0
  have hHp : {w : Euc d × Euc d | 0 < inner ℝ w.2 e} ⊆ {w : Euc d × Euc d | w.2 ≠ 0} := fun w hw h0 => by
    have : inner ℝ w.2 e = 0 := by rw [show w.2 = 0 from h0]; simp
    exact absurd hw (by simp [this])
  have hHm : {w : Euc d × Euc d | inner ℝ w.2 e < 0} ⊆ {w : Euc d × Euc d | w.2 ≠ 0} := fun w hw h0 => by
    have : inner ℝ w.2 e = 0 := by rw [show w.2 = 0 from h0]; simp
    exact absurd hw (by simp [this])
  rw [dense_iff_closure_eq]
  apply Set.eq_univ_of_univ_subset
  rw [← hcover]
  exact Set.union_subset (closure_mono hHp) (closure_mono hHm)

theorem r26t8a_negative_conormal_extension {d : ℕ} (hd : 2≤d) (k b : ℕ)
    (M sigma : ℝ) (hM : 0≤M) (hsigma : sigma<0) (hk : (k:ℝ) < -sigma) :
    ∃ C : ℝ, 0≤C ∧ ∀ A : ℝ, 0≤A → ∀ F : Euc d → Euc d → ℝ,
      Conormal (k+1) b M sigma A F →
      ∃ Fext : Euc d → Euc d → ℝ,
        (∀ x y, x≠y → Fext x y=F x y) ∧ ContDiff ℝ k (Function.uncurry Fext) ∧
        (∀ G : Euc d → Euc d → ℝ, Continuous (Function.uncurry G) →
          (∀ x y, x≠y → G x y=F x y) → G=Fext) ∧
        ∀ j≤k, ∀ x y,
          ‖iteratedFDeriv ℝ j (Function.uncurry Fext) (x,y)‖≤C*A*HRS.MS.Phase2S82.pairWeight M x y := by
  obtain ⟨chi, hchi⟩ := r26t8a_p06_exists_cutoff d
  obtain ⟨e, he⟩ := r26t8a_unit_vec (show 1 ≤ d by omega)
  have he0 : e ≠ 0 := norm_ne_zero_iff.1 (by rw [he]; norm_num)
  set E0 : ℝ := 2 + r26t8a_p06_M (-sigma - k) b with hE0
  have hE00 : 0 ≤ E0 := by rw [hE0]; unfold r26t8a_p06_M; positivity
  set L : Euc d × Euc d →L[ℝ] Euc d × Euc d :=
    (((1 / 2 : ℝ) • (ContinuousLinearMap.fst ℝ (Euc d) (Euc d) + ContinuousLinearMap.snd ℝ (Euc d) (Euc d))).prod
      (ContinuousLinearMap.fst ℝ (Euc d) (Euc d) - ContinuousLinearMap.snd ℝ (Euc d) (Euc d))) with hL
  have hLapp : ∀ x y : Euc d, L (x, y) = ((1 / 2 : ℝ) • (x + y), x - y) := fun x y => by simp [hL]
  refine ⟨∑ j ∈ Finset.range (k + 1), 2 ^ j * E0 * ‖L‖ ^ j,
    Finset.sum_nonneg fun j _ => by positivity, fun A hA F hF => ?_⟩
  have hF1 := hF.1
  have hΦ : ContDiffOn ℝ (k : WithTop ℕ∞) (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) {w | w.2 ≠ 0} :=
    (r26t8a_midPair_contDiffOn (hF1.of_le (by exact_mod_cast Nat.le_succ k)))
  have hg : ∀ j ≤ k, ∃ g : Euc d × Euc d → ContinuousMultilinearMap ℝ (fun _ : Fin j => Euc d × Euc d) ℝ,
      Continuous g ∧ ∀ w : Euc d × Euc d, w.2 ≠ 0 →
        g w = iteratedFDeriv ℝ j (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) w :=
    fun j hj => r26t8a_joint_ext hd hchi k b M sigma hM hk hA hF j hj
  obtain ⟨Φe, hΦe, hΦeU⟩ := r26t8a_extend_C e he0 k _ hΦ hg
  set Fext : Euc d → Euc d → ℝ := fun x y => Φe ((1 / 2 : ℝ) • (x + y), x - y) with hFext
  have hFE : Function.uncurry Fext = Φe ∘ L := by
    funext p; simp [hFext, hL, Function.uncurry]
  have hFe_cd : ContDiff ℝ (k : WithTop ℕ∞) (Function.uncurry Fext) := by
    rw [hFE]; exact hΦe.comp L.contDiff
  have hoff : ∀ x y : Euc d, x ≠ y → Fext x y = F x y := fun x y hxy => by
    have hz : x - y ≠ 0 := sub_ne_zero.2 hxy
    have := hΦeU ((1 / 2 : ℝ) • (x + y), x - y) hz
    simp only [hFext]
    rw [this]
    show F ((1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • (x - y)) ((1 / 2 : ℝ) • (x + y) - (1 / 2 : ℝ) • (x - y)) = F x y
    rw [show (1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • (x - y) = x by module,
      show (1 / 2 : ℝ) • (x + y) - (1 / 2 : ℝ) • (x - y) = y by module]
  refine ⟨Fext, hoff, hFe_cd, fun G hG hGo => r26t8a_unique_ext (by omega) hFe_cd.continuous hG hoff hGo, ?_⟩
  intro j hj x y
  -- bound for the jets of Phi_ext on all of E x E
  have hpwc : Continuous (fun w : Euc d × Euc d => HRS.MS.Phase2S82.pairWeight M (w.1 + (1 / 2 : ℝ) • w.2) (w.1 - (1 / 2 : ℝ) • w.2)) := by
    unfold HRS.MS.Phase2S82.pairWeight
    have c1 : Continuous (fun w : Euc d × Euc d => jbracket (w.1 + (1 / 2 : ℝ) • w.2)) :=
      (r26t8a_jbracket_continuous (d := d)).comp (continuous_fst.add (continuous_snd.const_smul (1 / 2 : ℝ)))
    have c2 : Continuous (fun w : Euc d × Euc d => jbracket (w.1 - (1 / 2 : ℝ) • w.2)) :=
      (r26t8a_jbracket_continuous (d := d)).comp (continuous_fst.sub (continuous_snd.const_smul (1 / 2 : ℝ)))
    exact (c1.rpow_const (fun _ => Or.inr hM)).mul (c2.rpow_const (fun _ => Or.inr hM))
  have hpw0 : ∀ w : Euc d × Euc d, 0 ≤ HRS.MS.Phase2S82.pairWeight M (w.1 + (1 / 2 : ℝ) • w.2) (w.1 - (1 / 2 : ℝ) • w.2) :=
    fun w => by
      unfold HRS.MS.Phase2S82.pairWeight
      exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  have hbd : ∀ w : Euc d × Euc d, ‖iteratedFDeriv ℝ j Φe w‖ ≤
      2 ^ j * E0 * A * HRS.MS.Phase2S82.pairWeight M (w.1 + (1 / 2 : ℝ) • w.2) (w.1 - (1 / 2 : ℝ) • w.2) := by
    intro w
    have hclosed : IsClosed {w : Euc d × Euc d | ‖iteratedFDeriv ℝ j Φe w‖ ≤
        2 ^ j * E0 * A * HRS.MS.Phase2S82.pairWeight M (w.1 + (1 / 2 : ℝ) • w.2) (w.1 - (1 / 2 : ℝ) • w.2)} :=
      isClosed_le ((hΦe.continuous_iteratedFDeriv (by exact_mod_cast hj)).norm) (continuous_const.mul hpwc)
    have hsub : {w : Euc d × Euc d | w.2 ≠ 0} ⊆ {w : Euc d × Euc d | ‖iteratedFDeriv ℝ j Φe w‖ ≤
        2 ^ j * E0 * A * HRS.MS.Phase2S82.pairWeight M (w.1 + (1 / 2 : ℝ) • w.2) (w.1 - (1 / 2 : ℝ) • w.2)} := by
      intro w0 hw0
      have hopen : IsOpen {w : Euc d × Euc d | w.2 ≠ 0} := isOpen_ne.preimage continuous_snd
      have hev : Φe =ᶠ[𝓝 w0] (fun Yw : Euc d × Euc d => midPair F Yw.1 Yw.2) := by
        filter_upwards [hopen.mem_nhds hw0] with w hw using hΦeU w hw
      show ‖iteratedFDeriv ℝ j Φe w0‖ ≤ _
      rw [(hev.iteratedFDeriv ℝ j).self_of_nhds]
      have := r26t8a_joint_bound_off hchi k b M sigma hk hA hF j hj w0.1 w0.2 hw0
      simpa [mul_assoc] using this
    have hd' := r26t8a_p06_dense_U (show 1 ≤ d by omega)
    have := hclosed.closure_subset_iff.2 hsub
    rw [hd'.closure_eq] at this
    exact this (Set.mem_univ w)
  -- chain rule for the change of variables
  have hjk : (j : WithTop ℕ∞) ≤ (k : WithTop ℕ∞) := by exact_mod_cast hj
  have hcomp : ‖iteratedFDeriv ℝ j (Φe ∘ L) (x, y)‖ ≤ ‖iteratedFDeriv ℝ j Φe (L (x, y))‖ * ‖L‖ ^ j := by
    rw [ContinuousLinearMap.iteratedFDeriv_comp_right L hΦe (x, y) hjk]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    rw [Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  rw [hFE]
  refine hcomp.trans ?_
  have hw := hbd (L (x, y))
  rw [hLapp] at hw
  have hpwxy : HRS.MS.Phase2S82.pairWeight M ((1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • (x - y))
      ((1 / 2 : ℝ) • (x + y) - (1 / 2 : ℝ) • (x - y)) = HRS.MS.Phase2S82.pairWeight M x y := by
    rw [show (1 / 2 : ℝ) • (x + y) + (1 / 2 : ℝ) • (x - y) = x by module,
      show (1 / 2 : ℝ) • (x + y) - (1 / 2 : ℝ) • (x - y) = y by module]
  simp only [hpwxy] at hw
  have hsingle : 2 ^ j * E0 * ‖L‖ ^ j ≤ ∑ j ∈ Finset.range (k + 1), 2 ^ j * E0 * ‖L‖ ^ j :=
    Finset.single_le_sum (f := fun j : ℕ => 2 ^ j * E0 * ‖L‖ ^ j) (fun i _ => by positivity)
      (Finset.mem_range.2 (by omega))
  have hpwxy0 : 0 ≤ HRS.MS.Phase2S82.pairWeight M x y := by
    unfold HRS.MS.Phase2S82.pairWeight
    exact mul_nonneg (Real.rpow_nonneg (s83_jb_pos _).le _) (Real.rpow_nonneg (s83_jb_pos _).le _)
  calc ‖iteratedFDeriv ℝ j Φe (L (x, y))‖ * ‖L‖ ^ j ≤
        (2 ^ j * E0 * A * HRS.MS.Phase2S82.pairWeight M x y) * ‖L‖ ^ j :=
        mul_le_mul_of_nonneg_right (by simpa [hLapp] using hw) (by positivity)
    _ = (2 ^ j * E0 * ‖L‖ ^ j) * A * HRS.MS.Phase2S82.pairWeight M x y := by ring
    _ ≤ _ := by
        have := mul_le_mul_of_nonneg_right hsingle (mul_nonneg hA hpwxy0)
        nlinarith [this]

end HRS.MS.R26T8A
