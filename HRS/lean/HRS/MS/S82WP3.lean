import HRS.MS.S82WP2

/-!
# S8.2 A05 (S82W), part 3: jets of the centered pair statistic off collisions
-/

set_option autoImplicit false
noncomputable section
open MeasureTheory Filter Topology ProbabilityTheory
open scoped ENNReal NNReal BigOperators ContDiff RealInnerProductSpace

namespace HRS.MS.S82W
open HRS HRS.Whole HRS.MS.Phase2S82 HRS.MS.S82U

section affine
variable {E : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]

lemma w_affine_jets (S : E → ℝ) {U : Set E} (hU : IsOpen U) (hS : ContDiffOn ℝ 2 S U) (k c : ℝ) {x : E}
    (hx : x ∈ U) :
    ‖fderiv ℝ (fun y => k * S y - c) x‖ ≤ |k| * ‖fderiv ℝ S x‖ ∧
    ‖fderiv ℝ (fderiv ℝ (fun y => k * S y - c)) x‖ ≤ |k| * ‖fderiv ℝ (fderiv ℝ S) x‖ := by
  have hd : ∀ y ∈ U, DifferentiableAt ℝ S y := fun y hy =>
    (hS.differentiableOn (by norm_num)).differentiableAt (hU.mem_nhds hy)
  have hev : fderiv ℝ (fun y => k * S y - c) =ᶠ[𝓝 x] fun y => k • fderiv ℝ S y := by
    filter_upwards [hU.mem_nhds hx] with y hy
    rw [fderiv_sub_const, fderiv_const_mul (hd y hy)]
  have hdd : DifferentiableAt ℝ (fderiv ℝ S) x :=
    ((hS.contDiffAt (hU.mem_nhds hx)).fderiv_right (m := 1) (by norm_num)).differentiableAt one_ne_zero
  constructor
  · rw [hev.self_of_nhds]
    have := norm_smul k (fderiv ℝ S x)
    exact (le_of_eq (by simpa [Real.norm_eq_abs] using this))
  · have e : fderiv ℝ (fun y => k • fderiv ℝ S y) x = k • fderiv ℝ (fderiv ℝ S) x :=
      fderiv_const_smul hdd k
    rw [hev.fderiv_eq, e]
    have := ContinuousLinearMap.opNorm_smul_le k (fderiv ℝ (fderiv ℝ S) x)
    simpa [Real.norm_eq_abs] using this

end affine

section pairstat
variable {d N : ℕ}

def wLij (d N : ℕ) (i j : Fin N) : EucConfig d N →L[ℝ] Euc d × Euc d :=
  (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) i).prod
    (ContinuousLinearMap.proj (R := ℝ) (φ := fun _ : Fin N => Euc d) j)

lemma wLij_apply (i j : Fin N) (X : EucConfig d N) : wLij d N i j X = (X i, X j) := rfl

lemma wLij_norm_le (i j : Fin N) : ‖wLij d N i j‖ ≤ 1 := by
  refine ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun X => ?_
  rw [wLij_apply, one_mul, Prod.norm_def]
  exact max_le (norm_le_pi_norm X i) (norm_le_pi_norm X j)

/-- the size controlling the jets of the `(i,j)` term -/
def wBq (M A : ℝ) (i j : Fin N) (X : EucConfig d N) : ℝ :=
  A * Phase2S82.pairWeight M (X i) (X j) * (1 + smallRadius (X i) (X j) ^ (-criticalS d))

lemma wBq_nonneg (M : ℝ) {A : ℝ} (hA : 0 ≤ A) (i j : Fin N) (X : EucConfig d N) : 0 ≤ wBq M A i j X := by
  unfold wBq
  exact mul_nonneg (mul_nonneg hA (w_pw_nonneg M _ _)) (by
    have := Real.rpow_nonneg (le_trans zero_le_one (le_refl 1)) (-criticalS d)
    have : 0 ≤ smallRadius (X i) (X j) ^ (-criticalS d) := by
      unfold smallRadius
      exact Real.rpow_nonneg (le_min zero_le_one (norm_nonneg _)) _
    linarith)

theorem w_pairstat_jets (hd : 2 ≤ d) {a beta : ℝ} {rho : Euc d → ℝ} {M A : ℝ} {f : Euc d → ℝ}
    {Q : Euc d → Euc d → ℝ} (hQ : PairCorrector a beta rho M A f Q) (hA : 0 ≤ A) (c : ℝ) :
    ContDiffOn ℝ 2 (fun X : EucConfig d N => Phase2S82.pairStatistic Q X - c) (eucCollisionSet d N)ᶜ ∧
    ∀ X : EucConfig d N, X ∉ eucCollisionSet d N →
      |Phase2S82.pairStatistic Q X - c| + ‖fderiv ℝ (fun Y => Phase2S82.pairStatistic Q Y - c) X‖ +
        ‖iteratedFDeriv ℝ 2 (fun Y => Phase2S82.pairStatistic Q Y - c) X‖ ≤
      5 * (N : ℝ) ^ (-(3 / 2 : ℝ)) * ∑ i, ∑ j ∈ Finset.univ.erase i, wBq M A i j X + |c| := by
  set k : ℝ := (N : ℝ) ^ (-(3 / 2 : ℝ)) with hk
  have hk0 : 0 ≤ k := Real.rpow_nonneg (Nat.cast_nonneg N) _
  have hU : IsOpen {p : Euc d × Euc d | p.1 ≠ p.2} := isOpen_ne_fun continuous_fst continuous_snd
  have hQ2 : ContDiffOn ℝ 2 (Function.uncurry Q) {p : Euc d × Euc d | p.1 ≠ p.2} :=
    hQ.smooth.of_le (by norm_num)
  have hterm : ∀ i j : Fin N, i ≠ j → ContDiffOn ℝ 2 (fun Y : EucConfig d N => Function.uncurry Q (wLij d N i j Y))
      (eucCollisionSet d N)ᶜ := by
    intro i j hij
    refine hQ2.comp (wLij d N i j).contDiff.contDiffOn fun Y hY => ?_
    exact fun h => hY ⟨i, j, hij, h⟩
  have hrow : ∀ i : Fin N, ContDiffOn ℝ 2 (fun Y : EucConfig d N =>
      ∑ j ∈ Finset.univ.erase i, Function.uncurry Q (wLij d N i j Y)) (eucCollisionSet d N)ᶜ := fun i =>
    ContDiffOn.sum fun j hj => hterm i j (Finset.ne_of_mem_erase hj).symm
  have hS : ContDiffOn ℝ 2 (fun Y : EucConfig d N => ∑ i, ∑ j ∈ Finset.univ.erase i,
      Function.uncurry Q (wLij d N i j Y)) (eucCollisionSet d N)ᶜ := ContDiffOn.sum fun i _ => hrow i
  have hF : (fun X : EucConfig d N => Phase2S82.pairStatistic Q X - c) =
      fun X => k * (∑ i, ∑ j ∈ Finset.univ.erase i, Function.uncurry Q (wLij d N i j X)) - c := by
    funext X; simp only [Phase2S82.pairStatistic, Phase2S82.pairSum, hk, wLij_apply, Function.uncurry]
  rw [hF]
  refine ⟨(contDiffOn_const.mul hS).sub contDiffOn_const, fun X hX => ?_⟩
  have hne : ∀ i j : Fin N, j ∈ Finset.univ.erase i → X i ≠ X j := fun i j hj h =>
    hX ⟨i, j, (Finset.ne_of_mem_erase hj).symm, h⟩
  -- jets of each term
  have htj : ∀ i j : Fin N, j ∈ Finset.univ.erase i →
      |Function.uncurry Q (wLij d N i j X)| ≤ 2 * wBq M A i j X ∧
      ‖fderiv ℝ (fun Y => Function.uncurry Q (wLij d N i j Y)) X‖ ≤ 2 * wBq M A i j X ∧
      ‖fderiv ℝ (fderiv ℝ (fun Y => Function.uncurry Q (wLij d N i j Y))) X‖ ≤ wBq M A i j X := by
    intro i j hij
    have hxy : X i ≠ X j := hne i j hij
    obtain ⟨b0, b1, b2⟩ := w_Qjets hd hQ hA hxy
    have hmem : wLij d N i j X ∈ {p : Euc d × Euc d | p.1 ≠ p.2} := hxy
    obtain ⟨l1, l2⟩ := w_lin_jets (Function.uncurry Q) hU hQ2 (wLij d N i j) hmem
    have hn := wLij_norm_le (d := d) i j
    have hn0 := norm_nonneg (wLij d N i j)
    have n1 := norm_nonneg (fderiv ℝ (Function.uncurry Q) (wLij d N i j X))
    have n2 := norm_nonneg (fderiv ℝ (fderiv ℝ (Function.uncurry Q)) (wLij d N i j X))
    rw [wLij_apply] at l1 l2 ⊢
    refine ⟨b0, ?_, ?_⟩
    · refine l1.trans ?_
      calc _ ≤ ‖fderiv ℝ (Function.uncurry Q) (X i, X j)‖ * 1 := mul_le_mul_of_nonneg_left hn n1
        _ ≤ _ := by rw [mul_one]; exact b1
    · refine l2.trans ?_
      have : ‖wLij d N i j‖ ^ 2 ≤ 1 := by nlinarith
      calc _ ≤ ‖fderiv ℝ (fderiv ℝ (Function.uncurry Q)) (X i, X j)‖ * 1 := mul_le_mul_of_nonneg_left this n2
        _ ≤ _ := by rw [mul_one]; exact b2
  have hUo : IsOpen (eucCollisionSet d N)ᶜ := u4_D_open
  -- jets of the double sum
  have hin : ∀ i : Fin N,
      ‖fderiv ℝ (fun Y : EucConfig d N => ∑ j ∈ Finset.univ.erase i, Function.uncurry Q (wLij d N i j Y)) X‖ ≤
        ∑ j ∈ Finset.univ.erase i, 2 * wBq M A i j X ∧
      ‖fderiv ℝ (fderiv ℝ (fun Y : EucConfig d N => ∑ j ∈ Finset.univ.erase i,
        Function.uncurry Q (wLij d N i j Y))) X‖ ≤ ∑ j ∈ Finset.univ.erase i, wBq M A i j X := by
    intro i
    obtain ⟨s1, s2⟩ := w_sum_jets (Finset.univ.erase i)
      (fun j Y => Function.uncurry Q (wLij d N i j Y)) hUo
      (fun j hj => hterm i j (Finset.ne_of_mem_erase hj).symm) hX
    exact ⟨s1.trans (Finset.sum_le_sum fun j hj => (htj i j hj).2.1),
      s2.trans (Finset.sum_le_sum fun j hj => (htj i j hj).2.2)⟩
  obtain ⟨o1, o2⟩ := w_sum_jets (Finset.univ : Finset (Fin N))
    (fun i Y => ∑ j ∈ Finset.univ.erase i, Function.uncurry Q (wLij d N i j Y)) hUo (fun i _ => hrow i) hX
  have hT1 : ‖fderiv ℝ (fun Y : EucConfig d N => ∑ i, ∑ j ∈ Finset.univ.erase i,
      Function.uncurry Q (wLij d N i j Y)) X‖ ≤ 2 * ∑ i, ∑ j ∈ Finset.univ.erase i, wBq M A i j X := by
    refine o1.trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (hin i).1.trans (le_of_eq ?_)
    rw [Finset.mul_sum]
  have hT2 : ‖fderiv ℝ (fderiv ℝ (fun Y : EucConfig d N => ∑ i, ∑ j ∈ Finset.univ.erase i,
      Function.uncurry Q (wLij d N i j Y))) X‖ ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, wBq M A i j X :=
    o2.trans (Finset.sum_le_sum fun i _ => (hin i).2)
  have hval : |∑ i, ∑ j ∈ Finset.univ.erase i, Function.uncurry Q (wLij d N i j X)| ≤
      2 * ∑ i, ∑ j ∈ Finset.univ.erase i, wBq M A i j X := by
    refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun i _ => (Finset.abs_sum_le_sum_abs _ _).trans ?_
    rw [Finset.mul_sum]
    exact Finset.sum_le_sum fun j hj => (htj i j hj).1
  obtain ⟨a1, a2⟩ := w_affine_jets _ hUo hS k c hX
  rw [abs_of_nonneg hk0] at a1 a2
  rw [w_j2]
  have hB0 : 0 ≤ ∑ i, ∑ j ∈ Finset.univ.erase i, wBq M A i j X :=
    Finset.sum_nonneg fun i _ => Finset.sum_nonneg fun j _ => wBq_nonneg M hA i j X
  have hv : |k * (∑ i, ∑ j ∈ Finset.univ.erase i, Function.uncurry Q (wLij d N i j X)) - c| ≤
      k * (2 * ∑ i, ∑ j ∈ Finset.univ.erase i, wBq M A i j X) + |c| := by
    refine (abs_sub _ _).trans ?_
    rw [abs_mul, abs_of_nonneg hk0]
    exact add_le_add (mul_le_mul_of_nonneg_left hval hk0) le_rfl
  have m1 := mul_le_mul_of_nonneg_left hT1 hk0
  have m2 := mul_le_mul_of_nonneg_left hT2 hk0
  have hF' : Phase2S82.pairStatistic Q X - c =
      k * (∑ i, ∑ j ∈ Finset.univ.erase i, Function.uncurry Q (wLij d N i j X)) - c := congrFun hF X
  rw [hF']
  linarith

end pairstat

end HRS.MS.S82W
