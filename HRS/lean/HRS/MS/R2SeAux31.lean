import HRS.MS.R2SeAux30

/-!
# S9.9 `r2_static_edgeworth`, packet 31: the limit of the quadratic term for a bounded pair kernel

Worker S99, namespace `S99`.  `s99_Bkernel`: for `h ∈ IsBoundedPairKernel s B`, every `ε > 0` and `N ≥ N₀(ε,h)`,
`|E[B_h ψ(W_N)] - ½ ∑_{l,q} Q_h(l,q) E[∂_q∂_lψ(G)]| ≤ ε`, uniformly in `ψ ∈ Bd 4`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section Bker

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

theorem s99_Bh_int {B : ℝ} {k : Euc d → Euc d → ℝ} (hk : IsBoundedPairKernel s B k) {N : ℕ} (hN : 2 ≤ N)
    {ψW : EucConfig d N → ℝ} (hψ : BM ψW) :
    Integrable (fun X : EucConfig d N => Bh d s a β γ N k X * ψW X) (S46.s46_P d s a β γ N) := by
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN).prob
  have hi := s99_pairE_int hd hs0 hs ha hβ hγ hT hS hk hN
  have h1 : Integrable (fun X : EucConfig d N => Bh d s a β γ N k X) (S46.s46_P d s a β γ N) := by
    unfold Bh
    exact (hi.sub (integrable_const _)).const_mul _
  obtain ⟨Cψ, hCψ⟩ := hψ.bd
  exact h1.mul_bdd hψ.meas.aestronglyMeasurable (Filter.Eventually.of_forall fun X => by
    rw [Real.norm_eq_abs]; exact hCψ X) |>.congr (Filter.Eventually.of_forall fun X => by simp)

set_option maxHeartbeats 2000000 in
theorem s99_Bkernel {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) γ (φ i) (φ j))) {B : ℝ} {h : Euc d → Euc d → ℝ}
    (hh : IsBoundedPairKernel s B h) :
    ∀ ε : ℝ, 0 < ε → ∃ N0 : ℕ, ∀ N : ℕ, N0 ≤ N → 2 ≤ N → ∀ {ψ : SeqL2 → ℝ}, Bd 4 ψ →
      |Bterm d s a β γ φ N h ψ - (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ h l q *
        ∫ z, pd (pd ψ l) q z ∂G| ≤ ε := by
  intro ε hε
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  set μ := thermalMeasure d s a β with hμdef
  obtain ⟨Ca, hj, hap, htail⟩ := s99_tail hd hs0 hs ha hβ hγ hT hS hh
  set b : ℕ → ℝ := fun j => cbNorm (J1 d) (φ j) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  set Sb : ℝ := ∑' j, b j with hSb
  have hFK0 := F.hK
  set Qc : ℝ := F.K ^ 2 * Sb ^ 2 + 1 with hQc
  have hQc0 : 0 < Qc := by positivity
  -- the `L¹(μ⊗μ)` convergence of the approximants
  have hconv := hap.converges 1 le_rfl (by simpa using hsd)
  obtain ⟨n1, hn1⟩ := eventually_atTop.1 (hconv.eventually (gt_mem_nhds (ENNReal.ofReal_pos.2
    (show 0 < ε / (3 * Qc) by positivity))))
  obtain ⟨n0, hn0⟩ := htail (ε / 3) (by positivity)
  set n := max n0 n1 with hn
  -- the finite-rank kernel
  obtain ⟨m, cc, u, hu, hjn⟩ := hap.finiteRank n
  obtain ⟨K, hK0, hFR⟩ := s99_FR hd hs0 hs ha hβ hγ hT hS hφ F hG hu
  refine ⟨max 2 (⌈(3 * K / ε) ^ 2⌉₊ + 1), fun N hN hN2 ψ hψ => ?_⟩
  have hN2' : 2 ≤ N := hN2
  haveI hP : IsProbabilityMeasure (S46.s46_P d s a β γ N) := (hS N hN2).prob
  haveI hν : IsProbabilityMeasure (S46.s46_nu d s a β γ N) := s99_nu_prob (by omega)
  have hN1 : 1 ≤ N := by omega
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  have hJ1 : 1 ≤ J1 d := by unfold J1; omega
  have hWc : Continuous (fun X : EucConfig d N => featureVec φ (S46.s46_nu d s a β γ N) X) :=
    (s99_W_contDiff hN1 hJ1 hφ).continuous
  set ψW : EucConfig d N → ℝ := fun X => ψ (featureVec φ (S46.s46_nu d s a β γ N) X) with hψW
  have hψBM : BM ψW := ⟨(hψ.1.continuous.comp hWc).measurable, 1, fun X => hψ.abs_le _⟩
  have hψWb : ∀ X, |ψW X| ≤ 1 := fun X => hψ.abs_le _
  have hhj : IsBoundedPairKernel s (Ca * B) (hj n) := s99_approx_bounded hd hs0 hs ha hβ hγ hT hS hap n
  -- term A: the tail
  have hA : |Bterm d s a β γ φ N h ψ - Bterm d s a β γ φ N (hj n) ψ| ≤ ε / 3 := by
    have hdiff : ∀ X, Bh d s a β γ N h X - Bh d s a β γ N (hj n) X =
        -(Bh d s a β γ N (fun x y => hj n x y - h x y) X) := fun X => by
      have := s99_Bh_sub hd hs0 hs ha hβ hγ hT hS hhj hh hN2' X
      linarith
    unfold Bterm
    rw [← integral_sub (s99_Bh_int hd hs0 hs ha hβ hγ hT hS hφ F hh hN2' hψBM)
      (s99_Bh_int hd hs0 hs ha hβ hγ hT hS hφ F hhj hN2' hψBM)]
    have e : (fun X : EucConfig d N => Bh d s a β γ N h X * ψW X - Bh d s a β γ N (hj n) X * ψW X) =
        fun X => -(Bh d s a β γ N (fun x y => hj n x y - h x y) X) * ψW X := funext fun X => by
      rw [← sub_mul, hdiff]
    simp only [hψW] at e ⊢
    rw [e, ← Real.norm_eq_abs]
    refine (norm_integral_le_integral_norm _).trans ?_
    have hkd := HRS.MS.R2Mt.s92_diff_kernel hh hap n
    have hBi : Integrable (fun X : EucConfig d N => |Bh d s a β γ N (fun x y => hj n x y - h x y) X|)
        (S46.s46_P d s a β γ N) := by
      have := s99_Bh_int hd hs0 hs ha hβ hγ hT hS hφ F hkd hN2' (BM.const (α := EucConfig d N) 1)
      simpa using this.abs
    refine le_trans ?_ (hn0 n (le_max_left _ _) N hN2')
    refine integral_mono_of_nonneg (Filter.Eventually.of_forall fun X => norm_nonneg _) hBi
      (Filter.Eventually.of_forall fun X => ?_)
    beta_reduce
    rw [Real.norm_eq_abs, abs_mul, abs_neg]
    calc |Bh d s a β γ N (fun x y => hj n x y - h x y) X| * |ψW X|
        ≤ |Bh d s a β γ N (fun x y => hj n x y - h x y) X| * 1 :=
          mul_le_mul_of_nonneg_left (hψWb X) (abs_nonneg _)
      _ = _ := mul_one _
  -- term B: the finite-rank kernel
  have hB : |Bterm d s a β γ φ N (hj n) ψ - (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ (hj n) l q *
      ∫ z, pd (pd ψ l) q z ∂G| ≤ ε / 3 := by
    have h1 := hFR N hN2' hψ
    rw [← hjn] at h1
    refine h1.trans ?_
    rw [div_le_iff₀ hsqN]
    have hx : (3 * K / ε) ^ 2 ≤ (N : ℝ) := by
      have h2 : (3 * K / ε) ^ 2 ≤ (⌈(3 * K / ε) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
      have h3 : ((⌈(3 * K / ε) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
        exact_mod_cast (le_max_right _ _).trans hN
      push_cast at h3
      linarith
    have h4 : 3 * K / ε ≤ Real.sqrt N := Real.le_sqrt_of_sq_le hx
    rw [div_le_iff₀ hε] at h4
    nlinarith
  -- term C: the coefficients
  have hC : |(1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ (hj n) l q * ∫ z, pd (pd ψ l) q z ∂G -
      (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ h l q * ∫ z, pd (pd ψ l) q z ∂G| ≤ ε / 3 := by
    have hwj := s99_kernel_wr8 hd hs0 hs ha hβ hγ hT hS hhj
    have hwh := s99_kernel_wr8 hd hs0 hs ha hβ hγ hT hS hh
    have hQ0 : ∀ l q, Qk d s a β γ φ (fun _ _ => (0 : ℝ)) l q = 0 := fun l q => by
      unfold Qk; simp
    have hzero : Integrable (Function.uncurry fun (_ _ : Euc d) => (0 : ℝ)) (μ.prod μ) := by
      exact integrable_const (0 : ℝ)
    have hQb : ∀ (k : Euc d → Euc d → ℝ), Integrable (Function.uncurry k) (μ.prod μ) → ∀ l q,
        |Qk d s a β γ φ k l q| ≤ F.K ^ 2 * (∫ p : Euc d × Euc d, |k p.1 p.2| ∂(μ.prod μ)) * (b l * b q) := by
      intro k hk l q
      have := s99_Qk_diff hd hs0 hs ha hβ hγ hT hS hφ F hk hzero l q
      rw [hQ0, sub_zero] at this
      simp only [sub_zero] at this
      refine this.trans (le_of_eq ?_)
      simp only [hbdef]; ring
    set Gm : ℕ → ℕ → ℝ := fun l q => ∫ z, pd (pd ψ l) q z ∂G with hGm
    have hGb : ∀ l q, |Gm l q| ≤ 1 := fun l q => by
      have := norm_integral_le_of_norm_le_const (μ := G) (f := pd (pd ψ l) q) (C := 1)
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]; exact ((hψ.pd l).pd q).abs_le z)
      simpa [Real.norm_eq_abs, hGm] using this
    -- the `L¹` distance of the kernels
    have hlt := hn1 n (le_max_right _ _)
    have hdm : Measurable fun p : Euc d × Euc d => hj n p.1 p.2 - h p.1 p.2 :=
      hhj.measurable.sub hh.measurable
    have hle : eLpNorm (fun p : Euc d × Euc d => hj n p.1 p.2 - h p.1 p.2) 1 (μ.prod μ) ≤
        ENNReal.ofReal (ε / (3 * Qc)) := by simpa using hlt.le
    obtain ⟨-, hδ⟩ := s99_l1_bound (by positivity) hdm.aestronglyMeasurable hle
    set δ : ℝ := ∫ p : Euc d × Euc d, |hj n p.1 p.2 - h p.1 p.2| ∂(μ.prod μ) with hδdef
    have hδ0 : 0 ≤ δ := integral_nonneg fun p => abs_nonneg _
    have hdiffQ := fun l q => s99_Qk_diff hd hs0 hs ha hβ hγ hT hS hφ F hwj.prod hwh.prod l q
    have hsub := s99_tsum2_sub hb0 hbs (A1 := F.K ^ 2 * (∫ p : Euc d × Euc d, |hj n p.1 p.2| ∂(μ.prod μ)))
      (A2 := F.K ^ 2 * (∫ p : Euc d × Euc d, |h p.1 p.2| ∂(μ.prod μ))) (D := F.K ^ 2 * δ)
      (f := fun l q => Qk d s a β γ φ (hj n) l q * Gm l q) (g := fun l q => Qk d s a β γ φ h l q * Gm l q)
      (fun l q => by
        rw [abs_mul]
        calc |Qk d s a β γ φ (hj n) l q| * |Gm l q| ≤ |Qk d s a β γ φ (hj n) l q| * 1 :=
              mul_le_mul_of_nonneg_left (hGb l q) (abs_nonneg _)
          _ ≤ _ := by rw [mul_one]; exact hQb _ hwj.prod l q)
      (fun l q => by
        rw [abs_mul]
        calc |Qk d s a β γ φ h l q| * |Gm l q| ≤ |Qk d s a β γ φ h l q| * 1 :=
              mul_le_mul_of_nonneg_left (hGb l q) (abs_nonneg _)
          _ ≤ _ := by rw [mul_one]; exact hQb _ hwh.prod l q)
      (fun l q => by
        rw [← sub_mul, abs_mul]
        calc |Qk d s a β γ φ (hj n) l q - Qk d s a β γ φ h l q| * |Gm l q|
            ≤ |Qk d s a β γ φ (hj n) l q - Qk d s a β γ φ h l q| * 1 :=
              mul_le_mul_of_nonneg_left (hGb l q) (abs_nonneg _)
          _ ≤ _ := by
              rw [mul_one]
              refine (hdiffQ l q).trans (le_of_eq ?_)
              simp only [hbdef, hδdef]; ring)
    rw [← mul_sub, abs_mul, abs_of_pos (by norm_num : (0 : ℝ) < 1 / 2)]
    have hS0 : 0 ≤ Sb := tsum_nonneg hb0
    calc 1 / 2 * |(∑' l, ∑' q, Qk d s a β γ φ (hj n) l q * Gm l q) -
          ∑' l, ∑' q, Qk d s a β γ φ h l q * Gm l q| ≤ 1 / 2 * (F.K ^ 2 * δ * Sb ^ 2) :=
          mul_le_mul_of_nonneg_left hsub (by norm_num)
      _ ≤ 1 / 2 * (Qc * (ε / (3 * Qc))) := by
          refine mul_le_mul_of_nonneg_left ?_ (by norm_num)
          have h1 : F.K ^ 2 * δ * Sb ^ 2 = (F.K ^ 2 * Sb ^ 2) * δ := by ring
          rw [h1]
          exact mul_le_mul (by simp only [hQc]; linarith) hδ (hδ0) hQc0.le
      _ ≤ ε / 3 := by
          have : Qc * (ε / (3 * Qc)) = ε / 3 := by field_simp
          rw [this]; linarith
  -- assembly
  calc |Bterm d s a β γ φ N h ψ - (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ h l q * ∫ z, pd (pd ψ l) q z ∂G|
      = |(Bterm d s a β γ φ N h ψ - Bterm d s a β γ φ N (hj n) ψ) +
          (Bterm d s a β γ φ N (hj n) ψ - (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ (hj n) l q *
            ∫ z, pd (pd ψ l) q z ∂G) +
          ((1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ (hj n) l q * ∫ z, pd (pd ψ l) q z ∂G -
            (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ h l q * ∫ z, pd (pd ψ l) q z ∂G)| := by
        congr 1; ring
    _ ≤ ε / 3 + ε / 3 + ε / 3 :=
        ((abs_add_le _ _).trans (add_le_add (abs_add_le _ _) le_rfl)).trans (add_le_add (add_le_add hA hB) hC)
    _ = ε := by ring

end Bker

end S99

end
