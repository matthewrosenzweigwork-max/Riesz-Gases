import HRS.MS.R2SeAux40

/-!
# S9.9 `r2_static_edgeworth`, packet 41: the identification of the limit (per `j`, and in total)

Worker S99, namespace `S99`.  `s99_jident`: for each `j` and `f` in the Stein class,
`∑_k Alim(f,(j,k)) + ½ ∑_{lq} Q_j(l,q) T_{jlq} = -½ ∑_{km} κ_{jkm} T_{jkm}`; `s99_limit_ident`: the sum over `j`.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

section Ident2

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

theorem s99_cc_bd (j k m : ℕ) :
    |cc d s a β γ F (j, k) m| ≤ (Kw d γ F * (cbNorm (J1 d) (φ j) * cbNorm (J1 d) (φ k))) *
      (F.K * cbNorm (J1 d) (φ m)) := by
  have hw := s99_wF_cb hd hγ hφ.1 F j k
  have hwbd : ∀ x, |wF F j k x| ≤ Kw d γ F * (cbNorm (J1 d) (φ j) * cbNorm (J1 d) (φ k)) := fun x => by
    have := s99_norm_iter_le_cb hw.1 (Nat.zero_le _) x
    rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
    refine this.trans (hw.2.trans (le_of_eq ?_))
    unfold Kw; ring
  exact s99_kap_bd hd hs0 hs ha hβ hγ hT hS hφ F hw.1.1.continuous.measurable hwbd m

theorem s99_Alim_bd {G : Measure SeqL2} [IsProbabilityMeasure G] {f : SeqL2 → ℝ} (hf : SteinCl f)
    (p : ℕ × ℕ) :
    |Alim d s a β γ F G f p| ≤ Kw d γ F * F.K * (∑' j, cbNorm (J1 d) (φ j)) *
      (cbNorm (J1 d) (φ p.1) * cbNorm (J1 d) (φ p.2)) := by
  have hb0 : ∀ j, 0 ≤ cbNorm (J1 d) (φ j) := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable fun j => cbNorm (J1 d) (φ j) := hφ.2
  have hGb : ∀ m, |∫ z, pd (pd (pd f p.1) p.2) m z ∂G| ≤ 1 := fun m => by
    have := norm_integral_le_of_norm_le_const (μ := G) (f := pd (pd (pd f p.1) p.2) m) (C := 1)
      (Filter.Eventually.of_forall fun z => by
        rw [Real.norm_eq_abs]; exact (((hf.pd p.1).pd p.2).pd m).abs_le z)
    simpa [Real.norm_eq_abs] using this
  unfold Alim
  rw [abs_neg]
  have hg : HasSum (fun m => Kw d γ F * (cbNorm (J1 d) (φ p.1) * cbNorm (J1 d) (φ p.2)) * F.K *
      cbNorm (J1 d) (φ m)) (Kw d γ F * (cbNorm (J1 d) (φ p.1) * cbNorm (J1 d) (φ p.2)) * F.K *
      ∑' j, cbNorm (J1 d) (φ j)) := hbs.hasSum.mul_left _
  have := tsum_of_norm_bounded hg (f := fun m => cc d s a β γ F p m * ∫ z, pd (pd (pd f p.1) p.2) m z ∂G)
    (fun m => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |cc d s a β γ F p m| * |∫ z, pd (pd (pd f p.1) p.2) m z ∂G| ≤
          ((Kw d γ F * (cbNorm (J1 d) (φ p.1) * cbNorm (J1 d) (φ p.2))) * (F.K * cbNorm (J1 d) (φ m))) * 1 :=
            mul_le_mul (s99_cc_bd hd hs0 hs ha hβ hγ hT hS hφ F p.1 p.2 m) (hGb m) (abs_nonneg _)
              (by have := hb0 m; have := hb0 p.1; have := hb0 p.2; have := s99_Kw_nonneg F hγ; have := F.hK; positivity)
        _ = _ := by ring)
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  ring

set_option maxHeartbeats 2000000 in
theorem s99_jident {G : Measure SeqL2} [IsProbabilityMeasure G] {f : SeqL2 → ℝ} (hf : SteinCl f) (j : ℕ) :
    (∑' k, Alim d s a β γ F G f (j, k)) + (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ
        (commutatorKernel d s (gradient (F.χ j))) l q * T3 G f j l q =
      -(1 / 2) * ∑' k, ∑' m, kap3 d s a β γ φ j k m * T3 G f j k m := by
  obtain ⟨Bj, hj⟩ := s99_hj_bdd hd hs0 hs ha hβ hγ hT hS hφ F j
  set b : ℕ → ℝ := fun j => cbNorm (J1 d) (φ j) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  have hbb : Summable fun p : ℕ × ℕ => b p.1 * b p.2 :=
    Summable.mul_of_nonneg (f := b) (g := b) hbs hbs (fun j => hb0 j) (fun j => hb0 j)
  have hFK0 := F.hK
  have hKw0 := s99_Kw_nonneg F hγ
  set Ij : ℝ := ∫ p : Euc d × Euc d, |commutatorKernel d s (gradient (F.χ j)) p.1 p.2|
    ∂((thermalMeasure d s a β).prod (thermalMeasure d s a β)) with hIj
  have hIj0 : 0 ≤ Ij := integral_nonneg fun p => abs_nonneg _
  set A : ℕ × ℕ → ℝ := fun p => cc d s a β γ F (j, p.1) p.2 * T3 G f j p.1 p.2 with hA
  set Q : ℕ × ℕ → ℝ := fun p => Qk d s a β γ φ (commutatorKernel d s (gradient (F.χ j))) p.1 p.2 *
    T3 G f j p.1 p.2 with hQ
  set K' : ℕ × ℕ → ℝ := fun p => kap3 d s a β γ φ j p.1 p.2 * T3 G f j p.1 p.2 with hK'
  have hAs : Summable A := Summable.of_norm_bounded (hbb.mul_left (Kw d γ F * b j * F.K)) (fun p => by
    rw [Real.norm_eq_abs, hA]; simp only
    rw [abs_mul]
    calc |cc d s a β γ F (j, p.1) p.2| * |T3 G f j p.1 p.2| ≤
        ((Kw d γ F * (b j * b p.1)) * (F.K * b p.2)) * 1 :=
          mul_le_mul (s99_cc_bd hd hs0 hs ha hβ hγ hT hS hφ F j p.1 p.2) (T3_abs_le G hf j p.1 p.2)
            (abs_nonneg _) (by have := hb0 p.2; have := hb0 p.1; have := hb0 j; positivity)
      _ = _ := by ring)
  have hQs : Summable Q := Summable.of_norm_bounded (hbb.mul_left (F.K ^ 2 * Ij)) (fun p => by
    rw [Real.norm_eq_abs, hQ]; simp only
    rw [abs_mul]
    calc |Qk d s a β γ φ (commutatorKernel d s (gradient (F.χ j))) p.1 p.2| * |T3 G f j p.1 p.2| ≤
        (F.K ^ 2 * Ij * (b p.1 * b p.2)) * 1 :=
          mul_le_mul (s99_Qk_bd hd hs0 hs ha hβ hγ hT hS hφ F hj p.1 p.2) (T3_abs_le G hf j p.1 p.2)
            (abs_nonneg _) (by have := hb0 p.2; have := hb0 p.1; positivity)
      _ = _ := by ring)
  have hKs : Summable K' := Summable.of_norm_bounded (hbb.mul_left (F.K ^ 3 * b j)) (fun p => by
    rw [Real.norm_eq_abs, hK']; simp only
    rw [abs_mul]
    calc |kap3 d s a β γ φ j p.1 p.2| * |T3 G f j p.1 p.2| ≤
        (F.K ^ 3 * (b j * b p.1 * b p.2)) * 1 :=
          mul_le_mul (s99_kap3_bd hd hs0 hs ha hβ hγ hT hS hφ F j p.1 p.2) (T3_abs_le G hf j p.1 p.2)
            (abs_nonneg _) (by have := hb0 p.2; have := hb0 p.1; have := hb0 j; positivity)
      _ = _ := by ring)
  -- the pointwise identity
  have hpt : ∀ p : ℕ × ℕ, K' p = A p + A (p.2, p.1) - Q p := by
    intro p
    obtain ⟨k, m⟩ := p
    simp only [hA, hQ, hK']
    have hc := s99_cancel hd hs0 hs ha hβ hγ hT hS hφ F j k m
    have hcc : kap3 d s a β γ φ j k m = cc d s a β γ F (j, k) m + cc d s a β γ F (j, m) k -
        Qk d s a β γ φ (commutatorKernel d s (gradient (F.χ j))) k m := by
      unfold kap3; rw [← hc]
    rw [hcc, T3_symm G hf j m k]
    ring
  have hswap : ∑' p : ℕ × ℕ, A (p.2, p.1) = ∑' p : ℕ × ℕ, A p :=
    (Equiv.prodComm ℕ ℕ).tsum_eq A
  have hAsw : Summable fun p : ℕ × ℕ => A (p.2, p.1) := (Equiv.summable_iff (Equiv.prodComm ℕ ℕ)).2 hAs
  have hKsum : ∑' p, K' p = 2 * ∑' p, A p - ∑' p, Q p := by
    have : (fun p : ℕ × ℕ => K' p) = fun p => A p + A (p.2, p.1) - Q p := funext hpt
    rw [this, (hAs.add hAsw).tsum_sub hQs, hAs.tsum_add hAsw, hswap]
    ring
  -- translate the iterated sums
  have e1 : ∑' k, Alim d s a β γ F G f (j, k) = -∑' p, A p := by
    rw [hAs.tsum_prod, ← tsum_neg]
    refine tsum_congr fun k => ?_
    unfold Alim
    simp only [hA, T3]
  have e2 : ∑' l, ∑' q, Qk d s a β γ φ (commutatorKernel d s (gradient (F.χ j))) l q * T3 G f j l q =
      ∑' p, Q p := by
    rw [hQs.tsum_prod]
  have e3 : ∑' k, ∑' m, kap3 d s a β γ φ j k m * T3 G f j k m = ∑' p, K' p := by
    rw [hKs.tsum_prod]
  rw [e1, e2, e3, hKsum]
  ring

theorem s99_U_bd {G : Measure SeqL2} [IsProbabilityMeasure G] {f : SeqL2 → ℝ} (hf : SteinCl f) (j : ℕ) :
    |∑' k, ∑' m, kap3 d s a β γ φ j k m * T3 G f j k m| ≤
      F.K ^ 3 * cbNorm (J1 d) (φ j) * (∑' i, cbNorm (J1 d) (φ i)) ^ 2 := by
  set b : ℕ → ℝ := fun j => cbNorm (J1 d) (φ j) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  have hFK0 := F.hK
  have hSb0 : 0 ≤ ∑' i, b i := tsum_nonneg hb0
  have hin : ∀ k, |∑' m, kap3 d s a β γ φ j k m * T3 G f j k m| ≤ F.K ^ 3 * b j * b k * (∑' i, b i) := by
    intro k
    have hg : HasSum (fun m => F.K ^ 3 * b j * b k * b m) (F.K ^ 3 * b j * b k * ∑' i, b i) :=
      hbs.hasSum.mul_left _
    have := tsum_of_norm_bounded hg (f := fun m => kap3 d s a β γ φ j k m * T3 G f j k m) (fun m => by
      rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
      calc |kap3 d s a β γ φ j k m| * |T3 G f j k m| ≤ (F.K ^ 3 * (b j * b k * b m)) * 1 :=
            mul_le_mul (s99_kap3_bd hd hs0 hs ha hβ hγ hT hS hφ F j k m) (T3_abs_le G hf j k m)
              (abs_nonneg _) (by have := hb0 j; have := hb0 k; have := hb0 m; positivity)
        _ = _ := by ring)
    rwa [Real.norm_eq_abs] at this
  have hg2 : HasSum (fun k => F.K ^ 3 * b j * (∑' i, b i) * b k) (F.K ^ 3 * b j * (∑' i, b i) * ∑' i, b i) :=
    hbs.hasSum.mul_left _
  have := tsum_of_norm_bounded hg2 (f := fun k => ∑' m, kap3 d s a β γ φ j k m * T3 G f j k m) (fun k => by
    rw [Real.norm_eq_abs]
    exact (hin k).trans (le_of_eq (by ring)))
  rw [Real.norm_eq_abs] at this
  refine this.trans (le_of_eq ?_)
  ring

theorem s99_limit_ident {G : Measure SeqL2} [IsProbabilityMeasure G] {f : SeqL2 → ℝ} (hf : SteinCl f) :
    (∑' p : ℕ × ℕ, Alim d s a β γ F G f p) + (∑' j, (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ
        (commutatorKernel d s (gradient (F.χ j))) l q * ∫ z, pd (pd (pd f j) l) q z ∂G) =
      -(1 / 2) * ∑' j, ∑' k, ∑' m, kap3 d s a β γ φ j k m * T3 G f j k m := by
  show (∑' p : ℕ × ℕ, Alim d s a β γ F G f p) + (∑' j, (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ
        (commutatorKernel d s (gradient (F.χ j))) l q * T3 G f j l q) =
      -(1 / 2) * ∑' j, ∑' k, ∑' m, kap3 d s a β γ φ j k m * T3 G f j k m
  set b : ℕ → ℝ := fun j => cbNorm (J1 d) (φ j) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  have hbb : Summable fun p : ℕ × ℕ => b p.1 * b p.2 :=
    Summable.mul_of_nonneg (f := b) (g := b) hbs hbs (fun j => hb0 j) (fun j => hb0 j)
  have hAs : Summable fun p : ℕ × ℕ => Alim d s a β γ F G f p :=
    Summable.of_norm_bounded (hbb.mul_left (Kw d γ F * F.K * ∑' j, b j)) (fun p => by
      rw [Real.norm_eq_abs]
      exact (s99_Alim_bd hd hs0 hs ha hβ hγ hT hS hφ F hf p).trans (le_of_eq (by simp only [hbdef])))
  have hSA : Summable fun j => ∑' k, Alim d s a β γ F G f (j, k) := hAs.prod
  have hU : Summable fun j => ∑' k, ∑' m, kap3 d s a β γ φ j k m * T3 G f j k m :=
    Summable.of_norm_bounded (hbs.mul_left (F.K ^ 3 * (∑' i, b i) ^ 2)) (fun j => by
      rw [Real.norm_eq_abs]
      exact (s99_U_bd hd hs0 hs ha hβ hγ hT hS hφ F hf j).trans (le_of_eq (by simp only [hbdef]; ring)))
  have hid : ∀ j, (∑' k, Alim d s a β γ F G f (j, k)) + (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ
        (commutatorKernel d s (gradient (F.χ j))) l q * T3 G f j l q =
      -(1 / 2) * ∑' k, ∑' m, kap3 d s a β γ φ j k m * T3 G f j k m := fun j =>
    s99_jident hd hs0 hs ha hβ hγ hT hS hφ F hf j
  have hB : ∀ j, (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ (commutatorKernel d s (gradient (F.χ j))) l q *
      T3 G f j l q =
      -(1 / 2) * (∑' k, ∑' m, kap3 d s a β γ φ j k m * T3 G f j k m) - ∑' k, Alim d s a β γ F G f (j, k) := by
    intro j
    have := hid j
    linarith
  have hSB : Summable fun j => (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ
      (commutatorKernel d s (gradient (F.χ j))) l q * T3 G f j l q := by
    have : (fun j => (1 / 2) * ∑' l, ∑' q, Qk d s a β γ φ
        (commutatorKernel d s (gradient (F.χ j))) l q * T3 G f j l q) =
        fun j => -(1 / 2) * (∑' k, ∑' m, kap3 d s a β γ φ j k m * T3 G f j k m) -
          ∑' k, Alim d s a β γ F G f (j, k) := funext hB
    rw [this]
    exact (hU.mul_left _).sub hSA
  rw [hAs.tsum_prod, ← hSA.tsum_add hSB]
  simp_rw [hid]
  rw [tsum_mul_left]

end Ident2

end S99

end
