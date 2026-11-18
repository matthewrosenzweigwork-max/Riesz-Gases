import HRS.MS.R2SeAux37

/-!
# S9.9 `r2_static_edgeworth`, packet 38: the uniform limits of the linear and quadratic series

Worker S99, namespace `S99`.  Tannery over the index sets of the two series of the decomposition `s99_D1`:

* `s99_ULimA`: `∑_{p=(j,k)} Aterm_N(f,p) → ∑_p Alim(f,p)` uniformly over the Stein class;
* `s99_ULimB`: `∑_j E[B_j ∂_jf(W_N)] → ∑_j ½ ∑_{l,q} Q_j(l,q) E ∂_q∂_l∂_jf(G)` uniformly over the Stein class.
-/

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators RealInnerProductSpace ContDiff

noncomputable section

namespace S99

open S45
open HRS.Whole
open HRS (Euc cbNorm MemCb)

variable {d N : ℕ}

theorem ULim.of_rate_ge2 {u : ℕ → (SeqL2 → ℝ) → ℝ} {L : (SeqL2 → ℝ) → ℝ} {K : ℝ} (hK : 0 ≤ K)
    (h : ∀ N : ℕ, 2 ≤ N → ∀ f, SteinCl f → |u N f - L f| ≤ K / Real.sqrt N) : ULim u L := by
  intro ε hε
  refine ⟨max 2 (⌈(K / ε) ^ 2⌉₊ + 1), fun N hN f hf => ?_⟩
  have hN2 : 2 ≤ N := (le_max_left _ _).trans hN
  have hN0 : (0 : ℝ) < N := by exact_mod_cast (by omega : 0 < N)
  have hsqN : 0 < Real.sqrt N := Real.sqrt_pos.2 hN0
  refine (h N hN2 f hf).trans ?_
  rw [div_le_iff₀ hsqN]
  have hx : (K / ε) ^ 2 ≤ (N : ℝ) := by
    have h2 : (K / ε) ^ 2 ≤ (⌈(K / ε) ^ 2⌉₊ : ℝ) := Nat.le_ceil _
    have h3 : ((⌈(K / ε) ^ 2⌉₊ + 1 : ℕ) : ℝ) ≤ (N : ℝ) := by
      exact_mod_cast (le_max_right _ _).trans hN
    push_cast at h3
    linarith
  have h4 : K / ε ≤ Real.sqrt N := Real.le_sqrt_of_sq_le hx
  rw [div_le_iff₀ hε] at h4
  linarith

theorem ULim.congr_L {u : ℕ → (SeqL2 → ℝ) → ℝ} {L L' : (SeqL2 → ℝ) → ℝ}
    (h : ∀ f, SteinCl f → L f = L' f) (hu : ULim u L) : ULim u L' := by
  intro ε hε
  obtain ⟨N₁, h1⟩ := hu ε hε
  exact ⟨N₁, fun N hN f hf => by rw [← h f hf]; exact h1 N hN f hf⟩

section LimAB

variable (hd : 2 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hs : s < (d : ℝ) / 2) {a β γ : ℝ} (ha : 0 < a)
  (hβ : 0 < β) (hγ : 0 < γ) {C c BU Cs : ℝ} (hT : ThermalData d s a β C c BU)
  (hS : ∀ N : ℕ, 2 ≤ N → S46.S46Static d s a β γ Cs N)
  {φ : ℕ → Euc d → ℝ} (hφ : IsSummableFeatureFamily (J1 d) φ) (F : FamData d s a β γ φ)

include hd hs0 hs ha hβ hγ hT hS hφ F

theorem s99_ULimA {G : Measure SeqL2} [IsProbabilityMeasure G]
    (hG : IsCenteredGaussianSeq G (fun i j => susceptibilityCov (rieszKernel d s)
      (thermalMeasure d s a β) γ (φ i) (φ j))) :
    ULim (fun N f => if 2 ≤ N then ∑' p : ℕ × ℕ, Aterm d s a β γ F N f p else 0)
      (fun f => ∑' p : ℕ × ℕ, Alim d s a β γ F G f p) := by
  have hsd : s < d := by
    have : (0 : ℝ) ≤ (d : ℝ) / 2 := by positivity
    linarith
  haveI hμ : IsProbabilityMeasure (thermalMeasure d s a β) :=
    HRS.Whole.Q34.isProbabilityMeasure_nu hT.prob
  obtain ⟨KA, hKA0, hA⟩ := s99_A_rate hd hs0 hs ha hβ hγ hT hS hφ F hG
  set b : ℕ → ℝ := fun j => cbNorm (J1 d) (φ j) with hbdef
  have hb0 : ∀ j, 0 ≤ b j := fun j => HRS.MS.Tc5.tc5_cb_nonneg _ _
  have hbs : Summable b := hφ.2
  have hbb : Summable fun p : ℕ × ℕ => b p.1 * b p.2 :=
    Summable.mul_of_nonneg (f := b) (g := b) hbs hbs (fun j => hb0 j) (fun j => hb0 j)
  set Sb : ℝ := ∑' j, b j with hSb
  have hSb0 : 0 ≤ Sb := tsum_nonneg hb0
  have hKw0 := s99_Kw_nonneg F hγ
  have hFK0 := F.hK
  -- the bound on `Alim`
  have hAlim : ∀ f, SteinCl f → ∀ p : ℕ × ℕ, |Alim d s a β γ F G f p| ≤ Kw d γ F * F.K * Sb * (b p.1 * b p.2) := by
    intro f hf p
    have hw := s99_wF_cb hd hγ hφ.1 F p.1 p.2
    have hwbd : ∀ x, |wF F p.1 p.2 x| ≤ Kw d γ F * (b p.1 * b p.2) := fun x => by
      have := s99_norm_iter_le_cb hw.1 (Nat.zero_le _) x
      rw [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
      refine this.trans (hw.2.trans (le_of_eq ?_))
      unfold Kw; simp only [hbdef]; ring
    have hwm : Measurable (wF F p.1 p.2) := hw.1.1.continuous.measurable
    have hcc : ∀ m, |cc d s a β γ F p m| ≤ (Kw d γ F * (b p.1 * b p.2)) * (F.K * b m) := fun m =>
      s99_kap_bd hd hs0 hs ha hβ hγ hT hS hφ F hwm hwbd m
    have hGb : ∀ m, |∫ z, pd (pd (pd f p.1) p.2) m z ∂G| ≤ 1 := fun m => by
      have := norm_integral_le_of_norm_le_const (μ := G) (f := pd (pd (pd f p.1) p.2) m) (C := 1)
        (Filter.Eventually.of_forall fun z => by
          rw [Real.norm_eq_abs]; exact (((hf.pd p.1).pd p.2).pd m).abs_le z)
      simpa [Real.norm_eq_abs] using this
    unfold Alim
    rw [abs_neg]
    have hg : HasSum (fun m => Kw d γ F * (b p.1 * b p.2) * F.K * b m)
        (Kw d γ F * (b p.1 * b p.2) * F.K * Sb) := hbs.hasSum.mul_left _
    have := tsum_of_norm_bounded hg (f := fun m => cc d s a β γ F p m * ∫ z, pd (pd (pd f p.1) p.2) m z ∂G)
      (fun m => by
        rw [norm_mul, Real.norm_eq_abs, Real.norm_eq_abs]
        calc |cc d s a β γ F p m| * |∫ z, pd (pd (pd f p.1) p.2) m z ∂G| ≤
            ((Kw d γ F * (b p.1 * b p.2)) * (F.K * b m)) * 1 :=
              mul_le_mul (hcc m) (hGb m) (abs_nonneg _) (by have := hb0 m; have := hb0 p.1; have := hb0 p.2; positivity)
          _ = _ := by ring)
    rw [Real.norm_eq_abs] at this
    refine this.trans (le_of_eq ?_)
    ring
  -- reindex
  obtain ⟨e⟩ : Nonempty (ℕ ≃ ℕ × ℕ) := ⟨(Denumerable.eqv (ℕ × ℕ)).symm⟩
  set M : ℕ × ℕ → ℝ := fun p => (KA + Kw d γ F * F.K * Sb) * (b p.1 * b p.2) with hM
  have hMs : Summable fun n => M (e n) := (e.summable_iff (f := M)).2 (hbb.mul_left _)
  have hMn : ∀ p, 0 ≤ M p := fun p => by
    have := hb0 p.1; have := hb0 p.2; simp only [hM]; positivity
  have hmain := s99_ULim_tsum (u := fun n N f => if 2 ≤ N then Aterm d s a β γ F N f (e n) else 0)
    (L := fun n f => Alim d s a β γ F G f (e n)) (M := fun n => M (e n)) hMs
    (fun n N f hf => by
      by_cases hN : 2 ≤ N
      · simp only [hN, ite_true]
        have h1 := hA N hN f hf (e n)
        have h2 := hAlim f hf (e n)
        have hN0 : (1 : ℝ) ≤ Real.sqrt N := by
          rw [Real.one_le_sqrt]; exact_mod_cast (by omega : 1 ≤ N)
        have hsq : 0 < Real.sqrt N := by linarith
        have h3 : KA * (b (e n).1 * b (e n).2) / Real.sqrt N ≤ KA * (b (e n).1 * b (e n).2) := by
          rw [div_le_iff₀ hsq]
          have : 0 ≤ KA * (b (e n).1 * b (e n).2) := by have := hb0 (e n).1; have := hb0 (e n).2; positivity
          nlinarith
        calc |Aterm d s a β γ F N f (e n)| ≤ |Alim d s a β γ F G f (e n)| +
              |Aterm d s a β γ F N f (e n) - Alim d s a β γ F G f (e n)| := by
              have := abs_add_le (Alim d s a β γ F G f (e n)) (Aterm d s a β γ F N f (e n) - Alim d s a β γ F G f (e n))
              simpa using this
          _ ≤ _ := by
              simp only [hM]
              nlinarith [h1, h2, h3]
      · simp only [hN, ite_false, abs_zero]; exact hMn _)
    (fun n f hf => (hAlim f hf (e n)).trans (by
      simp only [hM]
      have := hb0 (e n).1; have := hb0 (e n).2
      have : Kw d γ F * F.K * Sb ≤ KA + Kw d γ F * F.K * Sb := by linarith
      exact mul_le_mul_of_nonneg_right this (by positivity)))
    (fun n => ULim.of_rate_ge2 (K := KA * (b (e n).1 * b (e n).2)) (by
        have := hb0 (e n).1; have := hb0 (e n).2; positivity) (fun N hN f hf => by
      simp only [hN, ite_true]
      exact (hA N hN f hf (e n))))
  refine ULim.congr_L (fun f hf => e.tsum_eq (fun p => Alim d s a β γ F G f p)) (ULim.congr (fun N f hf => ?_) hmain)
  by_cases hN : 2 ≤ N
  · simp only [hN, ite_true]
    exact (e.tsum_eq (fun p => Aterm d s a β γ F N f p))
  · simp [hN]

end LimAB

end S99

end
