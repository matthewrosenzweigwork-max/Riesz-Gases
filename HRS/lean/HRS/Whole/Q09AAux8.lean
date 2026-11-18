import HRS.Whole.Q09AAux7
open MeasureTheory Filter Topology
open scoped ENNReal NNReal ComplexConjugate ContDiff

/-!
# Packet Q09-A, part 8: `‖plat_N · h‖_{H^m}` for a uniformly local `h`

`sobolev_plat_bound`: if all the localizations `χ(· - z) h` lie in `H^m` with norm `≤ U`, then
`plat d N · h ∈ H^m` with `‖plat d N · h‖²_{H^m} ≤ K² (2N+1)^d U²`, `K = K(d, m)` independent of `N`.
-/

noncomputable section

namespace HRS.Whole.Q09A
open HRS.PDE.ToolboxRd LineDeriv

variable {d : ℕ}

/-- the unshifted piece as a complex function -/
def A0 (d : ℕ) : Euc d → ℂ := fun x => ((Th0 d x : ℝ) : ℂ)

theorem Th0_eq_Th (d : ℕ) (x : Euc d) : Th0 d x = Th d 0 (fun _ => 0) x := by
  simp [Th0, Th]

theorem A0_isCc (hd : 1 ≤ d) : IsCc (A0 d) := by
  refine ⟨Complex.ofRealCLM.contDiff.comp (Th0_contDiff d), ?_⟩
  refine HasCompactSupport.intro (isCompact_closedBall (zc d 0 (fun _ => 0)) 1) fun x hx => ?_
  by_contra hne
  have h1 : Th d 0 (fun _ => 0) x ≠ 0 := by
    rw [← Th0_eq_Th]
    intro h0; apply hne; simp [A0, h0]
  have h2 := inBox_dist hd (Th_ne_zero_inBox h1)
  exact hx (by simpa [Metric.mem_closedBall, dist_eq_norm] using h2)

/-- the piece `Th d N k` as a complex function: a translate of `A0` -/
def aK (d N : ℕ) (k : Fin d → ℕ) : Euc d → ℂ := fun x => ((Th d N k x : ℝ) : ℂ)

theorem aK_eq (hd : 1 ≤ d) (N : ℕ) (k : Fin d → ℕ) :
    aK d N k = fun x => A0 d (x - cvec d N k) := by
  ext x; simp [aK, A0, Th_eq hd]

theorem aK_isCc (hd : 1 ≤ d) (N : ℕ) (k : Fin d → ℕ) : IsCc (aK d N k) := by
  rw [aK_eq hd]; exact (A0_isCc hd).translate _

theorem tsupport_aK_subset (N : ℕ) (k : Fin d → ℕ) :
    tsupport (aK d N k) ⊆ {x | InBox d N k x} := by
  refine closure_minimal (fun x hx => ?_) (isClosed_inBox d N k)
  apply Th_ne_zero_inBox
  intro h0; apply hx; simp [aK, h0]

theorem coef_bound (hd : 1 ≤ d) (m : ℕ) :
    ∃ Bc : ℝ, 0 ≤ Bc ∧ ∀ (i : Fin d) (j l : ℕ), j ≤ m → l ≤ j → ∀ y : Euc d,
      ‖coef i (A0 d) j l y‖ ≤ Bc := by
  have hb : ∀ (t : Fin d × Fin (m + 1) × Fin (m + 1)), ∃ b : ℝ, ∀ y : Euc d,
      ‖coef t.1 (A0 d) t.2.1 t.2.2 y‖ ≤ b := fun t =>
    (coef_isCc (A0_isCc hd) t.2.1 t.2.2).supp.exists_bound_of_continuous
      (coef_isCc (A0_isCc hd) t.2.1 t.2.2).continuous
  choose bb hbb using hb
  obtain ⟨M, hM⟩ := (Set.finite_range bb).bddAbove
  refine ⟨max M 0, le_max_right _ _, fun i j l hj hl y => ?_⟩
  have := hbb (i, ⟨j, by omega⟩, ⟨l, by omega⟩) y
  have h2 : bb (i, ⟨j, by omega⟩, ⟨l, by omega⟩) ≤ M := hM ⟨_, rfl⟩
  exact (this.trans h2).trans (le_max_left _ _)


/-- **The `H^m` bound for the cutoff times a uniformly local function.** -/
theorem sobolev_plat_bound (hd : 1 ≤ d) {m : ℕ} (hm : 1 ≤ m) (χ : Euc d → ℝ)
    (hχ1 : ∀ x ∈ Metric.closedBall (0 : Euc d) 1, χ x = 1) :
    ∃ K : ℝ, 0 ≤ K ∧ ∀ (N : ℕ) (h : Euc d → ℝ) (U : ℝ),
      (∀ z : Euc d, HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (fun x => χ (x - z) * h x) ∧
        HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (fun x => χ (x - z) * h x) ≤ U ^ 2) →
      HRS.PDE.ToolboxRd.MemSobolev (m : ℝ) (fun x => plat d N x * h x) ∧
        HRS.PDE.ToolboxRd.sobolevNormSq (m : ℝ) (fun x => plat d N x * h x) ≤
          K ^ 2 * ((2 * N + 1 : ℝ) ^ d) * U ^ 2 := by
  classical
  obtain ⟨Bc, hBc0, hBc⟩ := coef_bound hd m
  refine ⟨Real.sqrt (((d : ℝ) + 1) ^ m * 3 ^ d * ((m : ℝ) + 1) ^ 2 * Bc ^ 2), Real.sqrt_nonneg _, ?_⟩
  intro N h U hU
  set B : Finset (Fin d → ℕ) := Fintype.piFinset (fun _ : Fin d => Finset.range (2 * N + 1)) with hB
  have hcard : (B.card : ℝ) = (2 * N + 1 : ℝ) ^ d := by
    rw [hB, Fintype.card_piFinset]
    simp
  -- the chains of the localized functions
  have hch : ∀ (k : Fin d → ℕ) (i : Fin d), ∃ G : ℕ → Euc d → ℂ,
      Chain i m (fun x => ((χ (x - zc d N k) * h x : ℝ) : ℂ)) G ∧ ∀ j ≤ m,
        ∃ hj : MemLp (G j) 2 volume, ∫ x, ‖G j x‖ ^ 2 ≤ U ^ 2 := by
    intro k i
    obtain ⟨G, hG, hGj⟩ := chain_of_memSobolev (hU (zc d N k)).1 i
    refine ⟨G, hG, fun j hj => ?_⟩
    obtain ⟨hmem, hint⟩ := hGj j hj
    exact ⟨hmem, hint.trans (hU (zc d N k)).2⟩
  choose Gk hGkchain hGkmem using hch
  -- chains of `plat * h`
  have hmulchain : ∀ i : Fin d, Chain i m (fun x => ∑ k ∈ B, aK d N k x * ((χ (x - zc d N k) * h x : ℝ) : ℂ))
      (fun j x => ∑ k ∈ B, ∑ l ∈ Finset.range (j + 1), coef i (aK d N k) j l x * Gk k i l x) :=
    fun i => Chain.sum B fun k _ => Chain.mul (hGkchain k i) (aK_isCc hd N k)
  have hfun : (fun x => ∑ k ∈ B, aK d N k x * ((χ (x - zc d N k) * h x : ℝ) : ℂ)) =
      fun x => ((plat d N x * h x : ℝ) : ℂ) := by
    ext x
    have h1 : ∀ k ∈ B, aK d N k x * ((χ (x - zc d N k) * h x : ℝ) : ℂ) =
        (((Th d N k x) * h x : ℝ) : ℂ) := by
      intro k _
      by_cases h0 : Th d N k x = 0
      · simp [aK, h0]
      · have hd1 := inBox_dist hd (Th_ne_zero_inBox h0)
        have hχ : χ (x - zc d N k) = 1 := hχ1 _ (by simpa [Metric.mem_closedBall] using hd1)
        simp [aK, hχ]
    rw [Finset.sum_congr rfl h1, plat_eq_sum, ← Complex.ofReal_sum, Finset.sum_mul]
  set Gp : Fin d → ℕ → Euc d → ℂ :=
    fun i j x => ∑ k ∈ B, ∑ l ∈ Finset.range (j + 1), coef i (aK d N k) j l x * Gk k i l x with hGp
  have hchp : ∀ i : Fin d, Chain i m (fun x => ((plat d N x * h x : ℝ) : ℂ)) (Gp i) := by
    intro i
    have := hmulchain i
    rw [hfun] at this
    exact this
  have hi0 : Fin d := ⟨0, hd⟩
  have hψ : MemLp (fun x => plat d N x * h x) 2 volume := by
    have h1 := ((hchp ⟨0, hd⟩).2 0 hm).1
    rw [(hchp ⟨0, hd⟩).1] at h1
    have := h1.re
    simpa using this
  -- the `L²` bounds for the chain functions
  have hL2 : ∀ (i : Fin d) (j : ℕ), j ≤ m → MemLp (Gp i j) 2 volume ∧
      ∫ x, ‖Gp i j x‖ ^ 2 ≤ 3 ^ d * ((B.card : ℝ) * (((j : ℝ) + 1) ^ 2 * Bc ^ 2 * U ^ 2)) := by
    intro i j hj
    have hF : ∀ k ∈ B, MemLp (fun x => ∑ l ∈ Finset.range (j + 1),
        coef i (aK d N k) j l x * Gk k i l x) 2 volume ∧
        ∫ x, ‖∑ l ∈ Finset.range (j + 1), coef i (aK d N k) j l x * Gk k i l x‖ ^ 2 ≤
          ((j : ℝ) + 1) ^ 2 * Bc ^ 2 * U ^ 2 := by
      intro k _
      refine l2_coef_sum (aK_isCc hd N k) i j Bc (U ^ 2) hBc0 (Gk k i)
        (fun l hl => (hGkmem k i l (by omega)).1) (fun l hl => (hGkmem k i l (by omega)).2)
        (fun l hl x => ?_)
      rw [aK_eq hd, coef_translate]
      exact hBc i j l hj hl _
    have hsupp : ∀ k x, x ∉ {x | InBox d N k x} → ∑ l ∈ Finset.range (j + 1),
        coef i (aK d N k) j l x * Gk k i l x = 0 := by
      intro k x hx
      refine Finset.sum_eq_zero fun l _ => ?_
      have : coef i (aK d N k) j l x = 0 :=
        image_eq_zero_of_notMem_tsupport
          (fun hxt => hx (tsupport_aK_subset N k
            (tsupport_coef_subset i (aK d N k) j l hxt)))
      simp [this]
    refine ⟨?_, ?_⟩
    · have := memLp_finsetSum' B fun k hk => (hF k hk).1
      exact this.ae_eq (Eventually.of_forall fun x => by simp [hGp])
    · calc ∫ x, ‖Gp i j x‖ ^ 2
          ≤ ((3 ^ d : ℕ) : ℝ) * ∑ k ∈ B, ∫ x, ‖∑ l ∈ Finset.range (j + 1),
              coef i (aK d N k) j l x * Gk k i l x‖ ^ 2 :=
            l2_sum_overlap B (fun k x => ∑ l ∈ Finset.range (j + 1),
              coef i (aK d N k) j l x * Gk k i l x) (fun k => {x | InBox d N k x}) (3 ^ d)
              (fun k hk => (hF k hk).1) hsupp (fun x => inBox_overlap d N x B)
        _ ≤ ((3 ^ d : ℕ) : ℝ) * ∑ _k ∈ B, (((j : ℝ) + 1) ^ 2 * Bc ^ 2 * U ^ 2) := by
            gcongr with k hk
            exact (hF k hk).2
        _ = _ := by
            simp only [Finset.sum_const, nsmul_eq_mul]
            push_cast
            ring
  obtain ⟨hMS, hnorm⟩ := memSobolev_of_chains hm hψ Gp hchp
  refine ⟨hMS, hnorm.trans ?_⟩
  have hψint : ∫ x, (plat d N x * h x) ^ 2 ≤
      3 ^ d * ((B.card : ℝ) * (((0 : ℕ) + 1 : ℝ) ^ 2 * Bc ^ 2 * U ^ 2)) := by
    have h0 := (hL2 ⟨0, hd⟩ 0 (Nat.zero_le _)).2
    have e : ∫ x, ‖Gp ⟨0, hd⟩ 0 x‖ ^ 2 = ∫ x, (plat d N x * h x) ^ 2 := by
      refine integral_congr_ae (Eventually.of_forall fun x => ?_)
      simp only [(hchp ⟨0, hd⟩).1]
      rw [Complex.norm_real, Real.norm_eq_abs, sq_abs]
    rw [e] at h0
    simpa using h0
  have hsum : ∑ i : Fin d, ∫ x, ‖Gp i m x‖ ^ 2 ≤
      d * (3 ^ d * ((B.card : ℝ) * (((m : ℝ) + 1) ^ 2 * Bc ^ 2 * U ^ 2))) := by
    calc ∑ i : Fin d, ∫ x, ‖Gp i m x‖ ^ 2
        ≤ ∑ _i : Fin d, (3 ^ d * ((B.card : ℝ) * (((m : ℝ) + 1) ^ 2 * Bc ^ 2 * U ^ 2))) :=
          Finset.sum_le_sum fun i _ => (hL2 i m le_rfl).2
      _ = _ := by simp
  rw [Real.sq_sqrt (by positivity), hcard] at *
  have hd1 : (0 : ℝ) ≤ (d : ℝ) + 1 := by positivity
  have hpow : ((d : ℝ) + 1) ^ (m - 1) * ((d : ℝ) + 1) = ((d : ℝ) + 1) ^ m := by
    rw [← pow_succ]; congr 1; omega
  have hm1 : (1 : ℝ) ≤ ((m : ℝ) + 1) ^ 2 := by nlinarith [Nat.cast_nonneg (α := ℝ) m]
  have hX : 0 ≤ (3 : ℝ) ^ d * ((2 * N + 1 : ℝ) ^ d * (Bc ^ 2 * U ^ 2)) := by positivity
  calc ((d : ℝ) + 1) ^ (m - 1) * ((∫ x, (plat d N x * h x) ^ 2) + ∑ i : Fin d, ∫ x, ‖Gp i m x‖ ^ 2)
      ≤ ((d : ℝ) + 1) ^ (m - 1) * (3 ^ d * ((2 * N + 1 : ℝ) ^ d * (((m : ℝ) + 1) ^ 2 * Bc ^ 2 * U ^ 2)) +
        d * (3 ^ d * ((2 * N + 1 : ℝ) ^ d * (((m : ℝ) + 1) ^ 2 * Bc ^ 2 * U ^ 2)))) := by
        gcongr
        · have h3 : (((0 : ℕ) : ℝ) + 1) ^ 2 ≤ ((m : ℝ) + 1) ^ 2 := by simpa using hm1
          refine hψint.trans ?_
          gcongr
    _ = ((d : ℝ) + 1) ^ m * 3 ^ d * ((m : ℝ) + 1) ^ 2 * Bc ^ 2 * (2 * N + 1 : ℝ) ^ d * U ^ 2 := by
        rw [← hpow]; ring
