import HRS.MS.QMul
import HRS.MS.UlocCb
import HRS.MS.UlocCut
import HRS.MS.UlocMWAux2

/-!
# UL-0, part 1: the norm toolkit for the lattice norm `ulNormE` and the continuum norm `ulocNormE`

New infrastructure (not a manuscript row); everything is in the namespace `HRS.MS.Ul`, helper lemmas
carry the prefix `ul0_`.  Statements:

* `ul_equiv`: for `IsUlCutoff θ` and `IsUlocCutoff χ` the norms `ulNormE m θ` and `ulocNormE m χ` are
  bounded by each other up to one constant (all `u`, all `m : ℕ`).  Route: the `uc_key` pattern of
  `UlocCutAux2.lean` (finite net and a smooth inverse `ρ` of `∑_y b(·-y)²`); `ul0_key` is the version
  for an arbitrary smooth compactly supported `a` and a family `b` which is `1` at one net point near every
  point (for the lattice direction one uses `θ = 1` on `[-2,2]^d` and the squares `θ²`, so no sign of `θ`
  is needed).
* `ulocNormE_mul_cb`: `‖a u‖_{ul} ≤ C ‖a‖_{C_b^m} ‖u‖_{ul}` (from `sobolevNormE_mul_cb_le`).
* `ulocNormE_le_cb`: `‖f‖_{ul} ≤ C ‖f‖_{C_b^m}` for `f ∈ C_b^m`.
* monotonicity in the smoothness index, triangle inequality, finiteness of `ulNormE` on `C_c^∞ + const`.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.Ul
open HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

/-! ### Elementary facts about `sobolevNormE` -/

theorem ul0_sobE_mono {r r' : ℝ} (h : r ≤ r') (u : Euc d → ℝ) :
    sobolevNormE r u ≤ sobolevNormE r' u := by
  by_cases hu : HRS.PDE.ToolboxRd.MemSobolev r' u
  · have hu' := HRS.PDE.ToolboxRd.FourierAux.memSobolev_mono h hu
    unfold sobolevNormE
    rw [if_pos hu, if_pos hu']
    apply ENNReal.ofReal_le_ofReal
    apply Real.sqrt_le_sqrt
    unfold HRS.PDE.ToolboxRd.sobolevNormSq
    refine integral_mono hu'.2 hu.2 fun ξ => ?_
    have hw := HRS.PDE.ToolboxRd.FourierAux.one_le_wt ξ
    show _ * _ ≤ _ * _
    gcongr
  · unfold sobolevNormE
    rw [if_neg hu]
    exact le_top

theorem ul0_ulNormE_mono {k k' : ℕ} (h : k ≤ k') (θ f : Euc d → ℝ) :
    ulNormE k θ f ≤ ulNormE k' θ f :=
  iSup_mono fun z => ul0_sobE_mono (by exact_mod_cast h) _

theorem ul0_ulNormE_add (k : ℕ) (θ a b : Euc d → ℝ) :
    ulNormE k θ (fun x => a x + b x) ≤ ulNormE k θ a + ulNormE k θ b := by
  refine iSup_le fun z => ?_
  have e : (fun x => θ (x - latticePt z) * (a x + b x)) =
      fun x => θ (x - latticePt z) * a x + θ (x - latticePt z) * b x := by
    funext x; ring
  rw [e]
  refine (HRS.MS.UlocCut.uc_tri _ _ _).trans (add_le_add ?_ ?_)
  · exact le_iSup (fun z : Fin d → ℤ => sobolevNormE (k : ℝ) fun x => θ (x - latticePt z) * a x) z
  · exact le_iSup (fun z : Fin d → ℤ => sobolevNormE (k : ℝ) fun x => θ (x - latticePt z) * b x) z

theorem ul0_ulNormE_sub_le (k : ℕ) (θ f g : Euc d → ℝ) :
    ulNormE k θ f ≤ ulNormE k θ (fun x => f x - g x) + ulNormE k θ g := by
  have := ul0_ulNormE_add k θ (fun x => f x - g x) g
  simpa using this

theorem ul0_ulocNormE_add (m : ℕ) (χ a b : Euc d → ℝ) :
    ulocNormE m χ (fun x => a x + b x) ≤ ulocNormE m χ a + ulocNormE m χ b := by
  refine iSup_le fun z => ?_
  have e : (fun x => χ (x - z) * (a x + b x)) =
      fun x => χ (x - z) * a x + χ (x - z) * b x := by
    funext x; ring
  rw [e]
  refine (HRS.MS.UlocCut.uc_tri _ _ _).trans (add_le_add ?_ ?_)
  · exact le_iSup (fun z : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - z) * a x) z
  · exact le_iSup (fun z : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - z) * b x) z

/-! ### The smooth inverse and the generalised key lemma -/

/-- a smooth compactly supported inverse of a smooth function on a closed ball where it is `≥ 1` -/
theorem ul0_exists_inv (Sg : Euc d → ℝ) (hS : ContDiff ℝ ∞ Sg) (R : ℝ) (hR : 0 < R)
    (hge : ∀ p : Euc d, ‖p‖ ≤ R → 1 ≤ Sg p) :
    ∃ ρ : Euc d → ℝ, ContDiff ℝ ∞ ρ ∧ HasCompactSupport ρ ∧ ∀ p : Euc d, ‖p‖ ≤ R → ρ p * Sg p = 1 := by
  have hU : IsOpen {p : Euc d | 1 / 2 < Sg p} := isOpen_lt continuous_const hS.continuous
  have hKU : Metric.closedBall (0 : Euc d) R ⊆ {p : Euc d | 1 / 2 < Sg p} := fun p hp => by
    have := hge p (by simpa using hp)
    show 1 / 2 < Sg p
    linarith
  obtain ⟨δ, hδ, hth⟩ := (isCompact_closedBall (0 : Euc d) R).exists_thickening_subset_open hU hKU
  let f : ContDiffBump (0 : Euc d) := ⟨R, R + δ / 2, hR, by linarith⟩
  have hts : tsupport f ⊆ {p : Euc d | 1 / 2 < Sg p} := by
    rw [f.tsupport_eq]
    intro p hp
    apply hth
    rw [thickening_closedBall hδ hR.le]
    have : ‖p‖ ≤ R + δ / 2 := by simpa [f] using hp
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  refine ⟨fun p => f p / Sg p, ?_, ?_, ?_⟩
  · refine contDiff_iff_contDiffAt.2 fun x => ?_
    by_cases hx : Sg x = 0
    · have hxn : x ∉ tsupport f := fun h => by
        have := hts h
        simp only [Set.mem_ofPred_eq] at this
        linarith
      have hev := notMem_tsupport_iff_eventuallyEq.1 hxn
      refine (contDiffAt_const (c := (0 : ℝ))).congr_of_eventuallyEq ?_
      filter_upwards [hev] with y hy
      simp [hy]
    · exact (f.contDiff.contDiffAt).div (hS.contDiffAt) hx
  · refine f.hasCompactSupport.mono' ?_
    intro y hy
    refine subset_tsupport _ ?_
    intro h0
    exact hy (by simp [h0])
  · intro p hp
    have h1 : f p = 1 := f.one_of_mem_closedBall (by simpa [f] using hp)
    have h2 := hge p hp
    show f p / Sg p * Sg p = 1
    rw [h1]; field_simp

/-- the generalised key lemma: `a(·-z) u` is controlled by the finitely many pieces `b(·-(w+y)) u`. -/
theorem ul0_key (m : ℕ) (a b : Euc d → ℝ) (ha : ContDiff ℝ ∞ a) (hac : HasCompactSupport a)
    (hb : ContDiff ℝ ∞ b) (hbc : HasCompactSupport b) (Y : Finset (Euc d)) (R0 R1 R : ℝ)
    (hR : 0 < R) (hRR : R0 + R1 ≤ R) (hsup : ∀ p : Euc d, a p ≠ 0 → ‖p‖ ≤ R0)
    (hY : ∀ p : Euc d, ‖p‖ ≤ R → ∃ y ∈ Y, b (p - y) = 1) :
    ∃ C : ℝ, 0 < C ∧ ∀ z w : Euc d, ‖z - w‖ ≤ R1 → ∀ u : Euc d → ℝ,
      sobolevNormE (m : ℝ) (fun x => a (x - z) * u x) ≤
        ENNReal.ofReal C * ∑ y ∈ Y, sobolevNormE (m : ℝ) (fun x => b (x - (w + y)) * u x) := by
  set Sg : Euc d → ℝ := fun p => ∑ y ∈ Y, b (p - y) ^ 2 with hSg
  have hS : ContDiff ℝ ∞ Sg :=
    ContDiff.sum fun y _ => (hb.comp (contDiff_id.sub contDiff_const)).pow 2
  have hge : ∀ p : Euc d, ‖p‖ ≤ R → 1 ≤ Sg p := by
    intro p hp
    obtain ⟨y, hy, hpy⟩ := hY p hp
    calc (1 : ℝ) = b (p - y) ^ 2 := by rw [hpy]; norm_num
      _ ≤ Sg p := Finset.single_le_sum (f := fun y => b (p - y) ^ 2)
          (fun y _ => sq_nonneg _) hy
  obtain ⟨ρ, hρ, hρc, hρ1⟩ := ul0_exists_inv Sg hS R hR hge
  obtain ⟨C1, hC1, h1⟩ := HRS.MS.SobMul.sobolevNormE_mul_translate_le (d := d) (m : ℝ)
    (Nat.cast_nonneg m) a ha hac
  obtain ⟨C2, hC2, h2⟩ := HRS.MS.SobMul.sobolevNormE_mul_translate_le (d := d) (m : ℝ)
    (Nat.cast_nonneg m) ρ hρ hρc
  obtain ⟨C3, hC3, h3⟩ := HRS.MS.SobMul.sobolevNormE_mul_translate_le (d := d) (m : ℝ)
    (Nat.cast_nonneg m) b hb hbc
  refine ⟨C1 * C2 * C3, by positivity, fun z w hzw u => ?_⟩
  have hpt : (fun x => a (x - z) * u x) =
      fun x => a (x - z) * (ρ (x - w) * ∑ y ∈ Y, (b (x - (w + y)) * (b (x - (w + y)) * u x))) := by
    funext x
    by_cases hx : a (x - z) = 0
    · simp [hx]
    · have hn : ‖x - z‖ ≤ R0 := hsup _ hx
      have hxw : ‖x - w‖ ≤ R := by
        calc ‖x - w‖ = ‖(x - z) + (z - w)‖ := by rw [sub_add_sub_cancel]
          _ ≤ ‖x - z‖ + ‖z - w‖ := norm_add_le _ _
          _ ≤ R := by linarith
      have := hρ1 (x - w) hxw
      have e : ∑ y ∈ Y, (b (x - (w + y)) * (b (x - (w + y)) * u x)) = Sg (x - w) * u x := by
        rw [hSg]
        simp only
        rw [Finset.sum_mul]
        refine Finset.sum_congr rfl fun y _ => ?_
        rw [sub_sub]; ring
      rw [e, ← mul_assoc (ρ (x - w)), this, one_mul]
  rw [hpt]
  calc sobolevNormE (m : ℝ) (fun x => a (x - z) *
        (ρ (x - w) * ∑ y ∈ Y, (b (x - (w + y)) * (b (x - (w + y)) * u x))))
      ≤ ENNReal.ofReal C1 * sobolevNormE (m : ℝ)
          (fun x => ρ (x - w) * ∑ y ∈ Y, (b (x - (w + y)) * (b (x - (w + y)) * u x))) := h1 z _
    _ ≤ ENNReal.ofReal C1 * (ENNReal.ofReal C2 * sobolevNormE (m : ℝ)
          (fun x => ∑ y ∈ Y, (b (x - (w + y)) * (b (x - (w + y)) * u x)))) := by
        gcongr
        exact h2 w _
    _ ≤ ENNReal.ofReal C1 * (ENNReal.ofReal C2 * ∑ y ∈ Y, sobolevNormE (m : ℝ)
          (fun x => b (x - (w + y)) * (b (x - (w + y)) * u x))) := by
        gcongr
        exact HRS.MS.UlocCut.uc_sum_le (m : ℝ) Y (fun y x => b (x - (w + y)) * (b (x - (w + y)) * u x))
    _ ≤ ENNReal.ofReal C1 * (ENNReal.ofReal C2 * ∑ y ∈ Y, (ENNReal.ofReal C3 * sobolevNormE (m : ℝ)
          (fun x => b (x - (w + y)) * u x))) := by
        gcongr with y hy
        exact h3 (w + y) _
    _ = ENNReal.ofReal (C1 * C2 * C3) * ∑ y ∈ Y, sobolevNormE (m : ℝ)
          (fun x => b (x - (w + y)) * u x) := by
        rw [← Finset.mul_sum, ENNReal.ofReal_mul (by positivity), ENNReal.ofReal_mul hC1.le]
        ring

/-! ### Cutoffs exist -/

theorem ul0_exists_ulocCutoff (d : ℕ) : ∃ χ : Euc d → ℝ, IsUlocCutoff χ := by
  let f : ContDiffBump (0 : Euc d) := ⟨1, 3 / 2, one_pos, by norm_num⟩
  refine ⟨f, f.contDiff, f.hasCompactSupport, ?_, fun x => ⟨f.nonneg, f.le_one⟩, fun x hx => ?_⟩
  · rw [f.tsupport_eq]
    intro p hp
    have : ‖p‖ ≤ 3 / 2 := by simpa [f] using hp
    simp only [Metric.mem_ball, dist_zero_right]
    linarith
  · exact f.one_of_mem_closedBall (by simpa [f] using hx)

/-! ### `ul_equiv` -/

theorem ul0_latticePt_add (a b : Fin d → ℤ) : latticePt a + latticePt b = latticePt (a + b) := by
  unfold latticePt
  ext i
  simp

theorem ul0_ulNormE_le_uloc (m : ℕ) (θ χ : Euc d → ℝ) (hθ : IsUlCutoff θ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Euc d → ℝ, ulNormE m θ u ≤ ENNReal.ofReal C * ulocNormE m χ u := by
  obtain ⟨R0, hR0⟩ := hθ.2.1.isCompact.isBounded.subset_closedBall (0 : Euc d)
  set R0' : ℝ := max R0 0 + 1 with hR0'
  have hR0pos : 0 < R0' := by positivity
  obtain ⟨Y, hY⟩ := HRS.MS.UlocCut.uc_cover (fun y : Euc d => y)
    (fun p => ⟨p, by simpa using one_pos⟩) R0'
  obtain ⟨C, hC, h⟩ := ul0_key m θ χ hθ.1 hθ.2.1 hχ.1 hχ.2.1 Y R0' 0 R0' hR0pos (by linarith)
    (fun p hp => by
      have : p ∈ tsupport θ := subset_tsupport _ hp
      have := hR0 this
      simp only [Metric.mem_closedBall, dist_zero_right] at this
      linarith [le_max_left R0 0])
    (fun p hp => by
      obtain ⟨y, hy, hpy⟩ := hY p hp
      exact ⟨y, hy, hχ.2.2.2.2 _ (by simpa using hpy.le)⟩)
  refine ⟨C * Y.card + 1, by positivity, fun u => ?_⟩
  refine iSup_le fun z => ?_
  refine (h (latticePt z) (latticePt z) (by simp) u).trans ?_
  have : ∑ y ∈ Y, sobolevNormE (m : ℝ) (fun x => χ (x - (latticePt z + y)) * u x) ≤
      Y.card • ulocNormE m χ u :=
    Finset.sum_le_card_nsmul _ _ _ fun y _ => le_iSup (fun z : Euc d =>
      sobolevNormE (m : ℝ) fun x => χ (x - z) * u x) (latticePt z + y)
  calc _ ≤ ENNReal.ofReal C * (Y.card • ulocNormE m χ u) := by gcongr
    _ = ENNReal.ofReal (C * Y.card) * ulocNormE m χ u := by
        rw [nsmul_eq_mul, ← mul_assoc, ENNReal.ofReal_mul hC.le]
        simp
    _ ≤ ENNReal.ofReal (C * Y.card + 1) * ulocNormE m χ u := by
        gcongr
        linarith

theorem ul0_round_bound (R : ℝ) (p : Euc d) (hp : ‖p‖ ≤ R) :
    ∃ y : Fin d → ℤ, (∀ i, |y i| ≤ ⌈R⌉ + 1) ∧ ∀ i, |p i - (y i : ℝ)| ≤ 1 / 2 := by
  refine ⟨fun i => round (p i), fun i => ?_, fun i => ?_⟩
  · have h1 : |p i| ≤ R := by
      have h2 : |p i| ≤ ‖p‖ := by
        simpa [Real.norm_eq_abs] using (PiLp.norm_apply_le p i)
      exact h2.trans hp
    have h2 := abs_sub_round (p i)
    have h5 : |(round (p i) : ℝ)| ≤ R + 1 / 2 := by
      have h6 := abs_sub_abs_le_abs_sub (round (p i) : ℝ) (p i)
      rw [abs_sub_comm] at h6
      linarith
    have h4 : (R : ℝ) ≤ ⌈R⌉ := Int.le_ceil R
    have : ((|round (p i)| : ℤ) : ℝ) ≤ ((⌈R⌉ + 1 : ℤ) : ℝ) := by
      push_cast [Int.cast_abs]; linarith
    exact_mod_cast this
  · exact abs_sub_round (p i)

theorem ul0_uloc_le_ulNormE (m : ℕ) (θ χ : Euc d → ℝ) (hθ : IsUlCutoff θ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Euc d → ℝ, ulocNormE m χ u ≤ ENNReal.ofReal C * ulNormE m θ u := by
  classical
  set R1 : ℝ := (d : ℝ) with hR1
  set R : ℝ := 2 + R1 with hRdef
  have hR : 0 < R := by positivity
  set Nz : ℤ := ⌈R⌉ + 1 with hNz
  set Y0 : Finset (Fin d → ℤ) := Fintype.piFinset (fun _ : Fin d => Finset.Icc (-Nz) Nz) with hY0
  set Y : Finset (Euc d) := Y0.image latticePt with hY
  obtain ⟨C, hC, h⟩ := ul0_key m χ θ hχ.1 hχ.2.1 hθ.1 hθ.2.1 Y 2 R1 R hR (by simp [hRdef])
    (fun p hp => by
      have : p ∈ tsupport χ := subset_tsupport _ hp
      have := hχ.2.2.1 this
      simp only [Metric.mem_ball, dist_zero_right] at this
      exact this.le)
    (fun p hp => by
      obtain ⟨y, hy1, hy2⟩ := ul0_round_bound R p hp
      refine ⟨latticePt y, Finset.mem_image_of_mem _ ?_, hθ.2.2 _ fun i => ?_⟩
      · rw [hY0, Fintype.mem_piFinset]
        intro i
        rw [Finset.mem_Icc]
        have := abs_le.1 (hy1 i)
        exact ⟨this.1, this.2⟩
      · have := hy2 i
        have e : (p - latticePt y) i = p i - (y i : ℝ) := by simp [latticePt]
        rw [e]; linarith)
  refine ⟨C * Y.card + 1, by positivity, fun u => ?_⟩
  refine iSup_le fun z => ?_
  set w0 : Fin d → ℤ := fun i => round (z i) with hw0
  have hzw : ‖z - latticePt w0‖ ≤ R1 := by
    rw [EuclideanSpace.norm_eq, Real.sqrt_le_left (by positivity)]
    calc ∑ i, ‖(z - latticePt w0) i‖ ^ 2 ≤ ∑ _i : Fin d, (1 : ℝ) := by
          refine Finset.sum_le_sum fun i _ => ?_
          have e : (z - latticePt w0) i = z i - (w0 i : ℝ) := by simp [latticePt]
          rw [e, Real.norm_eq_abs]
          have : |z i - (w0 i : ℝ)| ≤ 1 / 2 := abs_sub_round (z i)
          nlinarith [abs_nonneg (z i - (w0 i : ℝ))]
      _ = (d : ℝ) := by simp
      _ ≤ R1 ^ 2 := by
          rw [hR1]
          have : (1 : ℝ) ≤ d ∨ d = 0 := by
            rcases Nat.eq_zero_or_pos d with h0 | h0
            · exact Or.inr h0
            · exact Or.inl (by exact_mod_cast h0)
          rcases this with h1 | h1
          · nlinarith
          · simp [h1]
  refine (h z (latticePt w0) hzw u).trans ?_
  have : ∑ y ∈ Y, sobolevNormE (m : ℝ) (fun x => θ (x - (latticePt w0 + y)) * u x) ≤
      Y.card • ulNormE m θ u := by
    refine Finset.sum_le_card_nsmul _ _ _ fun y hy => ?_
    obtain ⟨y0, -, rfl⟩ := Finset.mem_image.1 hy
    rw [ul0_latticePt_add]
    exact le_iSup (fun z : Fin d → ℤ => sobolevNormE (m : ℝ) fun x => θ (x - latticePt z) * u x)
      (w0 + y0)
  calc _ ≤ ENNReal.ofReal C * (Y.card • ulNormE m θ u) := by gcongr
    _ = ENNReal.ofReal (C * Y.card) * ulNormE m θ u := by
        rw [nsmul_eq_mul, ← mul_assoc, ENNReal.ofReal_mul hC.le]
        simp
    _ ≤ ENNReal.ofReal (C * Y.card + 1) * ulNormE m θ u := by
        gcongr
        linarith

/-- **UL-0 `ul_equiv`**: the lattice norm `ulNormE m θ` and the continuum norm `ulocNormE m χ` are bounded by each
other up to one constant. -/
theorem ul_equiv (m : ℕ) (θ χ : Euc d → ℝ) (hθ : IsUlCutoff θ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ u : Euc d → ℝ,
      ulNormE m θ u ≤ ENNReal.ofReal C * ulocNormE m χ u ∧
      ulocNormE m χ u ≤ ENNReal.ofReal C * ulNormE m θ u := by
  obtain ⟨C1, hC1, h1⟩ := ul0_ulNormE_le_uloc m θ χ hθ hχ
  obtain ⟨C2, hC2, h2⟩ := ul0_uloc_le_ulNormE m θ χ hθ hχ
  refine ⟨max C1 C2, lt_max_of_lt_left hC1, fun u => ⟨?_, ?_⟩⟩
  · exact (h1 u).trans (by gcongr; exact le_max_left _ _)
  · exact (h2 u).trans (by gcongr; exact le_max_right _ _)


/-! ### Multipliers and `C_b^m` functions -/

theorem ul0_cbNorm_nonneg (m : ℕ) (f : Euc d → ℝ) : 0 ≤ HRS.cbNorm m f :=
  Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _

/-- **UL-0 `ulocNormE_mul_cb`**: multiplication by a `C_b^m` function (`ulocNormE`, any cutoff). -/
theorem ulocNormE_mul_cb (m : ℕ) (χ : Euc d → ℝ) :
    ∃ C : ℝ, 0 < C ∧ ∀ a : Euc d → ℝ, HRS.MemCb m a → ∀ u : Euc d → ℝ,
      ulocNormE m χ (fun x => a x * u x) ≤
        ENNReal.ofReal (C * HRS.cbNorm m a) * ulocNormE m χ u := by
  obtain ⟨C, hC, h⟩ := HRS.MS.QMul.sobolevNormE_mul_cb_le d m
  refine ⟨C, hC, fun a ha u => ?_⟩
  refine iSup_le fun z => ?_
  have e : (fun x => χ (x - z) * (a x * u x)) = fun x => a x * (χ (x - z) * u x) := by
    funext x; ring
  rw [e]
  refine (h a ha _).trans ?_
  gcongr
  exact le_iSup (fun z : Euc d => sobolevNormE (m : ℝ) fun x => χ (x - z) * u x) z

/-- **UL-0 `ulocNormE_le_cb`**: `‖f‖_{H^m_ul} ≤ C ‖f‖_{C_b^m}`. -/
theorem ulocNormE_le_cb (m : ℕ) (χ : Euc d → ℝ) (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 < C ∧ ∀ f : Euc d → ℝ, HRS.MemCb m f →
      ulocNormE m χ f ≤ ENNReal.ofReal (C * HRS.cbNorm m f) := by
  obtain ⟨C, hC, h⟩ := HRS.MS.QMul.sobolevNormE_mul_cb_le d m
  have hfin := HRS.MS.UlocMW.um_chi_finite hχ.1 hχ.2.1 (s := (m : ℝ)) (Nat.cast_nonneg m)
  set N : ℝ := (sobolevNormE (m : ℝ) χ).toReal with hN
  have hN0 : 0 ≤ N := ENNReal.toReal_nonneg
  refine ⟨C * (N + 1), by positivity, fun f hf => ?_⟩
  refine iSup_le fun z => ?_
  have e : (fun x => χ (x - z) * f x) = fun x => f x * χ (x - z) := by
    funext x; ring
  rw [e]
  refine (h f hf _).trans ?_
  rw [HRS.MS.SobMul.sobolevNormE_translate (m : ℝ) χ z, ← ENNReal.ofReal_toReal hfin, ← hN,
    ← ENNReal.ofReal_mul (by
      have := (ul0_cbNorm_nonneg m f)
      positivity)]
  apply ENNReal.ofReal_le_ofReal
  have h0 := ul0_cbNorm_nonneg m f
  nlinarith [mul_nonneg hC.le h0]

end HRS.MS.Ul
