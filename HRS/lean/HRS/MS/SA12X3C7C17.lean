import HRS.MS.SA12X3C7C16

/-!
# S.A.12 C7 (SA12X3), part C17 (7C): the far term `L²` bound with one fine-lattice Schur kernel
-/

set_option autoImplicit false
set_option maxHeartbeats 12800000

noncomputable section

open MeasureTheory Filter Topology Set Metric
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MH.AdjointRd.Phase2SA12Near

open HRS HRS.Whole HRS.MH.AdjointRd HRS.MH.AdjointRd.Phase2SA12 HRS.MH.AdjointRd.Phase2SA12Construction
  HRS.MH.AdjointRdP

variable {d : ℕ}

theorem sa12x3_far_kernel (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Λ Cb T : ℝ) (χ χh : Euc d → ℝ) (hχ : IsCutoffPair χ χh) :
    ∃ Cs L₁ : ℝ, 0 ≤ Cs ∧ ∀ (b : ℝ → Euc d → Euc d) (Ψ : ℝ → Euc d → Euc d), IsAdvectingDrift m Cb T b →
      IsNegDriftFlow T b Ψ → ∀ (L : ℝ) (γ : Euc d → ℝ), L₁ ≤ L →
      HRS.Whole.AppendixALemmas.IsPeriodicRieszKernel d s L γ → ∀ μ : Euc d → ℝ, ContDiff ℝ ∞ μ →
      (∀ (x : Euc d) (k : Fin d → ℤ), μ (x + L • latticePt k) = μ x) →
      (∀ j ≤ m + 3, ∀ x : Euc d, ∃ k : Fin d → ℤ,
        jbracket (x - L • latticePt k) ^ ((d : ℝ) + 3) * ‖iteratedFDeriv ℝ j μ x‖ ≤ Λ) →
      ∀ τ ∈ Icc (0 : ℝ) T, ∃ Kfin : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0,
        (⨆ z, ∑' z'', (Kfin z z'' : ℝ≥0∞) ≤ ENNReal.ofReal Cs) ∧
        (∀ z'', ∑' z, ENNReal.ofReal (cellWeight d z) * (Kfin z z'' : ℝ≥0∞) ≤
          ENNReal.ofReal Cs * ENNReal.ofReal (cellWeight d z'')) ∧
        ∀ F : Euc d → ℝ, BddJets m F → (∀ (x : Euc d) (k : Fin d → ℤ), F (x + L • latticePt k) = F x) →
          ∀ z : Fin d → ℤ, ∀ n ≤ m, ∀ (idx : Fin n → Fin d) (i j : Fin d),
          ∫ x, (advCutoff χ Ψ τ (cellPt d z) x * sa12x3_Tfar L γ (Ψ τ (cellPt d z))
            (advCutoff χh Ψ τ (cellPt d z)) μ F idx i j x) ^ 2 ≤
            Cs * Λ ^ 2 * (∑' z'', (Kfin z z'' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z'' F)).toReal := by
  obtain ⟨Ct, Lt, hCt, hK⟩ := sa12x3_far_K_ex hd hs0 hsd m Λ Cb T χ χh hχ
  obtain ⟨R', h, hR', hh, hgeom⟩ := sa12x3_geom hd m Cb T χ χh hχ
  obtain ⟨CF, hCF0, hCF⟩ := HRS.MH.Screened.flow_lip_sep_proof hd m Cb T χ χh hχ
  obtain ⟨κ, hκdef⟩ : ∃ κ : ℤ, κ = ⌈Real.sqrt d⌉ := ⟨_, rfl⟩
  have hκ1 : 1 ≤ κ := by
    rw [hκdef]
    exact Int.one_le_ceil_iff.2 (Real.sqrt_pos.2 (by exact_mod_cast hd))
  have hκR : (κ : ℝ) = ⌈Real.sqrt d⌉ := by rw [hκdef]
  set A : ℝ := (1 + κ * Real.sqrt d) ^ ((d : ℝ) + 3) with hA
  set B : ℝ := (1 + Real.sqrt d) ^ ((d : ℝ) + 3) with hB
  set Nr : ℝ := ((sa12x3_Rset d κ).card : ℝ) with hNr
  have hκ0 : (0 : ℝ) ≤ κ := by exact_mod_cast (by omega : (0 : ℤ) ≤ κ)
  set Cs : ℝ := 2 ^ d * Ct + 2 ^ d * A * Nr * Ct * B + Ct with hCs
  have hCs0 : 0 ≤ Cs := by positivity
  refine ⟨Cs, max (max 1 Lt) (2 * (R' + h / 2) + 1), hCs0, ?_⟩
  intro b Ψ hb hΨ L γ hLL hγ μ hμ hμp hμd τ hτ
  have hL1 : 1 ≤ L := (le_max_left _ _).trans ((le_max_left _ _).trans hLL)
  have hLt : Lt ≤ L := (le_max_right _ _).trans ((le_max_left _ _).trans hLL)
  have hRL : R' + h / 2 < L / 2 := by
    have := (le_max_right _ _).trans hLL
    linarith
  have hKex : ∀ r : Fin d → ℤ, ∃ K : (Fin d → ℤ) → (Fin d → ℤ) → ℝ≥0, r ∈ sa12x3_Rset d κ →
      (∀ q, ∑' y, (K q y : ℝ≥0∞) ≤ ENNReal.ofReal Ct) ∧
      (∀ y, ∑' q, ENNReal.ofReal (cellWeight d q) * (K q y : ℝ≥0∞) ≤
        ENNReal.ofReal Ct * ENNReal.ofReal (cellWeight d y)) ∧
      ∀ n' : Fin (m + 1), sa12x3_T7Ineq Ψ τ χ χh L γ μ (n' : ℕ) (sa12x3_e d κ r) Λ Ct K := by
    intro r
    by_cases hr : r ∈ sa12x3_Rset d κ
    · obtain ⟨K, h1, h2, h3⟩ := hK b Ψ hb hΨ L γ hL1 hLt hγ μ hμ hμp hμd τ hτ (sa12x3_e d κ r)
        (sa12x3_e_bounds hκ1 hr).2.2
      exact ⟨K, fun _ => ⟨h1, h2, h3⟩⟩
    · exact ⟨0, fun h' => absurd h' hr⟩
  choose K hKr using hKex
  refine ⟨sa12x3_Kfin κ K, ?_, ?_, ?_⟩
  · refine iSup_le fun z => ?_
    refine (sa12x3_Kfin_row K hCt (fun r hr q => (hKr r hr).1 q) hκ1 z).trans (ENNReal.ofReal_le_ofReal ?_)
    have : 0 ≤ 2 ^ d * A * Nr * Ct * B := by positivity
    linarith
  · intro z''
    refine (sa12x3_Kfin_col hκ1 K hCt (fun r hr y => (hKr r hr).2.1 y) z'').trans ?_
    gcongr
    have : 0 ≤ 2 ^ d * Ct := by positivity
    linarith
  · intro F hF hFp z n hn idx i j
    have hres := sa12x3_res_mem hκ1 z
    obtain ⟨hrow, hcol, hT⟩ := hKr _ hres
    have hdec := sa12x3_cellPt_dec (κ := κ) hκR hκ1 z
    obtain ⟨he0, he1, hen⟩ := sa12x3_e_bounds hκ1 hres
    have hLip := (hCF b Ψ hb hΨ τ hτ).1
    have hLp0 : 0 ≤ Real.exp (CF * τ) := (Real.exp_pos _).le
    have hΨc : Continuous (Ψ τ) := by
      refine LipschitzWith.continuous (LipschitzWith.of_dist_le' (K := Real.exp (CF * τ)) ?_)
      intro x y
      rw [dist_eq_norm, dist_eq_norm]
      exact hLip x y
    have hF1 : ContDiff ℝ ∞ F := hF.1
    have hdF : Continuous (fun y => fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))) :=
      ((hF1.fderiv_right (m := ∞) (by simp)).continuous).clm_apply continuous_const
    have hψp : ∀ (x : Euc d) (k : Fin d → ℤ), fderiv ℝ F (x + L • latticePt k) (EuclideanSpace.single j (1 : ℝ)) =
        fderiv ℝ F x (EuclideanSpace.single j (1 : ℝ)) := by
      intro x k
      have h1 : (fun y => F (y + L • latticePt k)) = F := funext fun y => hFp y k
      have h2 := fderiv_comp_add_right (𝕜 := ℝ) (f := F) (x := x) (L • latticePt k)
      rw [h1] at h2
      rw [← h2]
    have h7 := hT ⟨n, by omega⟩ (Fin.snoc idx i) _ hdF.measurable hψp (fun i => z i / κ)
    rw [← hdec] at h7
    -- geometry and the left-hand side
    obtain ⟨hη_ts, hwN'⟩ := hgeom b Ψ hb hΨ τ hτ (cellPt d z)
    have hRcut := advected_cutoff_jets d hd m Cb T χ χh hχ
    have hcut := hgeom
    have hwcont : Continuous (advCutoff χ Ψ τ (cellPt d z)) := by
      obtain ⟨B1, R1, hB1, hR11, hf⟩ := hRcut
      exact (hf b Ψ hb hΨ τ hτ (cellPt d z)).1.1.continuous
    have hηcont : Continuous (advCutoff χh Ψ τ (cellPt d z)) := by
      obtain ⟨B1, R1, hB1, hR11, hf⟩ := hRcut
      exact (hf b Ψ hb hΨ τ hτ (cellPt d z)).1.2.continuous
    have hwcs : HasCompactSupport (advCutoff χ Ψ τ (cellPt d z)) :=
      sa12x2_advCutoff_hasCompactSupport (hτ.1.trans hτ.2) hb hΨ hτ hχ.1.2.1 _
    have hpd0 : ∀ y, partialDeriv (fun i : Fin 0 => i.elim0 : Fin 0 → Fin d) μ y = μ y := by
      intro y; simp [partialDeriv]
    have hfun : (fun x => advCutoff χ Ψ τ (cellPt d z) x *
          ∫ y in {y | y - Ψ τ (cellPt d z) ∈ centeredBox d L},
            iteratedFDeriv ℝ (n + 1) γ (x - y) (fun l => EuclideanSpace.single ((Fin.snoc idx i : Fin (n + 1) → Fin d) l) (1 : ℝ)) *
              ((1 - advCutoff χh Ψ τ (cellPt d z) y) * (partialDeriv (fun i : Fin 0 => i.elim0 : Fin 0 → Fin d) μ y *
                fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ))))) =
        fun x => advCutoff χ Ψ τ (cellPt d z) x * sa12x3_Tfar L γ (Ψ τ (cellPt d z))
          (advCutoff χh Ψ τ (cellPt d z)) μ F idx i j x := by
      funext x
      simp only [hpd0, sa12x3_Tfar]
      rfl
    have hR'' : R' + h / 2 ≤ R' + h / 2 := le_rfl
    have hL2 := sa12x3_wT_eLp (s := s) hγ hh (by linarith) hR'' hRL (c := Ψ τ (cellPt d z)) (0 : Matrix (Fin d) (Fin d) ℝ)
      hwcont hwcs hηcont hμ.continuous hF1 (fun x hx => hwN' x hx) idx i j
    rw [hfun, hL2] at h7
    -- the right-hand side
    have hcell : ∀ z' : Fin d → ℤ, (eLpNorm ((flowCellAt Ψ τ (latticePt z' + sa12x3_e d κ (fun i => z i % κ))).indicator
          (fun y => fderiv ℝ F y (EuclideanSpace.single j (1 : ℝ)))) 2 volume) ^ 2 ≤
        ∑ ε : Fin d → Fin 2, ENNReal.ofReal (cellMass m Ψ τ (z' + fun i => ((ε i : ℕ) : ℤ)) F) := by
      intro z'
      have hAc := sa12x3_flowCellAt_compact hΨc (latticePt z' + sa12x3_e d κ (fun i => z i % κ))
      rw [sa12x3_eLp_ind hdF hAc.isClosed.measurableSet hAc.isBounded]
      exact sa12x3_shifted_cell_le hΨc hm hF1 j z' he0 he1
    have hmain : ENNReal.ofReal (∫ x, (advCutoff χ Ψ τ (cellPt d z) x * sa12x3_Tfar L γ (Ψ τ (cellPt d z))
          (advCutoff χh Ψ τ (cellPt d z)) μ F idx i j x) ^ 2) ≤
        ENNReal.ofReal (Ct * Λ ^ 2) * ∑' z'', (sa12x3_Kfin κ K z z'' : ℝ≥0∞) *
          ENNReal.ofReal (cellMass m Ψ τ z'' F) := by
      refine h7.trans ?_
      rw [sa12x3_Kfin_mass K z (fun y => ENNReal.ofReal (cellMass m Ψ τ y F))]
      gcongr with z'
      exact hcell z'
    -- finiteness of the mass sum
    obtain ⟨Mbar, hMbar⟩ := sa12x3_mass_bdd hLip hLp0 hΨc hF
    have hrowK : ∑' z'', (sa12x3_Kfin κ K z z'' : ℝ≥0∞) ≤ ENNReal.ofReal Cs := by
      refine (sa12x3_Kfin_row K hCt (fun r hr q => (hKr r hr).1 q) hκ1 z).trans (ENNReal.ofReal_le_ofReal ?_)
      have : 0 ≤ 2 ^ d * A * Nr * Ct * B := by positivity
      linarith
    have hX : ∑' z'', (sa12x3_Kfin κ K z z'' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z'' F) ≠ ⊤ := by
      refine ne_top_of_le_ne_top (ENNReal.mul_ne_top ENNReal.ofReal_ne_top ENNReal.ofReal_ne_top
        |> fun h' => (h' : ENNReal.ofReal Cs * ENNReal.ofReal Mbar ≠ ⊤)) ?_
      calc ∑' z'', (sa12x3_Kfin κ K z z'' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z'' F)
          ≤ ∑' z'', (sa12x3_Kfin κ K z z'' : ℝ≥0∞) * ENNReal.ofReal Mbar :=
            ENNReal.tsum_le_tsum fun z'' => by gcongr; exact hMbar z''
        _ = (∑' z'', (sa12x3_Kfin κ K z z'' : ℝ≥0∞)) * ENNReal.ofReal Mbar := ENNReal.tsum_mul_right
        _ ≤ ENNReal.ofReal Cs * ENNReal.ofReal Mbar := by gcongr
    set X := ∑' z'', (sa12x3_Kfin κ K z z'' : ℝ≥0∞) * ENNReal.ofReal (cellMass m Ψ τ z'' F) with hXdef
    have hXr : ENNReal.ofReal (Ct * Λ ^ 2) * X = ENNReal.ofReal (Ct * Λ ^ 2 * X.toReal) := by
      rw [ENNReal.ofReal_mul (p := Ct * Λ ^ 2) (q := X.toReal) (by positivity), ENNReal.ofReal_toReal hX]
    rw [hXr] at hmain
    have h8 := (ENNReal.ofReal_le_ofReal_iff (by positivity)).1 hmain
    have hCtCs : Ct ≤ Cs := by
      have : 0 ≤ 2 ^ d * Ct + 2 ^ d * A * Nr * Ct * B := by positivity
      linarith
    calc _ ≤ Ct * Λ ^ 2 * X.toReal := h8
      _ ≤ Cs * Λ ^ 2 * X.toReal := by gcongr

end HRS.MH.AdjointRd.Phase2SA12Near
