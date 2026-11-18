import HRS.MS.Fp81S21ShiftedMild5
import HRS.MS.S81sItoShift

/-!
# HRS S2.1(iii), packet 9c: reconstruction of shifted noise

The compiled feature is r2WindowFeature and the Hilbert integrand is s105Phi.
Pairing with s52y1 and s52y2 identifies the reconstruction with the local
scalar integral; s81s_ito_shift then identifies it with the compiled
physical-time noise difference.

The hC and hK assumptions are the S21mData.hC and .hK contracts produced by
S104b.s104b_data. The hphysical premise is produced by the shifted feature
regularity theorem in Fp81S21ShiftedMild3.
-/

set_option autoImplicit false
set_option maxHeartbeats 400000

noncomputable section

open MeasureTheory Filter Topology Set ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Fp81.S21

open HRS HRS.Whole HRS.MS.R2GenInit HRS.MS.R2Interp HRS.MS.S52 HRS.MS.GenPath
open HRS.MS.R26T3 HRS.MD.EQLawPath HRS.MP.RdRem

/-- At a fixed local time the shifted feature martingale reconstructs the
compiled shifted noise difference. -/
theorem fp81s21_shiftedNoise_reconstruction_at
    (p : Parameters) {δ : ℝ} (R : Trajectory p δ)
    {N : ℕ} (hN : 2 ≤ N) (A : Particle R N) (F : FilteredParticle A)
    {H b : ℝ} (hH : 0 < H) (hb : 0 ≤ b)
    (hphysical : S105Feat p.d ((wholeSpaceIndex p.d : ℕ) : ℝ) H (b + H)
      (fp81s21_shiftedNoiseFeatureFamily p R H b))
    (hC : OscAdjointInput (r26t3_coeff R)
      ((wholeSpaceIndex p.d : ℕ) : ℝ) (b + H))
    (hK : ∀ (a : Fin p.d) (r : ℝ), r ∈ Icc (0 : ℝ) (b + H) → ∀ x,
      S105WinK (r26t3_coeff R) ((wholeSpaceIndex p.d : ℕ) : ℝ)
        H b a r x)
    {s : ℝ} (hs : s ∈ Icc (0 : ℝ) H) (α : MultiIndex p.d) :
    ∀ᵐ ζ ∂A.P,
      OscDual.coord (reconstructPath ((wholeSpaceIndex p.d : ℕ) : ℝ) H
        (Classical.choose (fp81s21_shiftedNoise_feature_martingale
          p R hN A F hH hb hphysical)) ζ s) α =
        fp81s21_shiftedNoiseDiff p R A F b (b + s) α ζ := by
  classical
  let m : ℝ := ((wholeSpaceIndex p.d : ℕ) : ℝ)
  let ub : ℝ≥0 := b.toNNReal
  have hub : (ub : ℝ) = b := Real.coe_toNNReal _ hb
  let ℱb := HRS.Whole.BreakdownS81.s81b_shiftFil F.ℱ ub
  let Wb := HRS.MD.EQLawPath.shiftProc F.Wc ub
  let Xb := HRS.Whole.S79.s79p_shiftX ub F.X
  let Γ := fp81s21_shiftedNoiseLocalFeatureFamily p R H b
  let Φ := s105Phi Γ H p.β⁻¹ Xb
  let M := Classical.choose (fp81s21_shiftedNoise_feature_martingale
    p R hN A F hH hb hphysical)
  have hfiltered := HRS.Whole.BreakdownS81.s81b_filtered_shift F.filtered ub
  have hW0 : IsCylindricalBrownian A.P ℱb Wb :=
    HRS.GF.gfb3_isCylindricalBrownian_of_filtration hfiltered.brownian
  have hW : IsBrownianFiltration A.P ℱb Wb := HRS.MS.S52.s52_brownian_of_cyl hW0
  have hq : 0 ≤ p.β⁻¹ := inv_nonneg.mpr p.hβ.le
  have hNpos : (0 : ℝ) < N := by exact_mod_cast (show 0 < N by omega)
  have hIto := (Classical.choose_spec (fp81s21_shiftedNoise_feature_martingale
    p R hN A F hH hb hphysical)).1
  have hM : IsHilbertItoIntegral A.P ℱb Wb Φ M := by
    simpa [M, ℱb, Wb, Φ, Γ] using hIto
  have hlocal : S105Feat p.d m H H Γ :=
    fp81s21_shiftedNoiseLocalFeature_regular p R hH.le hb hphysical
  have hΦ : ∀ T' : ℝ, IsHSIntegrand A.P ℱb T' Φ := by
    intro T'
    exact s105_phi_isHS hH.le hlocal N p.β⁻¹ A.P ℱb Xb
      hfiltered.progressive T'
  let y1 := s52y1 m H s α
  let y2 := s52y2 m H α
  let c0 : ℝ := Real.sqrt (2 * p.β⁻¹ / N)
  let u1 : ℝ → A.Ω → Fin N × Fin p.d → ℝ :=
    fun r ζ ia => inner ℝ (Φ r ζ ia) y1
  let u2 : ℝ → A.Ω → Fin N × Fin p.d → ℝ :=
    fun r ζ ia => inner ℝ (Φ r ζ ia) y2
  let ud : ℝ → A.Ω → Fin N × Fin p.d → ℝ := fun r ζ => u1 r ζ - u2 r ζ
  have hL1 : IsProgressiveL2 A.P ℱb u1 := s52_pairL2 hΦ y1
  have hL2 : IsProgressiveL2 A.P ℱb u2 := s52_pairL2 hΦ y2
  have hLd : IsProgressiveL2 A.P ℱb ud := by
    dsimp [ud]
    exact isProgressiveL2_sub hL1 hL2
  have hu2val : ∀ r ∈ Icc (0 : ℝ) H, ∀ ζ (ia : Fin N × Fin p.d),
      u2 r ζ ia = c0 * gradComp ia.2
        (oscTestFun m α) (Xb (Real.toNNReal r) ζ ia.1) := by
    intro r hr ζ ia
    have hphysr : b + r ∈ Icc (0 : ℝ) (b + H) := by
      constructor <;> linarith [hr.1, hr.2]
    have hkr := hK ia.2 (b + r) hphysr (Xb (Real.toNNReal r) ζ ia.1)
    have hpair := fp81s21_shiftedNoiseFeature_y2 p R hb hr ia.2
      (Xb (Real.toNNReal r) ζ ia.1) α hkr
    change inner ℝ
      (Real.sqrt (2 * p.β⁻¹ / N) •
        (fp81s21_shiftedNoiseLocalFeatureFamily p R H b ia.2
          (mrrClamp H r) (Xb (Real.toNNReal r) ζ ia.1)))
      (s52y2 m H α) = _
    rw [real_inner_smul_left]
    rw [mrrClamp_of_mem hr]
    change c0 * inner ℝ (fp81s21_shiftedNoiseFeature p R H b r ia.2
      (Xb (Real.toNNReal r) ζ ia.1)) (s52y2 m H α) =
      c0 * gradComp ia.2 (oscTestFun m α) (Xb (Real.toNNReal r) ζ ia.1)
    rw [hpair]
  have hu1val : ∀ r ∈ Icc (0 : ℝ) H, ∀ ζ (ia : Fin N × Fin p.d),
      u1 r ζ ia = c0 * (if r ≤ s then
        gradComp ia.2 (propagatorW (r26t3_coeff R) (b + r) (b + s)
          (oscTestFun m α)) (Xb (Real.toNNReal r) ζ ia.1)
        else gradComp ia.2 (oscTestFun m α) (Xb (Real.toNNReal r) ζ ia.1)) := by
    intro r hr ζ ia
    have hphysr : b + r ∈ Icc (0 : ℝ) (b + H) := by
      constructor <;> linarith [hr.1, hr.2]
    have hkr := hK ia.2 (b + r) hphysr (Xb (Real.toNNReal r) ζ ia.1)
    have hpair := fp81s21_shiftedNoiseFeature_y1 p R hb hr hs hC
      ia.2 (Xb (Real.toNNReal r) ζ ia.1) α hkr
    change inner ℝ
      (Real.sqrt (2 * p.β⁻¹ / N) •
        (fp81s21_shiftedNoiseLocalFeatureFamily p R H b ia.2
          (mrrClamp H r) (Xb (Real.toNNReal r) ζ ia.1)))
      (s52y1 m H s α) = _
    rw [real_inner_smul_left]
    rw [mrrClamp_of_mem hr]
    change c0 * inner ℝ (fp81s21_shiftedNoiseFeature p R H b r ia.2
      (Xb (Real.toNNReal r) ζ ia.1)) (s52y1 m H s α) =
      c0 * (if r ≤ s then
        gradComp ia.2 (propagatorW (r26t3_coeff R) (b + r) (b + s)
          (oscTestFun m α)) (Xb (Real.toNNReal r) ζ ia.1)
        else gradComp ia.2 (oscTestFun m α) (Xb (Real.toNNReal r) ζ ia.1))
    rw [hpair]
  have hagreeE : ∀ r ∈ Icc (0 : ℝ) H, ∀ ζ,
      ud r ζ = (fun r ζ ia => if r ≤ s then ud r ζ ia else 0) r ζ := by
    intro r hr ζ
    funext ia
    by_cases hrs : r ≤ s
    · simp [hrs]
    · have h1 := hu1val r hr ζ ia
      have h2 := hu2val r hr ζ ia
      change u1 r ζ ia - u2 r ζ ia =
        (if r ≤ s then u1 r ζ ia - u2 r ζ ia else 0)
      rw [h1, h2]
      simp [hrs]
  have hLdt : IsProgressiveL2 A.P ℱb
      (fun r ζ ia => if r ≤ s then ud r ζ ia else 0) := by
    exact s52_isProgressiveL2_ite hLd (measurableSet_Iic (a := s))
  have hlcE := s52_lc hW hLd hLdt hH.le hagreeE
  have hkillE := s52_kill hW hLd hs.1
  let ψloc : ℝ → A.Ω → Fin N × Fin p.d → ℝ := fun r ζ ia =>
    if r ∈ Icc (0 : ℝ) s then c0 *
      gradComp ia.2 (propagatorW (r26t3_coeff R) (b + r) (b + s)
        (oscTestFun m α)) (Xb (Real.toNNReal r) ζ ia.1) else 0
  have hLψ : IsProgressiveL2 A.P ℱb ψloc := by
    have heq : ψloc = fun r ζ ia => if r ∈ Icc (0 : ℝ) s then u1 r ζ ia else 0 := by
      funext r ζ ia
      by_cases hrs : r ∈ Icc (0 : ℝ) s
      · have hrH : r ∈ Icc (0 : ℝ) H := ⟨hrs.1, hrs.2.trans hs.2⟩
        rw [hu1val r hrH ζ ia]
        simp [ψloc, Set.mem_Icc, hrs.1, hrs.2]
      · by_cases h0 : 0 ≤ r <;> by_cases hsr : r ≤ s
        · exact (hrs ⟨h0, hsr⟩).elim
        · simp [ψloc, Set.mem_Icc, h0, hsr]
        · simp [ψloc, Set.mem_Icc, h0, hsr]
        · simp [ψloc, Set.mem_Icc, h0, hsr]
    rw [heq]
    exact s52_isProgressiveL2_ite hL1 measurableSet_Icc
  have hagreeG : ∀ r ∈ Icc (0 : ℝ) s, ∀ ζ, u1 r ζ = ψloc r ζ := by
    intro r hr ζ
    funext ia
    have hrH : r ∈ Icc (0 : ℝ) H := ⟨hr.1, hr.2.trans hs.2⟩
    rw [hu1val r hrH ζ ia]
    simp [ψloc, Set.mem_Icc, hr.1, hr.2]
  have hlcG := s52_lc hW hL1 hLψ hs.1 hagreeG
  have hp1H := s52_pair_ito hW hM y1
    (pc_isProgressiveL2_inner hΦ y1 Finset.univ) hH.le
  have hp2H := s52_pair_ito hW hM y2
    (pc_isProgressiveL2_inner hΦ y2 Finset.univ) hH.le
  have hp2s := s52_pair_ito hW hM y2
    (pc_isProgressiveL2_inner hΦ y2 Finset.univ) hs.1
  have hsub := itoIntegral_sub hW hL1 hL2
  have hAdj : ∃ f, IsClassicalAdjointW (r26t3_coeff R) (b + s)
      (oscTestFun m α) f :=
    fp81s21_adjoint_of_osc_test p R
      (HRS.MS.GenPath.s56_isOscTest m α) (by linarith [hs.1, hb])
  let f : ℝ → Euc p.d → ℝ :=
    fun r => propagatorW (r26t3_coeff R) r (b + s) (oscTestFun m α)
  have hf : IsClassicalAdjointW (r26t3_coeff R) (b + s)
      (oscTestFun m α) f := by
    exact s102_propagator_classical hAdj
  have hOrigL2 : IsProgressiveL2 A.P F.ℱ
      (s102_Ig f (b + s) F.X) := by
    obtain ⟨Bg, hBg⟩ := s102_Ig_bdd hf F.X
    exact IsProgressiveL2.of_bounded A.P
      (s102_Ig_progressive hf F.filtered.progressive) Bg hBg
  have hOrigScaled : IsProgressiveL2 A.P F.ℱ
      (fun r ζ => c0 • s102_Ig f (b + s) F.X r ζ) :=
    hOrigL2.smul c0
  have hShift : ∀ r : ℝ, 0 < r → ∀ ζ ia,
      ψloc r ζ ia = (c0 • s102_Ig f (b + s) F.X (b + r) ζ) ia := by
    intro r hr ζ ia
    have hr0 : 0 ≤ r := le_of_lt hr
    have htime : (r ∈ Icc (0 : ℝ) s) = (b + r ∈ Icc (0 : ℝ) (b + s)) := by
      apply propext
      constructor
      · rintro ⟨h0, hrs⟩
        exact ⟨by linarith [hb, h0], by linarith [hrs]⟩
      · rintro ⟨h0, hrs⟩
        exact ⟨by linarith [hb, h0], by linarith [hrs]⟩
    have hxshift : Xb (Real.toNNReal r) ζ ia.1 = F.X (Real.toNNReal (b + r)) ζ ia.1 := by
      simp [Xb, HRS.Whole.S79.s79p_shiftX, ub,
        Real.toNNReal_add hb hr0, Real.toNNReal_coe]
    simp only [ψloc, htime, hxshift, s102_Ig, Pi.smul_apply, smul_eq_mul]
    split_ifs <;> simp [f]
  have hShift' : ∀ r : ℝ, 0 < r → ∀ ζ ia,
      ψloc r ζ ia = (c0 • s102_Ig f (b + s) F.X ((ub : ℝ) + r) ζ) ia := by
    intro r hr ζ ia
    simpa only [hub] using hShift r hr ζ ia
  have hItoShift := HRS.Whole.S81S.s81s_ito_shift F.filtered.brownian ub
    hOrigScaled hLψ hShift'
  have hsmulOrig := itoIntegral_smul F.filtered.brownian hOrigL2 c0
  filter_upwards [hp1H, hp2H, hp2s, hsub, hlcE, hkillE, hlcG,
    hItoShift, hsmulOrig] with ζ h1 h2 h3 h4 h5 h6 h7 h8 h9
  have hrec := s52_coord_recon hs.1 hs.2 M ζ α
  have k0a : inner ℝ (M H ζ) y1 = itoIntegral A.P ℱb Wb u1 H ζ := h1
  have k0b : inner ℝ (M H ζ) y2 = itoIntegral A.P ℱb Wb u2 H ζ := h2
  have k0c : inner ℝ (M s ζ) y2 = itoIntegral A.P ℱb Wb u2 s ζ := h3
  have k1 : itoIntegral A.P ℱb Wb ud H ζ =
      itoIntegral A.P ℱb Wb u1 H ζ - itoIntegral A.P ℱb Wb u2 H ζ := h4 H
  have k3 : itoIntegral A.P ℱb Wb ud (min H H) ζ =
      itoIntegral A.P ℱb Wb (fun r ζ ia => if r ≤ s then ud r ζ ia else 0)
        (min H H) ζ := h5 H hH.le
  have k4 : itoIntegral A.P ℱb Wb
      (fun r ζ ia => if r ≤ s then ud r ζ ia else 0) H ζ =
      itoIntegral A.P ℱb Wb ud (min H s) ζ := h6 H hH.le
  have k5 : itoIntegral A.P ℱb Wb u1 (min s s) ζ =
      itoIntegral A.P ℱb Wb ψloc (min s s) ζ := h7 s hs.1
  rw [min_self] at k3 k5
  rw [min_eq_right hs.2] at k4
  have hscaled := h8 s hs.1
  have hscaled_b : itoIntegral A.P ℱb Wb ψloc s ζ =
      itoIntegral A.P F.ℱ F.Wc
        (fun r ζ => c0 • s102_Ig f (b + s) F.X r ζ)
        (b + s) ζ -
      itoIntegral A.P F.ℱ F.Wc
        (fun r ζ => c0 • s102_Ig f (b + s) F.X r ζ) b ζ := by
    simpa only [hub] using hscaled
  have hnoise : c0 * (itoIntegral A.P F.ℱ F.Wc
        (s102_Ig f (b + s) F.X) (b + s) ζ -
      itoIntegral A.P F.ℱ F.Wc
        (s102_Ig f (b + s) F.X) b ζ) =
      fp81s21_shiftedNoiseDiff p R A F b (b + s) α ζ := by
    change c0 * (itoIntegral A.P F.ℱ F.Wc
        (s102_Ig f (b + s) F.X) (b + s) ζ -
      itoIntegral A.P F.ℱ F.Wc
        (s102_Ig f (b + s) F.X) b ζ) =
      (Real.sqrt N * (Real.sqrt (2 * p.β⁻¹) / N)) * _
    rw [← s105_sqrt_q (by omega : 0 < N) hq]
  have hsub_s : itoIntegral A.P ℱb Wb ud s ζ =
      itoIntegral A.P ℱb Wb u1 s ζ - itoIntegral A.P ℱb Wb u2 s ζ := by
    have hfun : ud = (fun r ζ ia => u1 r ζ ia - u2 r ζ ia) := by
      funext r ζ ia
      rfl
    rw [hfun]
    exact h4 s
  have hcoord : OscDual.coord (reconstructPath m H M ζ s) α =
      itoIntegral A.P ℱb Wb ψloc s ζ := by
    rw [hrec, k0a, k0b, k0c]
    calc
      _ = itoIntegral A.P ℱb Wb u1 H ζ -
          itoIntegral A.P ℱb Wb u2 H ζ +
          itoIntegral A.P ℱb Wb u2 s ζ := by rfl
      _ = itoIntegral A.P ℱb Wb ud H ζ +
          itoIntegral A.P ℱb Wb u2 s ζ := by rw [k1]
      _ = itoIntegral A.P ℱb Wb
            (fun r ζ ia => if r ≤ s then ud r ζ ia else 0) H ζ +
          itoIntegral A.P ℱb Wb u2 s ζ := by rw [k3]
      _ = itoIntegral A.P ℱb Wb ud s ζ +
          itoIntegral A.P ℱb Wb u2 s ζ := by rw [k4]
      _ = itoIntegral A.P ℱb Wb u1 s ζ := by rw [hsub_s]; ring
      _ = itoIntegral A.P ℱb Wb ψloc s ζ := k5
  rw [hcoord, hscaled_b, h9 (b + s), h9 b]
  calc
    _ = c0 * (itoIntegral A.P F.ℱ F.Wc
          (s102_Ig f (b + s) F.X) (b + s) ζ -
        itoIntegral A.P F.ℱ F.Wc
          (s102_Ig f (b + s) F.X) b ζ) := by ring
    _ = fp81s21_shiftedNoiseDiff p R A F b (b + s) α ζ := hnoise

#print axioms HRS.Fp81.S21.fp81s21_shiftedNoise_reconstruction_at

end HRS.Fp81.S21

end
