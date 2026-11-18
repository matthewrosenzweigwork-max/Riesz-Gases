import HRS.Commutator.Torus.NRSTAux17
import HRS.Commutator.Torus.Layer

/-!
# NRS-T, part 18: the torus NRS estimate, conditional on the base case and the multiplier bound
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped BigOperators ComplexConjugate ENNReal

namespace HRS.Commutator.TorusNote.NRST

open HRS HRS.Commutator

variable {d : ℕ} {s : ℝ}

theorem nrst_main (hd : 3 ≤ d) (hs0 : 0 ≤ s) (hsd : s < (d : ℝ) - 2) {C0 CB : ℝ} (hC0 : 0 ≤ C0)
    (hCB : 0 ≤ CB)
    (hbase : ∀ (V : Fin d → TPA d), (∀ j x, (ev (V j) x).im = 0) → ∀ L : ℝ, 0 ≤ L →
      IsLipschitzVF L (vOf V) → ∀ h : TPA d, IsRealT h →
        ‖Jf V (2 * (((d : ℝ) - s) / 2 - ⌊((d : ℝ) - s) / 2⌋₊)) h‖ ≤
          C0 * L * hom (((d : ℝ) - s) / 2 - ⌊((d : ℝ) - s) / 2⌋₊) h)
    (hmul : ∀ (V : Fin d → TPA d), (∀ j x, (ev (V j) x).im = 0) → ∀ K : ℝ,
      TorusSubTransport d s (vOf V) K → ∀ m : ℕ, 1 ≤ m → m ≤ ⌊((d : ℝ) - s) / 2⌋₊ →
        ∀ (a c : Fin d) (Γ : TPA d), IsRealT Γ → Γ.coeff 0 = 0 →
          hom (((d : ℝ) - s) / 2 - ⌊((d : ℝ) - s) / 2⌋₊ + m - 1) (dd a (V c) * Γ) ≤
            (CB * K) ^ 2 * hom (((d : ℝ) - s) / 2 - ⌊((d : ℝ) - s) / 2⌋₊ + m - 1) Γ) :
    ∃ C : ℝ, 0 < C ∧ ∀ (v : Torus d → Euc d) (K : ℝ), TorusSubTransport d s v K →
      ∀ a : Torus d → ℝ, Torus.IsSmooth a → ∫ x, a x = 0 →
        ENNReal.ofReal |CcommFunT (periodicRieszGrad d s) v a| ≤
          ENNReal.ofReal (C * K) * homSqT (-Whole.alphaE d s) (fun k => Torus.fcoef a k) := by
  set k : ℕ := ⌊((d : ℝ) - s) / 2⌋₊ with hk
  have hd1 : 1 ≤ d := by omega
  have hsd' : s < (d : ℝ) := by linarith
  have hα0 : 0 ≤ ((d : ℝ) - s) / 2 := by linarith
  have hk1 : (k : ℝ) ≤ ((d : ℝ) - s) / 2 := Nat.floor_le hα0
  have hc0 : 0 < rieszConst d s := rieszConst_pos (by omega) hs0 hsd'
  have hCm : 0 ≤ Cm d C0 CB k := Cm_nonneg hC0 hCB k
  refine ⟨2 * rieszConst d s * Cm d C0 CB k + 1, by positivity, ?_⟩
  intro v K hv a ha hmean
  set C : ℝ := 2 * rieszConst d s * Cm d C0 CB k + 1 with hC
  obtain ⟨L, F, hL0, hF0, hLip, hw, hLF⟩ := hv
  have hv' : TorusSubTransport d s v K := ⟨L, F, hL0, hF0, hLip, hw, hLF⟩
  have hLK : L ≤ K := by linarith
  have hK0 : 0 ≤ K := hL0.trans hLK
  have hvc : Continuous v := IsLipschitzVF.continuous hL0 hLip
  have hac : Continuous a := smooth_continuous ha
  set Bd : ℝ := ∑' k : Lattice d, ‖Torus.fcoef a k‖ with hBd
  have hBd0 : 0 ≤ Bd := tsum_nonneg fun _ => norm_nonneg _
  set X : ℝ≥0∞ := ENNReal.ofReal (C * K) * homSqT (-Whole.alphaE d s) (fun k => Torus.fcoef a k) with hX
  -- the bound for trigonometric polynomials
  have key : ∀ n m : ℕ, ENNReal.ofReal |CcommFunT (periodicRieszGrad d s) (vOf (Vn n v))
      (aOf (truncOf m a))| ≤ X := by
    intro n m
    have hAr : ∀ x, (ev (truncOf m a) x).im = 0 := ev_real_of_symm _ (truncOf_symm m a)
    have h1 := trig_bound hd hs0 hsd hk1 (Vn n v) (truncOf m a) hL0 hLK hC0 hCB (Vn_real n) hAr
      (truncOf_zero m hmean) (vOf_Vn_lip hvc hL0 hLip n)
      (fun h hh => by
        have := hbase (Vn n v) (Vn_real n) L hL0 (vOf_Vn_lip hvc hL0 hLip n) h hh
        refine this.trans ?_
        exact mul_le_mul_of_nonneg_right (mul_le_mul_of_nonneg_left hLK hC0) (hom_nonneg _ _))
      (hmul (Vn n v) (Vn_real n) K (transport_moll hs0 hsd hv' n))
    have h2 : |CcommFunT (periodicRieszGrad d s) (vOf (Vn n v)) (aOf (truncOf m a))| ≤
        C * K * hom (-(((d : ℝ) - s) / 2)) (truncOf m a) := by
      refine h1.trans ?_
      have hh := hom_nonneg (-(((d : ℝ) - s) / 2)) (truncOf m a)
      have : 2 * rieszConst d s * Cm d C0 CB k * K ≤ C * K := by
        rw [hC]; nlinarith
      nlinarith [mul_le_mul_of_nonneg_right this hh]
    calc ENNReal.ofReal |CcommFunT (periodicRieszGrad d s) (vOf (Vn n v)) (aOf (truncOf m a))|
        ≤ ENNReal.ofReal (C * K * hom (-(((d : ℝ) - s) / 2)) (truncOf m a)) :=
          ENNReal.ofReal_le_ofReal h2
      _ = ENNReal.ofReal (C * K) * ENNReal.ofReal (hom (-(((d : ℝ) - s) / 2)) (truncOf m a)) :=
          ENNReal.ofReal_mul (by positivity)
      _ ≤ X := by
          rw [hX]
          gcongr
          exact ofReal_hom_trunc_le _ m a
  -- limit in `m`
  have hlim_m : ∀ n : ℕ, ENNReal.ofReal |CcommFunT (periodicRieszGrad d s) (vOf (Vn n v)) a| ≤ X := by
    intro n
    have ht := CcommFunT_tendsto (s := s) hd1 hs0 hsd' (L := L) (B := Bd) hL0 hBd0
      (vOf_Vn_lip hvc hL0 hLip n) hac (vn := fun _ => vOf (Vn n v)) (wn := fun m => aOf (truncOf m a))
      (fun _ => vOf_Vn_lip hvc hL0 hLip n)
      (fun m => Complex.continuous_re.comp (continuous_ev _))
      (fun m x => abs_aOf_truncOf_le ha m x) (fun x => tendsto_const_nhds)
      (fun x => truncOf_tendsto ha x)
    have ht' : Tendsto (fun m : ℕ => ENNReal.ofReal |CcommFunT (periodicRieszGrad d s) (vOf (Vn n v))
        (aOf (truncOf m a))|) atTop
        (𝓝 (ENNReal.ofReal |CcommFunT (periodicRieszGrad d s) (vOf (Vn n v)) a|)) :=
      (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_abs.tendsto _).comp ht)
    exact le_of_tendsto' ht' fun m => key n m
  -- limit in `n`
  have ht := CcommFunT_tendsto (s := s) hd1 hs0 hsd' (L := L) (B := Bd) hL0 hBd0 hLip hac
    (vn := fun n => vOf (Vn n v)) (wn := fun _ => a) (fun n => vOf_Vn_lip hvc hL0 hLip n)
    (fun _ => hac) (fun _ x => Torus.abs_le_tsum_fcoef hac (smooth_summable ha) x) (fun x => vOf_Vn_tendsto hvc x) (fun x => tendsto_const_nhds)
  have ht' : Tendsto (fun n : ℕ => ENNReal.ofReal |CcommFunT (periodicRieszGrad d s) (vOf (Vn n v)) a|)
      atTop (𝓝 (ENNReal.ofReal |CcommFunT (periodicRieszGrad d s) v a|)) :=
    (ENNReal.continuous_ofReal.tendsto _).comp ((continuous_abs.tendsto _).comp ht)
  exact le_of_tendsto' ht' hlim_m

end HRS.Commutator.TorusNote.NRST
