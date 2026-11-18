import HRS.MS.DecStatAux1

/-!
# SA4, packet 2: the covariance test bound `Sa4Test` from `C_b^{m_*}` bounds only

`Sa4Test d s χ C₀ᶜ C`: the test inequality of `B:lem:test-cutoff` for `h_{fg} = ∇f·∇g`, for `f, g ∈ C_b^{m_*}`, `s ∈ [0, d)`.
It is `sa2_pathwise_core` at the Sobolev index `mm = d/2 + 1 ≥ (d-s)/2`; the `H^{mm}` localisation of `h_{fg}` follows from
`ulocNormE_mul_cb`/`ulocNormE_le_cb` (`m_* = mm + 2`), so no uloc bound on `f` is needed.
-/

noncomputable section

open MeasureTheory Filter Topology
open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MS.MainRdStat
open scoped ENNReal NNReal ContDiff

namespace HRS.MS.DecStat

variable {d : ℕ}

/-- the Sobolev index of the test inequality -/
def sa4mm (d : ℕ) : ℕ := d / 2 + 1

theorem sa4_mStar_eq (d : ℕ) : mStar d = sa4mm d + 2 := by unfold mStar sa4mm; omega

theorem sa4_hSob {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (f g : Euc d → ℝ), MemCb (mStar d) f → MemCb (mStar d) g → ∀ Xf Xg : ℝ, 0 ≤ Xf → 0 ≤ Xg →
      cbNorm (mStar d) f ≤ Xf → cbNorm (mStar d) g ≤ Xg → ∀ z : Euc d,
        sobolevNormE ((sa4mm d : ℕ) : ℝ) (fun x => χ (x - z) * sa2h f g x) ≤ ENNReal.ofReal (C * Xf * Xg) := by
  obtain ⟨Cu, hCu0, hCu⟩ := HRS.MS.Ul.ulocNormE_le_cb (d := d) (sa4mm d) χ hχ
  obtain ⟨Cm, hCm0, hCm⟩ := HRS.MS.QMul.sobolevNormE_mul_cb_le d (sa4mm d)
  refine ⟨d * (Cm * Cu), by positivity, fun f g hf hg Xf Xg hXf hXg hcf hcg z => ?_⟩
  have hmm : mStar d = (sa4mm d + 1) + 1 := by rw [sa4_mStar_eq]
  have hf' : MemCb ((sa4mm d + 1) + 1) f := hmm ▸ hf
  have hg' : MemCb ((sa4mm d + 1) + 1) g := hmm ▸ hg
  have hcf' : cbNorm ((sa4mm d + 1) + 1) f ≤ Xf := hmm ▸ hcf
  have hcg' : cbNorm ((sa4mm d + 1) + 1) g ≤ Xg := hmm ▸ hcg
  -- the coordinate derivatives
  have hdf : ∀ j : Fin d, MemCb (sa4mm d) (fun x => fderiv ℝ f x (EuclideanSpace.single j 1)) ∧
      cbNorm (sa4mm d) (fun x => fderiv ℝ f x (EuclideanSpace.single j 1)) ≤ Xf := by
    intro j
    obtain ⟨h1, h2⟩ := sa4_vj_memCb hf' j
    exact ⟨sa2_memCb_mono (Nat.le_succ _) h1, (sa2_cbNorm_mono (Nat.le_succ _) _).trans (h2.trans hcf')⟩
  have hdg : ∀ j : Fin d, MemCb (sa4mm d) (fun x => fderiv ℝ g x (EuclideanSpace.single j 1)) ∧
      cbNorm (sa4mm d) (fun x => fderiv ℝ g x (EuclideanSpace.single j 1)) ≤ Xg := by
    intro j
    obtain ⟨h1, h2⟩ := sa4_vj_memCb hg' j
    exact ⟨sa2_memCb_mono (Nat.le_succ _) h1, (sa2_cbNorm_mono (Nat.le_succ _) _).trans (h2.trans hcg')⟩
  have hfun : (fun x => χ (x - z) * sa2h f g x) = fun x => ∑ j : Fin d,
      fderiv ℝ g x (EuclideanSpace.single j 1) *
        (χ (x - z) * fderiv ℝ f x (EuclideanSpace.single j 1)) := by
    funext x
    unfold sa2h
    rw [Finset.mul_sum]
    exact Finset.sum_congr rfl fun j _ => by ring
  rw [hfun]
  have hterm : ∀ j : Fin d, sobolevNormE ((sa4mm d : ℕ) : ℝ) (fun x => fderiv ℝ g x (EuclideanSpace.single j 1) *
      (χ (x - z) * fderiv ℝ f x (EuclideanSpace.single j 1))) ≤
      ENNReal.ofReal (Cm * Xg) * ENNReal.ofReal (Cu * Xf) := by
    intro j
    refine (hCm _ (hdg j).1 _).trans ?_
    have h1 : sobolevNormE ((sa4mm d : ℕ) : ℝ) (fun x => χ (x - z) * fderiv ℝ f x (EuclideanSpace.single j 1)) ≤
        ENNReal.ofReal (Cu * Xf) := by
      refine (le_iSup (fun z : Euc d => sobolevNormE ((sa4mm d : ℕ) : ℝ)
        fun x => χ (x - z) * fderiv ℝ f x (EuclideanSpace.single j 1)) z).trans ?_
      refine (hCu _ (hdf j).1).trans (ENNReal.ofReal_le_ofReal ?_)
      exact mul_le_mul_of_nonneg_left (hdf j).2 hCu0.le
    gcongr
    exact (hdg j).2
  calc sobolevNormE ((sa4mm d : ℕ) : ℝ) (fun x => ∑ j : Fin d, fderiv ℝ g x (EuclideanSpace.single j 1) *
        (χ (x - z) * fderiv ℝ f x (EuclideanSpace.single j 1)))
      ≤ ∑ j : Fin d, sobolevNormE ((sa4mm d : ℕ) : ℝ) (fun x => fderiv ℝ g x (EuclideanSpace.single j 1) *
        (χ (x - z) * fderiv ℝ f x (EuclideanSpace.single j 1))) :=
        HRS.MS.UlocCut.uc_sum_le _ _ _
    _ ≤ ∑ _j : Fin d, ENNReal.ofReal (Cm * Xg) * ENNReal.ofReal (Cu * Xf) :=
        Finset.sum_le_sum fun j _ => hterm j
    _ = ENNReal.ofReal (d * (Cm * Cu) * Xf * Xg) := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, nsmul_eq_mul,
          ← ENNReal.ofReal_mul (by positivity), ← ENNReal.ofReal_natCast d,
          ← ENNReal.ofReal_mul (by positivity)]
        congr 1
        ring

/-- The conclusion of `sa4_test_h` for the constants `(C₀ᶜ, C)`. -/
def Sa4Test (d : ℕ) (s : ℝ) (_χ : Euc d → ℝ) (C₀c C : ℝ) : Prop :=
  ∀ Λ : ℝ, 1 ≤ Λ → ∀ N : ℕ, 2 ≤ N → ∀ ρ : Euc d → ℝ, HRS.Whole.IsProbDensity ρ → (∀ x, ρ x ≤ Λ) →
    Integrable (fun x => ‖x‖ ^ 2 * ρ x) → ∀ X : EucConfig d N, Function.Injective X →
    ∀ (f g : Euc d → ℝ), MemCb (mStar d) f → MemCb (mStar d) g → ∀ Xf Xg : ℝ, 0 ≤ Xf → 0 ≤ Xg →
      cbNorm (mStar d) f ≤ Xf → cbNorm (mStar d) g ≤ Xg → ∀ R : ℝ, 1 ≤ R →
      |HRS.Whole.pair (HRS.Whole.empirical X) (sa2h f g) -
          HRS.Whole.pair (HRS.Whole.withDensityReal ρ) (sa2h f g)| ≤
        C * Xf * Xg * (R ^ ((d : ℝ) / 2) * (smearScale d N Λ +
            Real.sqrt (rieszModulatedEnergy d s X (HRS.Whole.withDensityReal ρ) + oNΛ d s C₀c Λ N)) +
          (secondMomentOf (HRS.Whole.empirical X) + secondMomentOf (HRS.Whole.withDensityReal ρ)) / R ^ 2)

/-- The test inequality of `B:lem:test-cutoff` for `h_{fg}`, at the Sobolev index `mm = d/2 + 1`, from `C_b^{m_*}` bounds. -/
theorem sa4_test_h (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) (C₁ : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ C₀ : ℝ, WholeCoercivityPair d s C₀ C₁ → Sa4Test d s χ C₀ C := by
  obtain ⟨K, hK0, hK⟩ := Q09A.sobolev_plat_bound hd (m := sa4mm d) (by unfold sa4mm; omega) χ hχ.2.2.2.2
  obtain ⟨Lp, hLp0, hLp⟩ := Q09A.plat_lipschitz d
  obtain ⟨Ch, hCh0, hCh⟩ := sa4_hSob hχ
  set cpc : ℝ := |C₁| * (Lp + 1) + |C₁| * (K * Real.sqrt (((2 * d + 5 : ℕ) : ℝ) ^ d)) + 1 with hcpc
  have hcpc0 : 0 ≤ cpc := by positivity
  refine ⟨cpc * (d + 2 * d + Ch), by positivity, fun C₀ hpair Λ hΛ N hN ρ hρ hρΛ hmom X hX f g hf hg Xf Xg
    hXf hXg hcf hcg R hR => ?_⟩
  have hmm : ((d : ℝ) - s) / 2 ≤ ((sa4mm d : ℕ) : ℝ) := by
    unfold sa4mm
    have : (d : ℝ) ≤ 2 * ((d / 2 : ℕ) : ℝ) + 1 := by exact_mod_cast (by omega : d ≤ 2 * (d / 2) + 1)
    push_cast
    linarith
  have hf2 : MemCb 2 f := sa2_memCb_mono sa2_two_le_mStar hf
  have hg2 : MemCb 2 g := sa2_memCb_mono sa2_two_le_mStar hg
  have hcf2 : cbNorm 2 f ≤ Xf := (sa2_cbNorm_mono sa2_two_le_mStar f).trans hcf
  have hcg2 : cbNorm 2 g ≤ Xg := (sa2_cbNorm_mono sa2_two_le_mStar g).trans hcg
  have hsob : ∀ z : Euc d, HRS.PDE.ToolboxRd.MemSobolev ((sa4mm d : ℕ) : ℝ) (fun x => χ (x - z) * sa2h f g x) ∧
      HRS.PDE.ToolboxRd.sobolevNormSq ((sa4mm d : ℕ) : ℝ) (fun x => χ (x - z) * sa2h f g x) ≤
        (Ch * Xf * Xg) ^ 2 := fun z =>
    sa2_sobE_unpack (by positivity) (hCh f g hf hg Xf Xg hXf hXg hcf hcg z)
  have key := sa2_pathwise_core hd s hs0 hsd (sa4mm d) hmm χ K Lp hK0 hLp0 hK hLp C₁ C₀ hpair Λ hΛ N hN ρ hρ hρΛ
    hmom X hX (sa2h f g) (d * Xf * Xg) (2 * d * Xf * Xg) (Ch * Xf * Xg) (by positivity) (by positivity)
    (by positivity) (fun x => sa2h_bound hf2 hg2 hcf2 hcg2 x) (fun x y => sa2h_lip hf2 hg2 hcf2 hcg2 x y) hsob R hR
  refine key.trans (le_of_eq ?_)
  ring

/-- Existence of the test constants for all large `C₀`. -/
theorem sa4_test_exists (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d)
    {χ : Euc d → ℝ} (hχ : IsUlocCutoff χ) :
    ∃ C₀t Ct : ℝ, 0 ≤ C₀t ∧ 0 ≤ Ct ∧ ∀ C₀c : ℝ, C₀t ≤ C₀c → Sa4Test d s χ C₀c Ct := by
  obtain ⟨C₀b, C₁, hC₀b, hpair⟩ := HRS.MH.CoercTest.p_assembly d hd s hs0 hsd
  obtain ⟨Ct, hCt0, hCt⟩ := sa4_test_h hd hs0 hsd hχ C₁
  exact ⟨C₀b, Ct, hC₀b, hCt0, fun C₀c hc => hCt C₀c (hpair C₀c hc)⟩

end HRS.MS.DecStat
