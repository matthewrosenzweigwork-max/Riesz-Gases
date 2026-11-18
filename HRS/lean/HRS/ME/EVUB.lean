import HRS.PDE.MeanFieldAprioriSobolev
import HRS.PDE.ClassicalPart
import HRS.PDE.EnergyTorus

/-!
# Chunk E, packet EVB: V-uniform nonlinear loss bounds (`_unifV`)

Copies in namespace `HRS.ME.EVU` of the following originals, with the constant chosen before the potential `V`:
* `exists_nonlinear_loss_bound_unifV` of `HRS.PDE.MFApriori.exists_nonlinear_loss_bound`
  (`HRS/PDE/MeanFieldAprioriParaproduct.lean:805`); `V` is now `Torus.IsCk (K+2) V` with `cbNorm (K+2) V ≤ Bv`, `j ≤ K`.
* `exists_nl_loss_unifV` of `HRS.PDE.MFApriori.exists_nl_loss` (`HRS/PDE/MeanFieldAprioriSobolev.lean:72`).

The only quantity of `V` in the original constant is `cb i = cbNorm ⌈σ'⌉₊ (∂_i V)` (`σ' = j - b`), entering the constant
`√(2 d (∑ Qg + ∑ C0 · cb_i²))`; `Qg` (from `paraproduct_sq_bound`) and `C0` (from `ProdAux.prodBound_all`) are `V`-free.
Here `cb i ≤ cbNorm (⌈σ'⌉₊+1) V ≤ cbNorm (K+2) V ≤ Bv` (`cbNorm_partialDeriv_le`, `cbNorm_mono'`), and the constant is
`√(2 d (∑ Qg + ∑ C0 · Bv²))`.  No other `V`-dependent constant occurs in the original.
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ComplexConjugate
open HRS.PDE HRS.PDE.MFApriori

namespace HRS.ME.EVU

-- `hsNorm` / `hsNormSq` of `HRS.PDE` (the root `HRS.hsNorm` would otherwise shadow them here)
export HRS.PDE (hsNorm hsNormSq)

variable {d : ℕ}

/-- `V`-uniform version of `HRS.PDE.MFApriori.exists_nonlinear_loss_bound`: the constant is chosen before `V`
(`Bv` fixed first); the hypothesis `IsCk (⌈j⌉₊+1) V` is replaced by `IsCk (K+2) V`, `cbNorm (K+2) V ≤ Bv`. -/
theorem exists_nonlinear_loss_bound_unifV (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (b : ℝ)
    (hb : max (s - d + 1) 0 < b) (hb1 : b ≤ 1) (j : ℝ) (hj : 1 ≤ j) (K : ℕ) (hjK : j ≤ K)
    (Bv : ℝ) (ν : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : Torus d → ℝ, Torus.IsCk (K + 2) V → Torus.cbNorm (K + 2) V ≤ Bv →
      ∀ f : Torus d → ℝ, Continuous f → MemHs j (coeffOf f) →
      MemHs (j - (1 + b)) (mfRhsCoeff d s V ν (coeffOf f) - (ν : ℂ) • laplaceCoeff (coeffOf f)) ∧
      hsNorm (j - (1 + b)) (mfRhsCoeff d s V ν (coeffOf f) - (ν : ℂ) • laplaceCoeff (coeffOf f)) ≤
        C * (Torus.supNorm f + 1) * hsNorm j (coeffOf f) := by
  have hb0 : 0 < b := lt_of_le_of_lt (le_max_right _ _) hb
  have hθb : s - d + 1 < b := lt_of_le_of_lt (le_max_left _ _) hb
  set σ' := j - b with hσ'
  have hσ'0 : 0 ≤ σ' := by linarith
  have hσ'j : σ' + b = j := by rw [hσ']; ring
  choose Qg hQg0 hQg using fun i : Fin d => paraproduct_sq_bound hd s hs0 hsd σ' b hσ'0 hb i
  obtain ⟨C0, hC00, hC0⟩ := ProdAux.prodBound_all hd ⌈σ'⌉₊ σ' hσ'0
    (by have := Nat.le_ceil σ'; linarith)
  have hσK : σ' ≤ K := by linarith
  have hceilK : ⌈σ'⌉₊ ≤ K := Nat.ceil_le.mpr hσK
  have hQsum : 0 ≤ ∑ i, Qg i := Finset.sum_nonneg fun i _ => hQg0 i
  have hCB0 : 0 ≤ ∑ _i : Fin d, C0 * Bv ^ 2 := Finset.sum_nonneg fun i _ => mul_nonneg hC00 (sq_nonneg _)
  have hQbv0 : 0 ≤ 2 * (d : ℝ) * (∑ i, Qg i + ∑ _i : Fin d, C0 * Bv ^ 2) :=
    mul_nonneg (by positivity) (add_nonneg hQsum hCB0)
  refine ⟨Real.sqrt (2 * (d : ℝ) * (∑ i, Qg i + ∑ _i : Fin d, C0 * Bv ^ 2)), Real.sqrt_nonneg _,
    fun V hVK hVB f hf hF => ?_⟩
  have hV : Torus.IsCk (⌈j⌉₊ + 1 : ℕ) V := isCk_of_le_nat K j hjK V hVK
  -- the smooth multipliers `∂_i V`
  set dV : Fin d → Torus d → ℝ := fun i => Torus.partialDeriv i V with hdV
  have hdVj : ∀ i, Torus.IsCk (⌈j⌉₊ : ℕ) (dV i) := fun i => ProdAux.isCk_partialDeriv hV i
  have hceil : ⌈σ'⌉₊ ≤ ⌈j⌉₊ := Nat.ceil_mono (by linarith)
  have hdVσ : ∀ i, Torus.IsCk (⌈σ'⌉₊ : ℕ) (dV i) := fun i =>
    (hdVj i).of_le (by exact_mod_cast hceil)
  have hj1 : 1 ≤ ⌈j⌉₊ := by
    have := Nat.le_ceil j
    exact_mod_cast (by linarith : (1 : ℝ) ≤ ⌈j⌉₊)
  have hdV1 : ∀ i, Torus.IsCk 1 (dV i) := fun i => (hdVj i).of_le (by exact_mod_cast hj1)
  have hV1 : Torus.IsCk 1 V := hV.of_le (by exact_mod_cast Nat.le_add_left 1 _)
  have hdVc : ∀ i, derivCoeff i (coeffOf V) = coeffOf (dV i) := fun i =>
    (coeffOf_partialDeriv_eq i V hV1).symm
  have hV0 : ∀ i, MemHs 0 (derivCoeff i (coeffOf V)) := fun i => by
    rw [hdVc]; exact (coeffOf_memHs_zero (continuous_of_isCk (hdV1 i))).1
  set cb : Fin d → ℝ := fun i => Torus.cbNorm ⌈σ'⌉₊ (dV i) with hcb
  -- the only `V`-dependent quantity: `cb i ≤ Bv`, uniformly
  have hcbB : ∀ i, cb i ≤ Bv := fun i => by
    have hσV : Torus.IsCk ((⌈σ'⌉₊ + 1 : ℕ) : WithTop ℕ∞) V := isCk_of_le_nat K σ' hσK V hVK
    have h1 := (HRS.PDE.ClassicalPart.cbNorm_partialDeriv_le ⌈σ'⌉₊ V hσV i).2
    exact h1.trans ((HRS.PDE.ET.cbNorm_mono' (a := ⌈σ'⌉₊ + 1) (b := K + 2) (by omega) V).trans hVB)
  have hcb0 : ∀ i, 0 ≤ cb i := fun i => HRS.PDE.ClassicalPart.cbNorm_nonneg'' _ _
  have hCsum : ∑ i, C0 * cb i ^ 2 ≤ ∑ _i : Fin d, C0 * Bv ^ 2 :=
    Finset.sum_le_sum fun i _ => mul_le_mul_of_nonneg_left (pow_le_pow_left₀ (hcb0 i) (hcbB i) 2) hC00
  set F := coeffOf f with hFdef
  have hFσ' : MemHs σ' F := memHs_mono' (by linarith) hF
  have hF0 : MemHs 0 F := memHs_mono' (by linarith) hF
  have hFσb : MemHs (σ' + b) F := by rw [hσ'j]; exact hF
  have hg0 : ∀ i, MemHs 0 (gradRieszCoeff d s i F) := fun i => by
    obtain ⟨Cs, -, hCs⟩ := grad_l2_bound (d := d) s i
    exact (hCs j (by linarith) F hF).1
  set Vt : Fin d → Coeff d := fun i => mulCoeff (coeffOf (dV i)) F with hVt
  set Gt : Fin d → Coeff d := fun i => mulCoeff F (gradRieszCoeff d s i F) with hGt
  have hGtb : ∀ i, MemHs σ' (Gt i) ∧ hsNormSq σ' (Gt i) ≤
      Qg i * Torus.supNorm f ^ 2 * hsNormSq (σ' + b) F := fun i => hQg i f hf hFσb
  have hVtb : ∀ i, MemHs σ' (Vt i) ∧ hsNormSq σ' (Vt i) ≤ C0 * cb i ^ 2 * hsNormSq σ' F :=
    fun i => hC0 (dV i) (hdVσ i) F hFσ'
  have hR : mfRhsCoeff d s V ν F - (ν : ℂ) • laplaceCoeff F =
      fun k => ∑ i, (derivCoeff i (Vt i) k + derivCoeff i (Gt i) k) := by
    funext k
    simp only [Pi.sub_apply, Pi.smul_apply, smul_eq_mul, mfRhsCoeff]
    rw [add_sub_cancel_left]
    refine Finset.sum_congr rfl fun i _ => ?_
    have h1 : mulCoeff F (fun k' => derivCoeff i (coeffOf V) k' + gradRieszCoeff d s i F k') =
        fun k' => Vt i k' + Gt i k' := by
      funext k'
      rw [mulCoeff_add_right hF0 (hV0 i) (hg0 i) k', hdVc, hVt, hGt]
      simp only [HRS.PDE.MFApriori.mulCoeff_comm F (coeffOf (dV i)) k']
    rw [h1]
    simp only [derivCoeff]
    ring
  have hRidx : j - (1 + b) = σ' - 1 := by rw [hσ']; ring
  rw [hR, hRidx]
  -- the two sums
  have hDV : ∀ i, MemHs (σ' - 1) (derivCoeff i (Vt i)) ∧
      hsNormSq (σ' - 1) (derivCoeff i (Vt i)) ≤ hsNormSq σ' (Vt i) :=
    fun i => hsNormSq_derivCoeff_le σ' i (hVtb i).1
  have hDG : ∀ i, MemHs (σ' - 1) (derivCoeff i (Gt i)) ∧
      hsNormSq (σ' - 1) (derivCoeff i (Gt i)) ≤ hsNormSq σ' (Gt i) :=
    fun i => hsNormSq_derivCoeff_le σ' i (hGtb i).1
  obtain ⟨hSV, hSVn⟩ := hsNormSq_sum_le (m := σ' - 1) (fun i => derivCoeff i (Vt i))
    (fun i => (hDV i).1)
  obtain ⟨hSG, hSGn⟩ := hsNormSq_sum_le (m := σ' - 1) (fun i => derivCoeff i (Gt i))
    (fun i => (hDG i).1)
  have hsplit : (fun k => ∑ i, (derivCoeff i (Vt i) k + derivCoeff i (Gt i) k)) =
      fun k => (∑ i, derivCoeff i (Vt i) k) + ∑ i, derivCoeff i (Gt i) k := by
    funext k; rw [Finset.sum_add_distrib]
  rw [hsplit]
  obtain ⟨hT, hTn⟩ := hsNormSq_add_le hSV hSG
  refine ⟨hT, ?_⟩
  set X := hsNormSq j F with hX
  have hX0 : 0 ≤ X := hsNormSq_nonneg _ _
  have hXσ : hsNormSq σ' F ≤ X := hsNormSq_mono' (by linarith) hF
  have hsup0 := supNorm_nonneg f
  have hVsum : ∑ i, hsNormSq (σ' - 1) (derivCoeff i (Vt i)) ≤ (∑ i, C0 * cb i ^ 2) * X := by
    rw [Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (hDV i).2.trans ((hVtb i).2.trans ?_)
    exact mul_le_mul_of_nonneg_left hXσ (by positivity)
  have hGsum : ∑ i, hsNormSq (σ' - 1) (derivCoeff i (Gt i)) ≤
      (∑ i, Qg i) * Torus.supNorm f ^ 2 * X := by
    rw [Finset.sum_mul, Finset.sum_mul]
    refine Finset.sum_le_sum fun i _ => ?_
    refine (hDG i).2.trans ((hGtb i).2.trans ?_)
    rw [hσ'j]
  have hCsum' : 0 ≤ ∑ i, C0 * cb i ^ 2 := Finset.sum_nonneg fun i _ => by positivity
  set Q := 2 * (d : ℝ) * (∑ i, Qg i + ∑ i, C0 * cb i ^ 2) with hQ
  have hQ0 : 0 ≤ Q := by rw [hQ]; exact mul_nonneg (by positivity) (add_nonneg hQsum hCsum')
  have hQle : Q ≤ 2 * (d : ℝ) * (∑ i, Qg i + ∑ _i : Fin d, C0 * Bv ^ 2) :=
    by rw [hQ]; exact mul_le_mul_of_nonneg_left (by linarith [hCsum]) (by positivity)
  have hfin : hsNormSq (σ' - 1) (fun k => (∑ i, derivCoeff i (Vt i) k) + ∑ i, derivCoeff i (Gt i) k) ≤
      Q * (Torus.supNorm f + 1) ^ 2 * X := by
    refine hTn.trans ?_
    have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    have h1 : hsNormSq (σ' - 1) (fun k => ∑ i, derivCoeff i (Vt i) k) ≤
        d * ((∑ i, C0 * cb i ^ 2) * X) :=
      hSVn.trans (mul_le_mul_of_nonneg_left hVsum hd0)
    have h2 : hsNormSq (σ' - 1) (fun k => ∑ i, derivCoeff i (Gt i) k) ≤
        d * ((∑ i, Qg i) * Torus.supNorm f ^ 2 * X) :=
      hSGn.trans (mul_le_mul_of_nonneg_left hGsum hd0)
    have h3 : (∑ i, C0 * cb i ^ 2) * X ≤ (∑ i, C0 * cb i ^ 2) * (Torus.supNorm f + 1) ^ 2 * X := by
      have : (1 : ℝ) ≤ (Torus.supNorm f + 1) ^ 2 := by nlinarith
      calc (∑ i, C0 * cb i ^ 2) * X = (∑ i, C0 * cb i ^ 2) * 1 * X := by ring
        _ ≤ _ := by gcongr
    have h4 : (∑ i, Qg i) * Torus.supNorm f ^ 2 * X ≤ (∑ i, Qg i) * (Torus.supNorm f + 1) ^ 2 * X := by
      have : Torus.supNorm f ^ 2 ≤ (Torus.supNorm f + 1) ^ 2 := by nlinarith
      gcongr
    calc 2 * (hsNormSq (σ' - 1) (fun k => ∑ i, derivCoeff i (Vt i) k) +
          hsNormSq (σ' - 1) (fun k => ∑ i, derivCoeff i (Gt i) k))
        ≤ 2 * (d * ((∑ i, C0 * cb i ^ 2) * (Torus.supNorm f + 1) ^ 2 * X) +
            d * ((∑ i, Qg i) * (Torus.supNorm f + 1) ^ 2 * X)) := by
          gcongr
          · exact h1.trans (mul_le_mul_of_nonneg_left h3 hd0)
          · exact h2.trans (mul_le_mul_of_nonneg_left h4 hd0)
      _ = _ := by rw [hQ]; ring
  unfold hsNorm
  have hQbX : Q * (Torus.supNorm f + 1) ^ 2 * X ≤
      2 * (d : ℝ) * (∑ i, Qg i + ∑ _i : Fin d, C0 * Bv ^ 2) * (Torus.supNorm f + 1) ^ 2 * X := by
    have hs2 : 0 ≤ (Torus.supNorm f + 1) ^ 2 * X := mul_nonneg (sq_nonneg _) hX0
    nlinarith [mul_le_mul_of_nonneg_right hQle hs2]
  calc Real.sqrt (hsNormSq (σ' - 1) (fun k => (∑ i, derivCoeff i (Vt i) k) + ∑ i, derivCoeff i (Gt i) k))
      ≤ Real.sqrt (2 * (d : ℝ) * (∑ i, Qg i + ∑ _i : Fin d, C0 * Bv ^ 2) * (Torus.supNorm f + 1) ^ 2 * X) :=
        Real.sqrt_le_sqrt (hfin.trans hQbX)
    _ = Real.sqrt (2 * (d : ℝ) * (∑ i, Qg i + ∑ _i : Fin d, C0 * Bv ^ 2)) * (Torus.supNorm f + 1) * Real.sqrt X := by
        rw [Real.sqrt_mul (mul_nonneg hQbv0 (sq_nonneg _)), Real.sqrt_mul hQbv0,
          Real.sqrt_sq (by linarith)]

/-- `V`-uniform version of `HRS.PDE.MFApriori.exists_nl_loss`: the constant is chosen before `V`
(`Bv` fixed last among the data); the hypothesis `IsCk (K+2) V` is kept and `cbNorm (K+2) V ≤ Bv` is added. -/
theorem exists_nl_loss_unifV (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (b : ℝ)
    (hb : max (s - d + 1) 0 < b) (hb1 : b ≤ 1) (K : ℕ) (j : ℝ) (hj1 : 1 ≤ j) (hjK : j ≤ K)
    (Bv : ℝ) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ V : Torus d → ℝ, Torus.IsCk (K + 2) V → Torus.cbNorm (K + 2) V ≤ Bv →
      ∀ f : Torus d → ℝ, Continuous f → MemHs j (coeffOf f) →
      MemHs (j - (1 + b)) (Aux.nlCoeff d s V (coeffOf f)) ∧
      hsNorm (j - (1 + b)) (Aux.nlCoeff d s V (coeffOf f)) ≤
        C * (Torus.supNorm f + 1) * hsNorm j (coeffOf f) := by
  obtain ⟨C, hC0, hC⟩ := exists_nonlinear_loss_bound_unifV hd s hs0 hsd b hb hb1 j hj1 K hjK Bv 0
  refine ⟨C, hC0, fun V hV hVB f hf hfj => ?_⟩
  have h := hC V hV hVB f hf hfj
  rwa [rhs_sub_laplace_eq] at h

end HRS.ME.EVU
