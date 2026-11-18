import HRS.MS.GoTie
import HRS.MS.FcauTie

/-!
# S5.5 features, bridge: uniqueness of classical adjoint solutions from `WholeSetup` (infrastructure)

`s55f_propagatorW_eq`: for `S : WholeSetup b` (`b.Valid`) and `N` such that the `Rd` disjunct of `S.regime N` holds
(one of `R1`, `R2a`, `R2c`, `R3` of `thm:adjoint-rd`), every classical adjoint solution `f` on `[0,t]`, `t ∈ [0,T]`,
of the coefficients `S.coeff N` agrees with `propagatorW (S.coeff N) · t φ` on `[0,t]` (`propagatorW_eq`, F-CAU).

What is read off `WholeSetup` (all hypotheses of `propagatorW_eq`):
* `D = S.dyn N`: `D.s = b.s`, `D.M = b.M`, `D.V = quadV b.Q b.c`, `D.invβ = S.invβ N ∈ [0, ν_*]` (`S.hinvβ`);
* `hM : MatBound MB b.M` with `MB = ∑ |M_{ij}|`;
* `hV : VHypRd (m+3) ΛV G₀ (quadV b.Q b.c)` (all derivatives of order `≥ 3` of a quadratic vanish), `m = b.k + 3`;
* `hρ : CoeffHypRd b.s m Λ' T (S.ρ N)`: `prob` from `S.mf`; `regular` from `S.dens` (weighted bounds with exponent
  `b.L ≥ d + 3` give `MemCb`, the `⟨x⟩^{d+3}`-weighted bound and the `C_b` norm sum, through order `m + 3 = b.k + 6`)
  and, for `d - 1 ≤ b.s`, from `S.force`; `cont` (weak continuity against bounded continuous tests) from the weak
  mean-field identity `S.mf` (continuity against `C_b²` tests, `s55_weak_cont`), pointwise continuity of
  `t ↦ ρ_t(y)` (`s55_pointwise`) and dominated convergence with the decay `⟨x⟩^{-(d+1)}`;
* `hRg` is the `Rd` disjunct of `S.regime N`.

The `Lp` disjunct of `S.regime N` (`LpCase.Holds d b.s 2 b.M c`) is NOT used: uniqueness there is
`adjoint_lp` (`HRS/Whole/AppendixAAdjoint.lean`, uniqueness of `IsLpSolutionRd`, statement only) and relating
`IsClassicalAdjointW` to `IsLpSolutionRd` is a separate development.  Covered: `b.s ≤ d - 2` (R1, any `M`), and for
`d - 2 < b.s`: `Torus.symPart b.M = 0` (R2a), `b.s ≤ d - 1` with `Torus.SymNonpos b.M` (R2c), `0 < ν₀ ≤ S.invβ N` (R3).
Not covered: `d - 1 < b.s < d`, `M = -λ I + skew` with `λ > 0` and `S.invβ N` not bounded below by a positive `ν₀`.

Helper names carry the prefix `s55f_`; namespace `HRS.MS.Go`.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.Go
open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.DualityRd

variable {d : ℕ}

/-! ### The quadratic potential at every order -/

lemma s55f_vhyp_quadV {Q : Matrix (Fin d) (Fin d) ℝ} (hQ : Q.IsSymm) (c : Euc d) (n : ℕ) :
    ∃ ΛV G₀ : ℝ, VHypRd n ΛV G₀ (quadV Q c) := by
  set Qc : Euc d →L[ℝ] Euc d := (Matrix.toEuclideanLin Q).toContinuousLinearMap with hQc
  set V : Euc d → ℝ := quadV Q c with hV
  have hVs : ContDiff ℝ ∞ V := by
    have h1 : ContDiff ℝ ∞ (fun x : Euc d => (1 / 2 : ℝ) * inner ℝ x (Qc x)) :=
      contDiff_const.mul (contDiff_id.inner ℝ Qc.contDiff)
    have h2 : ContDiff ℝ ∞ (fun x : Euc d => inner ℝ c x) :=
      contDiff_const.inner ℝ contDiff_id
    exact h1.add h2
  have hgrad : ∀ x, gradient V x = Qc x + c := fun x => HRS.MS.Adj.ad_gradient_quadV hQ c x
  have hF : fderiv ℝ V = fun x => (InnerProductSpace.toDual ℝ (Euc d)) (Qc x + c) := by
    funext x
    have := hgrad x
    unfold gradient at this
    rw [← this]
    simp
  set A : Euc d →L[ℝ] (Euc d →L[ℝ] ℝ) :=
    (InnerProductSpace.toDual ℝ (Euc d)).toContinuousLinearEquiv.toContinuousLinearMap.comp Qc with hA
  have hFF : fderiv ℝ (fderiv ℝ V) = fun _ => A := by
    funext y
    rw [hF]
    have hd : HasFDerivAt (fun x => (InnerProductSpace.toDual ℝ (Euc d)) (Qc x + c)) A y :=
      ((InnerProductSpace.toDual ℝ (Euc d)).toContinuousLinearEquiv.hasFDerivAt).comp y
        (Qc.hasFDerivAt.add_const c)
    exact hd.fderiv
  refine ⟨‖A‖, ‖gradient V 0‖, hVs, fun j hj2 hj x => ?_, le_rfl⟩
  obtain ⟨i, rfl⟩ : ∃ i, j = i + 2 := ⟨j - 2, by omega⟩
  have h1 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := fderiv ℝ V) (x := x) (n := i)
  have h2 := norm_iteratedFDeriv_fderiv (𝕜 := ℝ) (f := V) (x := x) (n := i + 1)
  rw [← h2, ← h1, hFF]
  rcases Nat.eq_zero_or_pos i with rfl | hi
  · simp
  · rw [iteratedFDeriv_const_of_ne (by omega)]
    simp
    exact norm_nonneg A

/-! ### Regular slice at every order -/

lemma s55f_regular_slice {n : ℕ} (r : ℕ) (hr : r ≤ n) {L Λ : ℝ} (hL : (d : ℝ) + 3 ≤ L) {f : Euc d → ℝ}
    (hf : ContDiff ℝ n f) (hw : weightedSupE n L f ≤ ENNReal.ofReal Λ) :
    MemCb r f ∧ weightedSupE r ((d : ℝ) + 3) f < ⊤ ∧
      HRS.cbNorm r f + (weightedSupE r ((d : ℝ) + 3) f).toReal ≤
        (∑ j ∈ Finset.range (r + 1), (d : ℝ) ^ j + 1) * max Λ 0 := by
  have hL0 : 0 ≤ L := by have : (0 : ℝ) ≤ d := Nat.cast_nonneg d; linarith
  have hΛ0 : 0 ≤ max Λ 0 := le_max_right _ _
  have hp : ∀ j ≤ r, ∀ (i : Fin j → Fin d) (x : Euc d), |partialDeriv i f x| ≤ max Λ 0 := by
    intro j hj i x
    have h1 := s55_dse_bound (w := fun _ => L) hw (j := j) (by omega) i x
    have h2 : 1 ≤ jbracket x ^ L := Real.one_le_rpow (HRS.MS.Adj.ad1_one_le_jb x) hL0
    nlinarith [abs_nonneg (partialDeriv i f x)]
  have hnorm : ∀ j ≤ r, ∀ x, ‖iteratedFDeriv ℝ j f x‖ ≤ (d : ℝ) ^ j * max Λ 0 := by
    intro j hj x
    exact (HRS.MP.RdInit.mri_norm_iter_le j f x).trans
      (s55_card_sum_le j _ fun i => hp j hj i x)
  have hmem : MemCb r f :=
    ⟨hf.of_le (by exact_mod_cast hr), fun j hj => ⟨(d : ℝ) ^ j * max Λ 0, by
      rintro _ ⟨x, rfl⟩; exact hnorm j hj x⟩⟩
  have hcb : HRS.cbNorm r f ≤ ∑ j ∈ Finset.range (r + 1), (d : ℝ) ^ j * max Λ 0 := by
    unfold HRS.cbNorm
    refine Finset.sum_le_sum fun j hj => ?_
    exact ciSup_le fun x => hnorm j (by have := Finset.mem_range.1 hj; omega) x
  have hwse : weightedSupE r ((d : ℝ) + 3) f ≤ ENNReal.ofReal (max Λ 0) := by
    refine s55_dse_le fun j hj i x => ?_
    have h1 := s55_dse_bound (w := fun _ => L) hw (j := j) (by omega) i x
    have h2 : jbracket x ^ ((d : ℝ) + 3) ≤ jbracket x ^ L :=
      Real.rpow_le_rpow_of_exponent_le (HRS.MS.Adj.ad1_one_le_jb x) hL
    exact (mul_le_mul_of_nonneg_right h2 (abs_nonneg _)).trans h1
  refine ⟨hmem, lt_of_le_of_lt hwse ENNReal.ofReal_lt_top, ?_⟩
  have h3 : (weightedSupE r ((d : ℝ) + 3) f).toReal ≤ max Λ 0 := by
    have := ENNReal.toReal_mono ENNReal.ofReal_ne_top hwse
    rwa [ENNReal.toReal_ofReal hΛ0] at this
  calc HRS.cbNorm r f + (weightedSupE r ((d : ℝ) + 3) f).toReal
      ≤ ∑ j ∈ Finset.range (r + 1), (d : ℝ) ^ j * max Λ 0 + max Λ 0 := add_le_add hcb h3
    _ = (∑ j ∈ Finset.range (r + 1), (d : ℝ) ^ j + 1) * max Λ 0 := by
        rw [add_mul, one_mul, Finset.sum_mul]

/-! ### `MFData` of the setup at every `s < d` -/

theorem s55f_mfdata {s T ν Λ L : ℝ} {n : ℕ} (hn : 3 ≤ n) (hL : (d : ℝ) + 3 ≤ L)
    (hs0 : 0 ≤ s) (hsd : s < (d : ℝ)) (M Q : Matrix (Fin d) (Fin d) ℝ) (hQ : Q.IsSymm) (c : Euc d)
    (hν : 0 ≤ ν) {ρ : ℝ → Euc d → ℝ}
    (hmf : IsWholeMeanFieldSolution (⟨s, M, quadV Q c, ν⟩ : WholeDyn d) T ρ)
    (hdens : ∀ t ∈ Set.Icc (0 : ℝ) T, ContDiff ℝ n (ρ t) ∧ weightedSupE n L (ρ t) ≤ ENNReal.ofReal Λ)
    (hforce : (d : ℝ) - 1 ≤ s → ∀ t ∈ Set.Icc (0 : ℝ) T, ∀ x,
      ‖HRS.Whole.AppendixA.fracForceRd d s (ρ t) x‖ ≤ (∑ j ∈ Finset.range 4, (d : ℝ) ^ j + 1) * max Λ 0) :
    ∃ ΛV G₀ : ℝ, MFData s ((∑ j ∈ Finset.range 4, (d : ℝ) ^ j + 1) * max Λ 0) T ΛV G₀
      (⟨s, M, quadV Q c, ν⟩ : WholeDyn d) ρ := by
  obtain ⟨ΛV, G₀, hV⟩ := s55_vhyp_quadV hQ c
  refine ⟨ΛV, G₀, rfl, hs0, hsd, hν, hV, hmf, ?_, ?_⟩
  · intro t ht
    exact s55_regular_slice hn hL (hdens t ht).1 (hdens t ht).2
  · exact hforce

/-! ### Weak continuity against bounded continuous tests -/

theorem s55f_weak_cont_bdd (hd : 1 ≤ d) {T : ℝ} {ρ : ℝ → Euc d → ℝ} (Λ : ℝ)
    (hreg : ∀ t ∈ Set.Icc (0 : ℝ) T, MemCb 3 (ρ t) ∧ weightedSupE 3 ((d : ℝ) + 3) (ρ t) < ⊤ ∧
      HRS.cbNorm 3 (ρ t) + (weightedSupE 3 ((d : ℝ) + 3) (ρ t)).toReal ≤ Λ)
    (hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Icc (0 : ℝ) T)) :
    ∀ ψ : Euc d → ℝ, Continuous ψ → (∃ B, ∀ x, |ψ x| ≤ B) →
      ContinuousOn (fun r => ∫ x, ψ x * ρ r x) (Set.Icc (0 : ℝ) T) := by
  intro ψ hψ ⟨B, hB⟩
  set A : ℝ := (d : ℝ) ^ 3 * max Λ 0 * 2 ^ ((d : ℝ) + 3) with hAdef
  have hA : 0 ≤ A := by positivity
  have hdec : ∀ r ∈ Set.Icc (0 : ℝ) T, HRS.MP.RdGen.RgDecay 3 (fun _ => A) (ρ r) := by
    intro r hr
    have hcb := hreg r hr
    have hcb0 : 0 ≤ HRS.cbNorm 3 (ρ r) :=
      Finset.sum_nonneg fun _ _ => Real.iSup_nonneg fun _ => norm_nonneg _
    exact HRS.MP.RdGen.rg_rho_decay hd (r := 3) (Λ := max Λ 0) hcb.1 hcb.2.1
      (by linarith [hcb.2.2, le_max_left Λ 0])
  have hparts := fun r hr => HRS.MP.RdGen.rg_decay_parts (n := 3) (by omega) (a := fun _ => A)
    (fun _ => hA) (hdec r hr)
  have hw : ∀ y : Euc d, (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ 1 := by
    intro y
    apply Real.rpow_le_one_of_one_le_of_nonpos (by linarith [norm_nonneg y])
    have : (0 : ℝ) ≤ d := Nat.cast_nonneg d
    linarith
  have hdiff : ∀ r ∈ Set.Icc (0 : ℝ) T, Differentiable ℝ (ρ r) := fun r hr =>
    ((hparts r hr).1).differentiable (by norm_num)
  have h0 : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ y, ‖ρ r y‖ ≤ A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) :=
    fun r hr => (hparts r hr).2.1
  have h1' : ∀ r ∈ Set.Icc (0 : ℝ) T, ∀ y, ‖fderiv ℝ (ρ r) y‖ ≤ A := fun r hr y =>
    ((hparts r hr).2.2.1 y).trans (by
      calc A * (1 + ‖y‖) ^ (-((d : ℝ) + 1)) ≤ A * 1 := mul_le_mul_of_nonneg_left (hw y) hA
        _ = A := mul_one _)
  have hpt : ∀ y, ContinuousOn (fun r => ρ r y) (Set.Icc (0 : ℝ) T) := fun y =>
    s55_pointwise hA hweak hdiff h1' y
  refine continuousOn_of_dominated (bound := fun x => |B| * (A * (1 + ‖x‖) ^ (-((d : ℝ) + 1))))
    (fun r hr => ?_) (fun r hr => Eventually.of_forall fun x => ?_) ?_
    (Eventually.of_forall fun x => ?_)
  · exact (hψ.mul (hdiff r hr).continuous).aestronglyMeasurable
  · rw [norm_mul]
    exact mul_le_mul ((hB x).trans (le_abs_self B)) (h0 r hr x) (norm_nonneg _) (abs_nonneg _)
  · exact ((HRS.MP.RdGen.rg_W_integrable hd).const_mul A).const_mul |B|
  · exact continuousOn_const.mul (hpt x)

/-! ### `CoeffHypRd` and `VHypRd`, `MatBound` of the setup -/

theorem s55f_matBound (M : Matrix (Fin d) (Fin d) ℝ) : PDE.MatBound (∑ i, ∑ j, |M i j|) M := by
  intro i j
  calc |M i j| ≤ ∑ j', |M i j'| :=
        Finset.single_le_sum (f := fun j' => |M i j'|) (fun _ _ => abs_nonneg _) (Finset.mem_univ j)
    _ ≤ ∑ i', ∑ j', |M i' j'| :=
        Finset.single_le_sum (f := fun i' => ∑ j', |M i' j'|)
          (fun _ _ => Finset.sum_nonneg fun _ _ => abs_nonneg _) (Finset.mem_univ i)

theorem s55f_coeffHyp (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ) :
    ∃ Λ' : ℝ, CoeffHypRd b.s (b.k + 3) Λ' b.T (S.ρ N) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have hk0 : (0 : ℝ) ≤ b.k := Nat.cast_nonneg b.k
  have hL := hb.hL
  have hs0 := hb.hs0
  have hdL : (d : ℝ) + 3 ≤ b.L := by linarith
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  have hn : 3 ≤ b.k + 6 + ⌈(d : ℝ) / 2⌉₊ := by omega
  set Λ3 : ℝ := (∑ j ∈ Finset.range 4, (d : ℝ) ^ j + 1) * max b.Λ 0 with hΛ3
  set Λr : ℝ := (∑ j ∈ Finset.range (b.k + 6 + 1), (d : ℝ) ^ j + 1) * max b.Λ 0 with hΛr
  have hΛ3le : b.Λ ≤ Λ3 := by
    have h1 : 1 ≤ ∑ j ∈ Finset.range 4, (d : ℝ) ^ j + 1 := by
      have : (0 : ℝ) ≤ ∑ j ∈ Finset.range 4, (d : ℝ) ^ j :=
        Finset.sum_nonneg fun _ _ => by positivity
      linarith
    calc b.Λ ≤ max b.Λ 0 := le_max_left _ _
      _ = 1 * max b.Λ 0 := (one_mul _).symm
      _ ≤ Λ3 := mul_le_mul_of_nonneg_right h1 (le_max_right _ _)
  have hΛrle : Λ3 ≤ max Λ3 Λr := le_max_left _ _
  obtain ⟨ΛV, G₀, hMF⟩ := s55f_mfdata hn hdL hb.hs0 hb.hsd b.M b.Q hb.hQ b.c (S.hinvβ N).1
    (S.mf N) (S.dens N) (fun h t ht x => (S.force h N t ht x).trans hΛ3le)
  have hreg3 : ∀ t ∈ Set.Icc (0 : ℝ) b.T, MemCb 3 (S.ρ N t) ∧
      weightedSupE 3 ((d : ℝ) + 3) (S.ρ N t) < ⊤ ∧
      HRS.cbNorm 3 (S.ρ N t) + (weightedSupE 3 ((d : ℝ) + 3) (S.ρ N t)).toReal ≤ Λ3 := fun t ht =>
    s55_regular_slice hn hdL (S.dens N t ht).1 (S.dens N t ht).2
  have hweak : ∀ ψ : Euc d → ℝ, ContDiff ℝ ∞ ψ → HasCompactSupport ψ →
      ContinuousOn (fun r => ∫ x, ψ x * S.ρ N r x) (Set.Icc (0 : ℝ) b.T) := fun ψ hψ hcs =>
    s55_weak_cont hMF (HRS.Whole.u4_memCb 2 ⟨hψ, hcs⟩)
  refine ⟨max Λ3 Λr, (S.mf N).density, ⟨?_, ?_⟩, ?_⟩
  · intro t ht
    obtain ⟨h1, h2, h3⟩ := s55f_regular_slice (n := b.k + 6 + ⌈(d : ℝ) / 2⌉₊) (b.k + 3 + 3)
      (by omega) hdL (S.dens N t ht).1 (S.dens N t ht).2
    refine ⟨h1, h2, h3.trans ?_⟩
    have : (∑ j ∈ Finset.range (b.k + 3 + 3 + 1), (d : ℝ) ^ j + 1) * max b.Λ 0 = Λr := by
      rw [hΛr]
    rw [this]
    exact le_max_right _ _
  · intro hs t ht x
    exact (S.force hs N t ht x).trans (hΛ3le.trans hΛrle)
  · exact s55f_weak_cont_bdd hd1 Λ3 hreg3 hweak

/-- **Uniqueness of classical adjoint solutions for the coefficients of a `WholeSetup`** (`Rd` regime disjunct).
If `f` is a classical adjoint solution on `[0,t]`, `t ∈ [0,T]`, with terminal datum `φ`, then
`propagatorW (S.coeff N) r t φ = f r` on `[0,t]`. -/
theorem s55f_propagatorW_eq (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hRd : ∃ (Rg : PDE.Regime) (ν₀ : ℝ), RdRegimeHolds Rg d b.s b.M (S.invβ N) ν₀)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW (S.coeff N) t φ f) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, propagatorW (S.coeff N) r t φ = f r := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  obtain ⟨Λ', hρ⟩ := s55f_coeffHyp b hb S N
  obtain ⟨ΛV, G₀, hV⟩ := s55f_vhyp_quadV hb.hQ b.c (b.k + 3 + 3)
  obtain ⟨Rg, ν₀, hRg⟩ := hRd
  exact HRS.MS.Fcau.propagatorW_eq hd1 hb.hs0 hb.hsd (b.k + 3) (by omega) Rg b.T Λ' ΛV G₀
    (∑ i, ∑ j, |b.M i j|) b.νstar ν₀ (S.dyn N) (S.ρ N) rfl (s55f_matBound _) hV (S.hinvβ N) hρ
    hRg ht hf

/-- Under the `Rd` regime disjunct, if a classical adjoint solution with datum `φ` exists, then
`r ↦ propagatorW (S.coeff N) r t φ` is the (unique) one, and it is determined by `φ` and `t` alone. -/
theorem s55f_propagatorW_classical (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ)
    {t : ℝ} {φ : Euc d → ℝ} (h : ∃ f, IsClassicalAdjointW (S.coeff N) t φ f) :
    IsClassicalAdjointW (S.coeff N) t φ (fun r => propagatorW (S.coeff N) r t φ) :=
  HRS.MS.Fcau.propagatorW_isClassical h

end HRS.MS.Go
