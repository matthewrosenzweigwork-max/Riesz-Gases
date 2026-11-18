import HRS.MS.StarAux4
import HRS.MS.FcauTie
import HRS.MS.GoFeatAux3
import HRS.MS.GoMeasAux3

/-!
# STAR-4: uniqueness of classical adjoint solutions in the corner, and S5.5 for every `WholeSetup`

* `lpcase_two_cover`: `LpCase.Holds d s 2 M c` gives `Rd` (R1) or `UlocStarRegime`.
* `propagatorW_unique_star`, `propagatorW_eq_star`: copies of `propagatorW_unique`/`propagatorW_eq` (`FcauTie.lean`) with
  `hRg : RdRegimeHolds ... ∨ UlocStarRegime ...` (via `uloc_uniqueness_star`).
* `s55f_propagatorW_eq_star`, `s55m_seq_star`, `s55m_continuousOn_star`: copies of `s55f_propagatorW_eq`
  (`GoFeatAux3.lean`) and of `s55m_seq`, `s55m_continuousOn` (`GoMeasAux3.lean`) with the hypothesis
  `hReg : (∃ Rg ν₀, RdRegimeHolds ...) ∨ UlocStarRegime ...`.
* `s55fMeas_holds`: `S55fMeas b S` for EVERY `S : WholeSetup b` with `b.Valid` (regime from `S.regime N` and
  `lpcase_two_cover`; no `Rd`-at-every-`N` hypothesis).
* `general_orbits_features_proof`, `general_orbits_maximal_proof`: the frozen rows of `HRS/Whole/Orbits.lean`
  (`s55f_features_of_meas`, `s55f_maximal_of_meas` plus `s55fMeas_holds`), with `type_of%` ties.

Note: `UlAdjointInput` (existence and `C_b` bounds of classical adjoint solutions) stays a hypothesis of `WholeSetup`;
only the uniqueness input is supplied here.
-/

noncomputable section

open MeasureTheory Filter Topology Metric
open scoped ENNReal NNReal BigOperators ContDiff

set_option synthInstance.maxHeartbeats 400000
set_option maxRecDepth 4000

namespace HRS.MS.Star

open HRS HRS.Whole HRS.Whole.AppendixA

variable {d : ℕ}

theorem star_matrix_symNonpos_of_lam {M : Matrix (Fin d) (Fin d) ℝ} {lam : ℝ} (hlam : 0 ≤ lam)
    {A : Matrix (Fin d) (Fin d) ℝ} (hA : A.transpose = -A) (hM : M = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + A) :
    Torus.SymNonpos M := by
  unfold Torus.SymNonpos Torus.symPart
  have h1 : M.transpose = -(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + -A := by
    rw [hM, Matrix.transpose_add, Matrix.transpose_neg, Matrix.transpose_smul, Matrix.transpose_one, hA]
  have h2 : -((1 / 2 : ℝ) • (M + M.transpose)) = lam • (1 : Matrix (Fin d) (Fin d) ℝ) := by
    rw [h1, hM]
    have : (-(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + A + (-(lam • (1 : Matrix (Fin d) (Fin d) ℝ)) + -A)) =
        (2 : ℝ) • (-(lam • (1 : Matrix (Fin d) (Fin d) ℝ))) := by
      rw [two_smul]; abel
    rw [this, smul_smul, smul_neg, neg_neg]
    norm_num
  rw [h2]
  exact Matrix.PosSemidef.one.smul hlam

/-- `LpCase.Holds` at `p = 2` is covered by `R1` or the corner regime. -/
theorem lpcase_two_cover {d : ℕ} {s : ℝ} {M : Matrix (Fin d) (Fin d) ℝ} {c : LpCase} (invβ : ℝ)
    (hκ : LpCase.Holds d s 2 M c) :
    (∃ (Rg : PDE.Regime) (ν₀ : ℝ), RdRegimeHolds Rg d s M invβ ν₀) ∨ UlocStarRegime d s M := by
  cases c with
  | sub => exact Or.inl ⟨PDE.Regime.R1, 0, hκ.1⟩
  | iso =>
    obtain ⟨hs, lam, hlam, hM⟩ := hκ
    refine Or.inr ⟨hs, star_matrix_symNonpos_of_lam hlam.le (A := 0) (by simp) (by simpa using hM)⟩
  | hilbert =>
    obtain ⟨hs, -, lam, hlam, A, hA, hM⟩ := hκ
    exact Or.inr ⟨hs, star_matrix_symNonpos_of_lam hlam hA hM⟩

end HRS.MS.Star

namespace HRS.MS.Fcau

open HRS HRS.Whole HRS.Whole.AppendixA HRS.Whole.AppendixALemmas HRS.MH.DualityRd HRS.MP.RdGen HRS.MS.Star

variable {d : ℕ}

/-- **Uniqueness of classical adjoint solutions (F-CAU), regime `Rd` or the corner `UlocStarRegime`.**  Under the coefficient hypotheses of
S.A.33 `uloc_uniqueness` (`D.s = s`, `0 ≤ s < d`, `m ≥ 1`, `MatBound`, `VHypRd (m+3)`, `0 ≤ ν ≤ ν̄`,
`CoeffHypRd s m Λ T ρ`) and one of its regimes (`RdRegimeHolds`), two classical adjoint solutions
(`IsClassicalAdjointW`, class `C_b²`) of `D.coeff ρ` on `[0,t]`, `t ≤ T`, with the same terminal
datum agree on `[0,t]`. -/
theorem propagatorW_unique_star (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (T Λ ΛV G₀ MB νbar ν₀ : ℝ) (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ)
    (hDs : D.s = s) (hM : PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hν : 0 ≤ D.invβ ∧ D.invβ ≤ νbar) (hρ : CoeffHypRd s m Λ T ρ)
    (hRg : RdRegimeHolds Rg d s D.M D.invβ ν₀ ∨ UlocStarRegime d s D.M) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {φ : Euc d → ℝ} {f₁ f₂ : ℝ → Euc d → ℝ} (h₁ : IsClassicalAdjointW (D.coeff ρ) t φ f₁)
    (h₂ : IsClassicalAdjointW (D.coeff ρ) t φ f₂) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, f₁ r = f₂ r := by
  subst hDs
  obtain ⟨χ, hχ⟩ := fcau_exists_cutoff (d := d)
  have hS := fcau_slices_of_hyp hd hs0 hsd m hm MB Λ ΛV G₀ rfl hM hV hρ ht
  have hw := fcau_sub hd D hs0 hsd ρ t hS h₁ h₂
  have hz := fcau_forward hd D hs0 hsd ρ t hS hw
  have hzb := fcau_ulBounded hχ hw
  have key := HRS.MS.Star.uloc_uniqueness_star hd D.s hs0 hsd m hm Rg T Λ ΛV G₀ MB νbar ν₀ χ hχ
    D.M D.V D.invβ ρ hM hV hν hρ hRg t ht (fun σ => (fun r x => f₁ r x - f₂ r x) (t - σ)) hzb hz
  intro r hr
  have hae := key (t - r) ⟨by linarith [hr.2], by linarith [hr.1]⟩
  simp only [sub_sub_cancel] at hae
  have hc : Continuous (fun x => f₁ r x - f₂ r x) :=
    (h₁.c2 r hr).continuous.sub (h₂.c2 r hr).continuous
  have h0 : (fun x => f₁ r x - f₂ r x) = 0 :=
    (Continuous.ae_eq_iff_eq volume hc continuous_const).1 hae
  funext x
  have := congrFun h0 x
  simp only [Pi.zero_apply] at this
  linarith

/-- (Star version.) If a classical adjoint solution `f` exists, `propagatorW` is `f` on `[0,t]`. -/
theorem propagatorW_eq_star (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (m : ℕ) (hm : 1 ≤ m)
    (Rg : PDE.Regime) (T Λ ΛV G₀ MB νbar ν₀ : ℝ) (D : WholeDyn d) (ρ : ℝ → Euc d → ℝ)
    (hDs : D.s = s) (hM : PDE.MatBound MB D.M) (hV : VHypRd (m + 3) ΛV G₀ D.V)
    (hν : 0 ≤ D.invβ ∧ D.invβ ≤ νbar) (hρ : CoeffHypRd s m Λ T ρ)
    (hRg : RdRegimeHolds Rg d s D.M D.invβ ν₀ ∨ UlocStarRegime d s D.M) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ} (hf : IsClassicalAdjointW (D.coeff ρ) t φ f) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, propagatorW (D.coeff ρ) r t φ = f r :=
  propagatorW_unique_star hd hs0 hsd m hm Rg T Λ ΛV G₀ MB νbar ν₀ D ρ hDs hM hV hν hρ hRg ht
    (propagatorW_isClassical ⟨f, hf⟩) hf

end HRS.MS.Fcau

namespace HRS.MS.Go

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MH.DualityRd HRS.MP.RdGen HRS.MS.Star

variable {d : ℕ}

/-- **Uniqueness of classical adjoint solutions for the coefficients of a `WholeSetup`** (`Rd` regime disjunct or the corner `UlocStarRegime`).
If `f` is a classical adjoint solution on `[0,t]`, `t ∈ [0,T]`, with terminal datum `φ`, then
`propagatorW (S.coeff N) r t φ = f r` on `[0,t]`. -/
theorem s55f_propagatorW_eq_star (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hReg : (∃ (Rg : PDE.Regime) (ν₀ : ℝ), RdRegimeHolds Rg d b.s b.M (S.invβ N) ν₀) ∨
      UlocStarRegime d b.s b.M)
    {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) b.T) {φ : Euc d → ℝ} {f : ℝ → Euc d → ℝ}
    (hf : IsClassicalAdjointW (S.coeff N) t φ f) :
    ∀ r ∈ Set.Icc (0 : ℝ) t, propagatorW (S.coeff N) r t φ = f r := by
  have hd1 : 1 ≤ d := by have := hb.hd; omega
  obtain ⟨Λ', hρ⟩ := s55f_coeffHyp b hb S N
  obtain ⟨ΛV, G₀, hV⟩ := s55f_vhyp_quadV hb.hQ b.c (b.k + 3 + 3)
  have hRg' : ∃ (Rg : PDE.Regime) (ν₀ : ℝ),
      RdRegimeHolds Rg d b.s b.M (S.invβ N) ν₀ ∨ UlocStarRegime d b.s b.M := by
    rcases hReg with ⟨Rg, ν₀, h⟩ | h
    · exact ⟨Rg, ν₀, Or.inl h⟩
    · exact ⟨PDE.Regime.R1, 0, Or.inr h⟩
  obtain ⟨Rg, ν₀, hRg⟩ := hRg'
  exact HRS.MS.Fcau.propagatorW_eq_star hd1 hb.hs0 hb.hsd (b.k + 3) (by omega) Rg b.T Λ' ΛV G₀
    (∑ i, ∑ j, |b.M i j|) b.νstar ν₀ (S.dyn N) (S.ρ N) rfl (s55f_matBound _) hV (S.hinvβ N) hρ
    hRg ht hf


theorem s55m_seq_star (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hReg : (∃ (Rg : PDE.Regime) (ν₀ : ℝ), RdRegimeHolds Rg d b.s b.M (S.invβ N) ν₀) ∨
      UlocStarRegime d b.s b.M)
    (α : MultiIndex d) {r t₀ : ℝ} (hr0 : 0 ≤ r) (ht₀ : t₀ ∈ Set.Ioc r b.T) {tn : ℕ → ℝ}
    (htn : ∀ n, tn n ∈ Set.Ioc r b.T) (hlim : Tendsto tn atTop (𝓝 t₀)) (a : Fin d) (x : Euc d) :
    ∃ ns : ℕ → ℕ, StrictMono ns ∧ Tendsto (fun i => gradComp a (propagatorW (S.coeff N) r (tn (ns i))
        (generatorW (S.coeff N) (tn (ns i)) (oscTestFun b.m α))) x) atTop
      (𝓝 (gradComp a (propagatorW (S.coeff N) r t₀ (generatorW (S.coeff N) t₀ (oscTestFun b.m α))) x)) := by
  obtain ⟨B, hB0, hfam⟩ := s55m_family b hb S N α
  obtain ⟨K, hK0, hgen⟩ := s55m_gen_rgW b hb S N
  obtain ⟨Bφ, hBφ0, hφ4, hφb⟩ := s55m_osc_bound b hb α
  have hk9 : (9 : ℝ) < b.k := by
    have := hb.hk; have : (2 : ℝ) ≤ d := by exact_mod_cast hb.hd
    linarith
  have hk9' : 9 < b.k := by exact_mod_cast hk9
  set C := S.coeff N with hC
  set φ := oscTestFun b.m α with hφ
  set ψ : ℝ → Euc d → ℝ := fun t => generatorW C t φ with hψ
  set fam : ℝ → ℝ → Euc d → ℝ := fun t r' => propagatorW C r' t (ψ t) with hfamdef
  have hmemT : ∀ n, tn n ∈ Set.Icc (0 : ℝ) b.T := fun n => ⟨hr0.trans (htn n).1.le, (htn n).2⟩
  have ht₀T : t₀ ∈ Set.Icc (0 : ℝ) b.T := ⟨hr0.trans ht₀.1.le, ht₀.2⟩
  have hcl : ∀ n, IsClassicalAdjointW C (tn n) (ψ (tn n)) (fam (tn n)) := fun n => (hfam _ (hmemT n)).1
  have hsl : ∀ n, ∀ r' ∈ Set.Icc (0 : ℝ) (tn n), ContDiff ℝ 5 (fam (tn n) r') ∧
      ∀ j ≤ 5, ∀ y, ‖iteratedFDeriv ℝ j (fam (tn n) r') y‖ ≤ B := by
    intro n r' hr'
    obtain ⟨h1, h2⟩ := (hfam _ (hmemT n)).2 r' hr'
    exact ⟨h1.of_le (by exact_mod_cast (by omega : 5 ≤ b.k + 1)), fun j hj y => h2 j (by omega) y⟩
  have hgl : ∀ n, ∀ τ ∈ Set.Icc (0 : ℝ) (tn n), ∀ y, |generatorW C τ (fam (tn n) τ) y| ≤ B * K * (1 + ‖y‖) := by
    intro n τ hτ y
    have hτT : τ ∈ Set.Icc (0 : ℝ) b.T := ⟨hτ.1, hτ.2.trans (hmemT n).2⟩
    obtain ⟨h1, h2⟩ := hsl n τ hτ
    have := (hgen τ hτT B (fam (tn n) τ) hB0 (h1.of_le (by norm_num)) (fun j hj => h2 j (by omega))).2 0
      (by norm_num) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  -- the clipped family
  set cl : ℕ → ℝ → ℝ := fun n r' => max 0 (min r' (tn n)) with hcl_def
  have hclmem : ∀ n r', cl n r' ∈ Set.Icc (0 : ℝ) (tn n) := fun n r' =>
    ⟨le_max_left _ _, max_le (hmemT n).1 (min_le_right _ _)⟩
  set F : ℕ → ℝ → Euc d → ℝ := fun n r' => fam (tn n) (cl n r') with hFdef
  set L : ℝ := max B (B * K) with hL
  have hL0 : 0 ≤ L := le_max_of_le_left hB0
  have hFb : ∀ n r' y, |F n r' y| ≤ B := by
    intro n r' y
    have := (hsl n _ (hclmem n r')).2 0 (by norm_num) y
    rwa [norm_iteratedFDeriv_zero, Real.norm_eq_abs] at this
  have hFr : ∀ n r' r'' y, |F n r' y - F n r'' y| ≤ L * (1 + ‖y‖) * |r' - r''| := by
    have key : ∀ n r' r'' y, r' ≤ r'' → |F n r' y - F n r'' y| ≤ L * (1 + ‖y‖) * |r' - r''| := by
      intro n r' r'' y hle
      have hcle : cl n r' ≤ cl n r'' := max_le_max le_rfl (min_le_min_right _ hle)
      have h1 := s55m_lip_r (hcl n) (BL := B * K) (hgl n) (hclmem n r').1 hcle (hclmem n r'').2 y
      have h2 := s55m_clip_le (tn n) r' r'' hle
      rw [abs_of_nonpos (sub_nonpos.2 hle), neg_sub]
      refine h1.trans ?_
      have : 0 ≤ B * K * (1 + ‖y‖) := by positivity
      calc B * K * (1 + ‖y‖) * (cl n r'' - cl n r') ≤ B * K * (1 + ‖y‖) * (r'' - r') :=
            mul_le_mul_of_nonneg_left h2 this
        _ ≤ L * (1 + ‖y‖) * (r'' - r') := by
            have h3 : B * K ≤ L := le_max_right _ _
            have h4 : 0 ≤ r'' - r' := sub_nonneg.2 hle
            gcongr
    intro n r' r'' y
    rcases le_total r' r'' with h | h
    · exact key n r' r'' y h
    · rw [abs_sub_comm (F n r' y), abs_sub_comm r' r'']; exact key n r'' r' y h
  have hFx : ∀ n r' y y', |F n r' y - F n r' y'| ≤ L * ‖y - y'‖ := by
    intro n r' y y'
    have hs := hsl n _ (hclmem n r')
    refine (s55m_lip_x (u := F n r') (B := B) (hs.1.differentiable (by norm_num)) (fun z => ?_) y y').trans ?_
    · have := hs.2 1 (by norm_num) z
      rwa [norm_iteratedFDeriv_one] at this
    · exact mul_le_mul_of_nonneg_right (le_max_left _ _) (norm_nonneg _)
  obtain ⟨ns, hns, g, hpt, hgr, -, -⟩ := s55m_ex F hL0 hFb hFr hFx
  set F' : ℕ → ℝ → Euc d → ℝ := fun i => F (ns i) with hF'
  have hF'b : ∀ i r', ContDiff ℝ 5 (F' i r') ∧ ∀ j ≤ 5, ∀ y, ‖iteratedFDeriv ℝ j (F' i r') y‖ ≤ B :=
    fun i r' => hsl (ns i) _ (hclmem (ns i) r')
  have htns : Tendsto (fun i => tn (ns i)) atTop (𝓝 t₀) := hlim.comp hns.tendsto_atTop
  have hftc : ∀ r₁ r₂ y, 0 ≤ r₁ → r₁ ≤ r₂ → r₂ < t₀ → ∀ᶠ i in atTop,
      F' i r₁ y - F' i r₂ y = ∫ τ in r₁..r₂, generatorW C τ (F' i τ) y ∧
        ContinuousOn (fun τ => generatorW C τ (F' i τ) y) (Set.Icc r₁ r₂) := by
    intro r₁ r₂ y h1 h12 h2
    filter_upwards [htns.eventually (Ioi_mem_nhds h2)] with i hi
    have hi' : r₂ ≤ tn (ns i) := le_of_lt hi
    have hcl_id : ∀ τ ∈ Set.Icc r₁ r₂, cl (ns i) τ = τ := by
      intro τ hτ
      show max 0 (min τ (tn (ns i))) = τ
      rw [min_eq_left (hτ.2.trans hi'), max_eq_right (h1.trans hτ.1)]
    have hFeq : ∀ τ ∈ Set.Icc r₁ r₂, F' i τ = fam (tn (ns i)) τ := fun τ hτ => by
      show fam (tn (ns i)) (cl (ns i) τ) = _
      rw [hcl_id τ hτ]
    refine ⟨?_, ?_⟩
    · rw [hFeq r₁ ⟨le_rfl, h12⟩, hFeq r₂ ⟨h12, le_rfl⟩, s55m_ftc (hcl (ns i)) h1 h12 hi' y]
      refine intervalIntegral.integral_congr fun τ hτ => ?_
      rw [Set.uIcc_of_le h12] at hτ
      simp only [hFeq τ hτ]
    · refine ((s55m_contL (hcl (ns i)) y).mono (Set.Icc_subset_Icc h1 hi')).congr fun τ hτ => ?_
      simp only [hFeq τ hτ]
  have hterm : g t₀ = ψ t₀ := by
    funext y
    have hψt : Tendsto (fun i => ψ (tn (ns i)) y) atTop (𝓝 (ψ t₀ y)) :=
      s55m_gen_tendsto_S b hb S N hBφ0 (τ := fun i => tn (ns i)) (fun i => hmemT _) ht₀T htns
        (u := fun _ => φ) (u₀ := φ)
        (fun _ => ⟨hφ4.of_le (by norm_num), fun n hn z => hφb n (by omega) z⟩)
        ⟨hφ4.of_le (by norm_num), fun n hn z => hφb n (by omega) z⟩ (fun _ => tendsto_const_nhds) y
        tendsto_const_nhds
    have h1 : Tendsto (fun i => F' i t₀ y - ψ (tn (ns i)) y) atTop (𝓝 (g t₀ y - ψ t₀ y)) :=
      (hpt (t₀) y).sub hψt
    have h2 : Tendsto (fun i => F' i t₀ y - ψ (tn (ns i)) y) atTop (𝓝 0) := by
      have h0 : Tendsto (fun i => B * K * (1 + ‖y‖) * |t₀ - tn (ns i)|) atTop (𝓝 0) := by
        have := ((htns.const_sub t₀).abs).const_mul (B * K * (1 + ‖y‖))
        simpa using this
      refine squeeze_zero_norm (fun i => ?_) h0
      have hterm_i : ψ (tn (ns i)) = fam (tn (ns i)) (tn (ns i)) := ((hcl (ns i)).terminal).symm
      rw [hterm_i, Real.norm_eq_abs]
      have := s55m_lip_r_abs (hcl (ns i)) (BL := B * K) (hgl (ns i)) (by positivity) (hclmem (ns i) t₀)
        ⟨(hmemT (ns i)).1, le_rfl⟩ y
      refine this.trans ?_
      have h3 := s55m_clip_abs (tn (ns i)) t₀ (tn (ns i))
      have h4 : max 0 (min (tn (ns i)) (tn (ns i))) = tn (ns i) := by
        rw [min_self, max_eq_right (hmemT _).1]
      rw [h4] at h3
      exact mul_le_mul_of_nonneg_left h3 (by positivity)
    have := tendsto_nhds_unique h1 h2
    linarith
  have hcl' : IsClassicalAdjointW C t₀ (ψ t₀) g :=
    s55m_limit b hb S N hB0 hK0 ht₀T (fun τ hτ u hu hub => hgen τ hτ B u hB0 hu hub) (F := F') hF'b hpt hgr hftc hterm
  have hfg : ∀ r' ∈ Set.Icc (0 : ℝ) t₀, propagatorW C r' t₀ (ψ t₀) = g r' :=
    s55f_propagatorW_eq_star b hb S N hReg ht₀T hcl'
  have hG1 := s55m_limit_G hB0 hF'b hpt r
  refine ⟨ns, hns, ?_⟩
  have hrle : ∀ i, F' i r = fam (tn (ns i)) r := fun i => by
    show fam (tn (ns i)) (cl (ns i) r) = _
    have : cl (ns i) r = r := by
      show max 0 (min r (tn (ns i))) = r
      rw [min_eq_left (htn _).1.le, max_eq_right hr0]
    rw [this]
  have hgrad := s55m_grad_tendsto (hG1.2.2 1 (by norm_num) x)
  have hcomp : Tendsto (fun i => gradient (F' i r) x a) atTop (𝓝 (gradient (g r) x a)) :=
    ((EuclideanSpace.proj a : Euc d →L[ℝ] ℝ).continuous.tendsto _).comp hgrad
  have e : gradComp a (propagatorW C r t₀ (ψ t₀)) x = gradient (g r) x a := by
    rw [hfg r ⟨hr0, ht₀.1.le⟩]; rfl
  rw [e]
  refine hcomp.congr fun i => ?_
  rw [hrle i]; rfl

/-! ### Continuity in the terminal time and `S55fMeas` -/

theorem s55m_continuousOn_star (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) (N : ℕ)
    (hReg : (∃ (Rg : PDE.Regime) (ν₀ : ℝ), RdRegimeHolds Rg d b.s b.M (S.invβ N) ν₀) ∨
      UlocStarRegime d b.s b.M)
    (α : MultiIndex d) (a : Fin d) {r : ℝ} (hr0 : 0 ≤ r) (x : Euc d) :
    ContinuousOn (fun t => gradComp a (propagatorW (S.coeff N) r t
      (generatorW (S.coeff N) t (oscTestFun b.m α))) x) (Set.Ioc r b.T) := by
  intro t₀ ht₀
  rw [ContinuousWithinAt, tendsto_iff_seq_tendsto]
  intro tn htn
  obtain ⟨hlim, hev⟩ := tendsto_nhdsWithin_iff.1 htn
  obtain ⟨n₀, hn₀⟩ := eventually_atTop.1 hev
  set tn' : ℕ → ℝ := fun n => tn (n + n₀) with htn'
  have hlim' : Tendsto tn' atTop (𝓝 t₀) := hlim.comp (tendsto_add_atTop_nat n₀)
  have hmem : ∀ n, tn' n ∈ Set.Ioc r b.T := fun n => hn₀ _ (by omega)
  rw [← tendsto_add_atTop_iff_nat n₀]
  refine tendsto_of_subseq_tendsto fun ns₁ hns₁ => ?_
  obtain ⟨ns, hns, h⟩ := s55m_seq_star b hb S N hReg α hr0 ht₀ (tn := fun i => tn' (ns₁ i)) (fun i => hmem _)
    (hlim'.comp hns₁) a x
  exact ⟨ns, h⟩

/-- The regime hypothesis at every `N`, from `S.regime N` and `lpcase_two_cover`. -/
theorem star_regime_cover (b : WholeBounds d) (S : WholeSetup b) (N : ℕ) :
    (∃ (Rg : PDE.Regime) (ν₀ : ℝ), RdRegimeHolds Rg d b.s b.M (S.invβ N) ν₀) ∨ UlocStarRegime d b.s b.M := by
  rcases S.regime N with h | ⟨c, hc⟩
  · exact Or.inl h
  · exact lpcase_two_cover (S.invβ N) hc

/-- `S55fMeas` for every `WholeSetup` (`b.Valid`). -/
theorem s55fMeas_holds (b : WholeBounds d) (hb : b.Valid) (S : WholeSetup b) : S55fMeas b S :=
  fun N a r hr α x =>
    (s55m_continuousOn_star b hb S N (star_regime_cover b S N) α a hr.1 x).aestronglyMeasurable
      measurableSet_Ioc

end HRS.MS.Go

namespace HRS.MS.Star

open HRS HRS.Whole HRS.Whole.AppendixA HRS.MS.Go

variable {d : ℕ}

/-- The frozen row `general_orbits_features` (HRS/Whole/Orbits.lean), proved. -/
theorem general_orbits_features_proof (b : WholeBounds d) (hb : b.Valid) :
    ∃ C : ℝ, ∀ S : WholeSetup b, ∀ (N : ℕ) (a : Fin d), ∀ r ∈ Set.Icc 0 b.T,
      ContDiff ℝ b.k (fun x => gradFeature (S.coeff N) b.m b.T a r x) ∧
      ∀ j : ℕ, j ≤ b.k → ∀ x : Euc d, ‖iteratedFDeriv ℝ j
        (fun y => gradFeature (S.coeff N) b.m b.T a r y) x‖ ≤ C := by
  obtain ⟨C, hC⟩ := s55f_features_of_meas b hb
  exact ⟨C, fun S N a r hr => hC S (s55fMeas_holds b hb S) N a r hr⟩

/-- The frozen row `general_orbits_maximal` (HRS/Whole/Orbits.lean), proved. -/
theorem general_orbits_maximal_proof (b : WholeBounds d) (hb : b.Valid) :
    ∃ Ctr Cmax : ℝ, ∀ S : WholeSetup b, ∀ N : ℕ, OrbitMaximalConclusion b.m b.T
      (fun (a : Fin d) (r : ℝ) (x : Euc d) => gradFeature (S.coeff N) b.m b.T a r x) Ctr Cmax := by
  obtain ⟨Ctr, Cmax, h⟩ := s55f_maximal_of_meas b hb
  exact ⟨Ctr, Cmax, fun S N => h S (s55fMeas_holds b hb S) N⟩

example := (@general_orbits_features_proof : type_of% @HRS.Whole.general_orbits_features)
example := (@general_orbits_maximal_proof : type_of% @HRS.Whole.general_orbits_maximal)

end HRS.MS.Star
