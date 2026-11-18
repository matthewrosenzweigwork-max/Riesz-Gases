import HRS.Main.A34Aux28

/-!
# det16b L8: `t`-uniform convergence of the transported fields (Example A.16)

A `t`-uniform rewrite of `a34_field_pointwise` (A34Aux28): the mode-wise bounds `a34_aco_diff` and the
bound `a34_transport_unif` are already uniform in `t`; the pointwise `a34_embed_tendsto` is replaced by a
finite-mode plus tail estimate (`det16b_tail_head_unif`).
-/

noncomputable section

open MeasureTheory Filter Topology Finset ProbabilityTheory
open scoped ENNReal NNReal BigOperators

namespace HRS.Main.Det16

open HRS HRS.PDE HRS.PDE.ET HRS.A33 HRS.A34 HRS.Main

variable {d : ℕ}

/-- head/tail, uniform in an index `t`. -/
theorem det16b_tail_head_unif {κ ι : Type*} (w : κ → ℝ) (hw0 : ∀ k, 0 ≤ w k) (hw1 : ∀ k, w k ≤ 1)
    (hw : Tendsto w cofinite (𝓝 0)) (x : ℕ → ι → κ → ℝ) (B : ℝ)
    (hxs : ∀ N t, Summable fun k => x N t k ^ 2)
    (hB : ∀ᶠ N in atTop, ∀ t, ∑' k, x N t k ^ 2 ≤ B)
    (hx : ∀ k, ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ t, |x N t k| < ε) :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ t, ∑' k, w k * x N t k ^ 2 < ε := by
  classical
  intro ε hε
  set η : ℝ := ε / (4 * (|B| + 1)) with hη
  have hηpos : 0 < η := by positivity
  have hfin : {k | ¬ w k < η}.Finite :=
    Filter.eventually_cofinite.1 ((tendsto_order.1 hw).2 η hηpos)
  set s : Finset κ := hfin.toFinset with hs
  set ε' : ℝ := Real.sqrt (ε / (4 * ((s.card : ℝ) + 1))) with hε'
  have hε'pos : 0 < ε' := Real.sqrt_pos.2 (by positivity)
  have hε'sq : ε' ^ 2 = ε / (4 * ((s.card : ℝ) + 1)) := Real.sq_sqrt (by positivity)
  have hsmall : ∀ᶠ N in atTop, ∀ k ∈ s, ∀ t, |x N t k| < ε' :=
    (Filter.eventually_all_finset s).2 fun k _ => hx k ε' hε'pos
  filter_upwards [hB, hsmall] with N hBN hsN t
  have hsum := hxs N t
  have hpt : ∀ k, w k * x N t k ^ 2 ≤ η * x N t k ^ 2 + (if k ∈ s then x N t k ^ 2 else 0) := by
    intro k
    by_cases hk : k ∈ s
    · rw [if_pos hk]
      have h1 : w k * x N t k ^ 2 ≤ x N t k ^ 2 := mul_le_of_le_one_left (sq_nonneg _) (hw1 k)
      have h2 : 0 ≤ η * x N t k ^ 2 := mul_nonneg hηpos.le (sq_nonneg _)
      linarith
    · rw [if_neg hk, add_zero]
      have : w k < η := by
        by_contra hcon
        exact hk (by simpa [hs] using hcon)
      exact mul_le_mul_of_nonneg_right this.le (sq_nonneg _)
  have hite : Summable fun k => if k ∈ s then x N t k ^ 2 else 0 :=
    summable_of_ne_finset_zero (s := s) (fun k hk => if_neg hk)
  have hsum2 : Summable fun k => w k * x N t k ^ 2 :=
    Summable.of_nonneg_of_le (fun k => mul_nonneg (hw0 k) (sq_nonneg _))
      (fun k => mul_le_of_le_one_left (sq_nonneg _) (hw1 k)) hsum
  have h1 : ∑' k, w k * x N t k ^ 2 ≤
      ∑' k, (η * x N t k ^ 2 + (if k ∈ s then x N t k ^ 2 else 0)) :=
    hsum2.tsum_le_tsum hpt ((hsum.mul_left η).add hite)
  rw [(hsum.mul_left η).tsum_add hite, tsum_mul_left,
    tsum_eq_sum (s := s) (fun k hk => if_neg hk)] at h1
  have h2 : ∑ k ∈ s, (if k ∈ s then x N t k ^ 2 else 0) = ∑ k ∈ s, x N t k ^ 2 :=
    Finset.sum_congr rfl fun k hk => if_pos hk
  rw [h2] at h1
  have h4 : η * ∑' k, x N t k ^ 2 ≤ ε / 4 := by
    have h5 : ∑' k, x N t k ^ 2 ≤ |B| + 1 := by linarith [le_abs_self B, hBN t]
    have h6 : 0 ≤ ∑' k, x N t k ^ 2 := tsum_nonneg fun k => sq_nonneg _
    calc η * ∑' k, x N t k ^ 2 ≤ η * (|B| + 1) := mul_le_mul_of_nonneg_left h5 hηpos.le
      _ = ε / 4 := by rw [hη]; field_simp
  have h7 : ∑ k ∈ s, x N t k ^ 2 ≤ ε / 4 := by
    have h8 : ∀ k ∈ s, x N t k ^ 2 ≤ ε' ^ 2 := fun k hk =>
      (sq_le_sq' (by linarith [abs_lt.1 (hsN k hk t)]) (abs_lt.1 (hsN k hk t)).2.le)
    refine (Finset.sum_le_sum h8).trans ?_
    rw [Finset.sum_const, nsmul_eq_mul, hε'sq]
    have : (s.card : ℝ) * (ε / (4 * ((s.card : ℝ) + 1))) = ε / 4 * ((s.card : ℝ) / ((s.card : ℝ) + 1)) := by
      field_simp
    rw [this]
    have h9 : (s.card : ℝ) / ((s.card : ℝ) + 1) ≤ 1 := by
      rw [div_le_one (by positivity)]; linarith
    nlinarith
  linarith

/-- every coordinate of `F` is bounded by `‖F‖`. -/
theorem det16b_abs_coord_le {m : ℝ} (F : NegSobolev d m) (k : NonzeroLattice d) :
    |NegSobolev.coord F k| ≤ ‖F‖ := by
  obtain ⟨hs, hn⟩ := NegSobolev.coord_sq F
  have : NegSobolev.coord F k ^ 2 ≤ ‖F‖ ^ 2 := by
    rw [hn]; exact hs.le_tsum k (fun j _ => sq_nonneg _)
  exact abs_le_of_sq_le_sq this (norm_nonneg _)

/-- `ψ_k = U^{0,t} e_k` has finite `H^γ` weight. -/
theorem det16b_prop_ws (hd : 1 ≤ d) (s : ℝ) (hs0 : 0 ≤ s) (hsd : s < d) (Rg : Regime)
    (MB Λ VB ν₀ T : ℝ) (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (hA : AdjointData s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (k : NonzeroLattice d) :
    A33WS (gammaIdx d : ℝ) (propagator D ρ 0 t (Torus.realMode k)) := by
  have hm3 := ClassicalPart.three_le_mStar d
  have hγ : gammaIdx d = mStar d + d + 3 := rfl
  have hJ : mStar d ≤ gammaIdx d := by omega
  have hφs := HRS.FieldSingAux.isSmooth_realMode (d := d) k
  rcases ht.1.eq_or_lt with h0 | hpos
  · rw [← h0, a34_prop_zero hd (gammaIdx d) hJ Rg s MB Λ VB ν₀ T D ρ hA (a33_cont hφs)
      (a33_memSob _ hφs)]
    exact a33_ws_smooth _ hφs
  · obtain ⟨K, K₂, hK0, hK₂0, hu⟩ := a34_unif hd s hs0 hsd (gammaIdx d) hJ Rg MB Λ VB ν₀ T
    obtain ⟨-, hr⟩ := hu D ρ hA ⟨hpos, ht.2⟩ (a33_cont hφs) (a33_memSob _ hφs)
    obtain ⟨hm, -⟩ := (hr 0 ⟨le_rfl, hpos.le⟩).1 (gammaIdx d) (by omega) le_rfl
    exact a33_ws_of_memSobolev hm

/-- `F ↦ V^{t,0} F` is additive (subtraction form). -/
theorem det16b_transport_sub (hd : 1 ≤ d) {s : ℝ} (hs0 : 0 ≤ s) (hsd : s < d) (Rg : Regime)
    (MB Λ VB ν₀ T : ℝ) (D : DynData d) (ρ : ℝ → Torus d → ℝ)
    (hA : AdjointData s (gammaIdx d) Rg MB Λ VB D ν₀ T ρ) {t : ℝ} (ht : t ∈ Set.Icc (0 : ℝ) T)
    (F G : NegSobolev d (gammaIdx d : ℝ)) :
    transportField D ρ t (gammaIdx d : ℝ) (F - G) =
      transportField D ρ t (gammaIdx d : ℝ) F - transportField D ρ t (gammaIdx d : ℝ) G := by
  refine a34_ext fun k => ?_
  rw [a34_coord_sub, a34_coord_tf hd Rg MB Λ VB ν₀ T D ρ hA ht, a34_coord_tf hd Rg MB Λ VB ν₀ T D ρ hA ht,
    a34_coord_tf hd Rg MB Λ VB ν₀ T D ρ hA ht]
  have h := a33_eval_add_left (F - G) G (det16b_prop_ws hd s hs0 hsd Rg MB Λ VB ν₀ T D ρ hA ht k)
  rw [sub_add_cancel] at h
  rw [show NegSobolev.eval (F - G) (propagator D ρ 0 t (Torus.realMode k)) =
    NegSobolev.eval F (propagator D ρ 0 t (Torus.realMode k)) -
      NegSobolev.eval G (propagator D ρ 0 t (Torus.realMode k)) by linarith]
  ring

/-- fixed datum: the embedded transported fields converge uniformly in `t ∈ [0,T]`. -/
theorem det16b_transport_fixed_unif (s : ℝ) (Rg : Regime) (ν₀ MB Λ T VB : ℝ) (S : MainData d)
    (hs : S.s = s) (hT : S.T = T) (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
    (F : NegSobolev d (gammaIdx d : ℝ)) {γ' : ℝ} (hγ : (gammaIdx d : ℝ) < γ') :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖NegSobolev.embed γ' (S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F) -
        NegSobolev.embed γ' (L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F)‖ < ε := by
  subst hs hT
  have hd := S.hd
  have hs0 := S.hs0
  have hsd := S.hsd
  obtain ⟨K', hK'0, hK'⟩ := a34_transport_unif hd S.s hs0 hsd Rg MB Λ VB ν₀ S.T
  obtain ⟨C, hC0, hC⟩ := a34_aco_diff hd S.s hs0 hsd Rg MB Λ VB ν₀ S.T
  have hmono : ∀ N, 1 ≤ N → AdjointData S.s (gammaIdx d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
    fun N hN => HRS.PDE.StabAux.adjointData_mono (by omega) (hcoef.seq_adjoint N hN)
  have hmonoL : AdjointData S.s (gammaIdx d) Rg MB Λ VB (L.dyn S) ν₀ S.T L.ρ :=
    HRS.PDE.StabAux.adjointData_mono (by omega) hcoef.limit_adjoint
  have hfacts := fun (N : ℕ) (hN : 1 ≤ N) =>
    a34_delta_facts S L (gammaIdx d) N Rg ν₀ MB Λ VB
      (HRS.PDE.StabAux.adjointData_mono (by omega) (hcoef.seq_adjoint N hN))
      (HRS.PDE.StabAux.adjointData_mono (by omega) hcoef.limit_adjoint)
  set Δ : ℕ → ℝ := fun N => S.coeffDiscrepancy L (gammaIdx d) N with hΔ
  have hΔt : Tendsto Δ atTop (𝓝 0) := hcoef.tendsto
  have hev1 : ∀ᶠ N in atTop, Δ N ≤ 1 := (tendsto_order.1 hΔt).2 1 one_pos |>.mono fun N h => h.le
  -- the fields
  set u : ℕ → Set.Icc (0 : ℝ) S.T → NegSobolev d (gammaIdx d : ℝ) := fun N t =>
    S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F with hu
  set u₀ : Set.Icc (0 : ℝ) S.T → NegSobolev d (gammaIdx d : ℝ) := fun t =>
    L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F with hu₀
  -- coordinate bound
  set M : NonzeroLattice d → ℝ := fun k => ‖F‖ * K' + |L.A| * (‖F‖ * (C *
    sobolevNorm ((gammaIdx d + 2 : ℕ) : ℝ) (Torus.realMode k : Torus d → ℝ))) with hM
  have hcoord : ∀ N, 1 ≤ N → ∀ (t : Set.Icc (0 : ℝ) S.T) (k : NonzeroLattice d),
      |NegSobolev.coord (u N t - u₀ t) k| ≤ Δ N * M k := by
    intro N hN t k
    have ht := t.2
    obtain ⟨h0, hρ, hβ, -, hA⟩ := hfacts N hN
    have hd1 := hC (S.dyn N) (L.dyn S) (S.ρ N) L.ρ (hcoef.seq_adjoint N hN) hcoef.limit_adjoint rfl
      rfl (Δ N) h0 hρ hβ t ht F k
    have hcN := a34_coord_tf hd Rg MB Λ VB ν₀ S.T (S.dyn N) (S.ρ N) (hmono N hN) ht F k
    have hcL := a34_coord_tf hd Rg MB Λ VB ν₀ S.T (L.dyn S) L.ρ hmonoL ht F k
    set cN := NegSobolev.coord (transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F) k with hcNd
    set cL := NegSobolev.coord (transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F) k with hcLd
    have e : NegSobolev.coord (u N t - u₀ t) k = (S.AN N - L.A) * cN + L.A * (cN - cL) := by
      rw [a34_coord_sub]
      simp only [hu, hu₀, a34_coord_smul]
      ring
    have hcNb : |cN| ≤ ‖F‖ * K' :=
      (det16b_abs_coord_le _ k).trans (hK' (S.dyn N) (S.ρ N) (hmono N hN) t ht F)
    have hdiff : |cN - cL| ≤ ‖F‖ * (C * Δ N * sobolevNorm ((gammaIdx d + 2 : ℕ) : ℝ)
        (Torus.realMode k : Torus d → ℝ)) := by
      have hjp : Lattice.jp k.1 ^ (-(gammaIdx d : ℝ)) ≤ 1 :=
        Real.rpow_le_one_of_one_le_of_nonpos (Torus.jp_ge_one _) (by
          have : (0 : ℝ) ≤ gammaIdx d := Nat.cast_nonneg _
          linarith)
      have hjp0 : 0 ≤ Lattice.jp k.1 ^ (-(gammaIdx d : ℝ)) := Real.rpow_nonneg (Torus.jp_pos _).le _
      rw [hcN, hcL, ← mul_sub, abs_mul, abs_of_nonneg hjp0]
      have hr0 : 0 ≤ ‖F‖ * (C * Δ N * sobolevNorm ((gammaIdx d + 2 : ℕ) : ℝ)
        (Torus.realMode k : Torus d → ℝ)) := by
        have h0' : 0 ≤ sobolevNorm ((gammaIdx d + 2 : ℕ) : ℝ) (Torus.realMode k : Torus d → ℝ) :=
          Real.sqrt_nonneg _
        positivity
      calc Lattice.jp k.1 ^ (-(gammaIdx d : ℝ)) * |NegSobolev.eval F
            (propagator (S.dyn N) (S.ρ N) 0 t (Torus.realMode k)) -
            NegSobolev.eval F (propagator (L.dyn S) L.ρ 0 t (Torus.realMode k))|
          ≤ 1 * |NegSobolev.eval F (propagator (S.dyn N) (S.ρ N) 0 t (Torus.realMode k)) -
            NegSobolev.eval F (propagator (L.dyn S) L.ρ 0 t (Torus.realMode k))| :=
            mul_le_mul_of_nonneg_right hjp (abs_nonneg _)
        _ ≤ _ := by rw [one_mul]; exact hd1
    rw [e]
    have hAb : |S.AN N - L.A| ≤ Δ N := hA
    calc |(S.AN N - L.A) * cN + L.A * (cN - cL)|
        ≤ |(S.AN N - L.A) * cN| + |L.A * (cN - cL)| := abs_add_le _ _
      _ ≤ Δ N * (‖F‖ * K') + |L.A| * (‖F‖ * (C * Δ N * sobolevNorm ((gammaIdx d + 2 : ℕ) : ℝ)
            (Torus.realMode k : Torus d → ℝ))) := by
          rw [abs_mul, abs_mul]
          exact add_le_add (mul_le_mul hAb hcNb (abs_nonneg _) h0)
            (mul_le_mul_of_nonneg_left hdiff (abs_nonneg _))
      _ = Δ N * M k := by simp only [hM]; ring
  -- norm bound
  have hnorm : ∀ N, 1 ≤ N → Δ N ≤ 1 → ∀ (t : Set.Icc (0 : ℝ) S.T),
      ‖u N t - u₀ t‖ ^ 2 ≤ ((2 * |L.A| + 1) * (‖F‖ * K')) ^ 2 := by
    intro N hN hN1 t
    have ht := t.2
    have h1 := hK' (S.dyn N) (S.ρ N) (hmono N hN) t ht F
    have h2 := hK' (L.dyn S) L.ρ hmonoL t ht F
    have hAb : |S.AN N| ≤ |L.A| + 1 := by
      have := (hfacts N hN).2.2.2.2
      have h3 : |S.AN N| ≤ |L.A| + |S.AN N - L.A| := by
        have := abs_add_le L.A (S.AN N - L.A)
        simpa using this
      linarith
    have hFK : 0 ≤ ‖F‖ * K' := mul_nonneg (norm_nonneg _) hK'0
    have hn1 : ‖u N t‖ ≤ (|L.A| + 1) * (‖F‖ * K') := by
      simp only [hu]
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul hAb h1 (norm_nonneg _) (by positivity)
    have hn2 : ‖u₀ t‖ ≤ |L.A| * (‖F‖ * K') := by
      simp only [hu₀]
      rw [norm_smul, Real.norm_eq_abs]
      exact mul_le_mul_of_nonneg_left h2 (abs_nonneg _)
    have h4 := (norm_sub_le _ _).trans (add_le_add hn1 hn2)
    refine pow_le_pow_left₀ (norm_nonneg _) (h4.trans (le_of_eq ?_)) 2
    ring
  -- assemble
  intro ε hε
  have hw := a34_w_tendsto (d := d) (δ := γ' - gammaIdx d) (by linarith)
  have key := det16b_tail_head_unif (fun k : NonzeroLattice d => (Lattice.jp k.1 ^ (-(γ' - gammaIdx d))) ^ 2)
    (fun k => sq_nonneg _) (fun k => a34_weight_le_one (by linarith) k) hw
    (fun N t k => NegSobolev.coord (u N t - u₀ t) k) (((2 * |L.A| + 1) * (‖F‖ * K')) ^ 2)
    (fun N t => (NegSobolev.coord_sq _).1)
    (by
      filter_upwards [eventually_ge_atTop 1, hev1] with N hN hN1 t
      rw [← (NegSobolev.coord_sq (u N t - u₀ t)).2]
      exact hnorm N hN hN1 t)
    (by
      intro k ε' hε'
      have hlim : Tendsto (fun N => Δ N * M k) atTop (𝓝 0) := by simpa using hΔt.mul_const (M k)
      filter_upwards [eventually_ge_atTop 1, (tendsto_order.1 hlim).2 ε' hε'] with N hN hN2 t
      exact lt_of_le_of_lt (hcoord N hN t k) hN2) (ε ^ 2) (by positivity)
  filter_upwards [key] with N hN t ht
  have hNt := hN ⟨t, ht⟩
  have hsq : ‖NegSobolev.embed γ' (u N ⟨t, ht⟩) - NegSobolev.embed γ' (u₀ ⟨t, ht⟩)‖ ^ 2 < ε ^ 2 := by
    rw [← a34_embed_sub hγ.le, a34_embed_norm_sq hγ.le]
    exact hNt
  exact lt_of_pow_lt_pow_left₀ 2 hε.le hsq

/-- **L8** (`t`-uniform transport convergence).  If `F_N → F₀` in `H^{-γ}` (`γ = gammaIdx d`), then for
every `γ' > γ`,
`sup_{t ∈ [0,T]} ‖embed_{γ'}(A_N V_N^{t,0} F_N) - embed_{γ'}(L.A V_∞^{t,0} F₀)‖ → 0`
(stated as: for every `ε > 0` eventually in `N`, for all `t ∈ [0,T]`, the distance is `< ε`). -/
theorem det16b_transport_unif_t (s : ℝ) (Rg : Regime) (ν₀ MB Λ T VB : ℝ) (S : MainData d)
    (hs : S.s = s) (hT : S.T = T) (L : LimitCoeffs d)
    (hcoef : CoeffConvergence S L Rg ν₀ MB Λ VB (gammaIdx d + 2) (gammaIdx d))
    (F : ℕ → NegSobolev d (gammaIdx d : ℝ)) (F₀ : NegSobolev d (gammaIdx d : ℝ))
    (hF : Tendsto F atTop (𝓝 F₀)) {γ' : ℝ} (hγ : (gammaIdx d : ℝ) < γ') :
    ∀ ε : ℝ, 0 < ε → ∀ᶠ N in atTop, ∀ t ∈ Set.Icc (0 : ℝ) T,
      ‖NegSobolev.embed γ' (S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) (F N)) -
        NegSobolev.embed γ' (L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F₀)‖ < ε := by
  intro ε hε
  have hfix := det16b_transport_fixed_unif s Rg ν₀ MB Λ T VB S hs hT L hcoef F₀ hγ (ε / 2) (by positivity)
  subst hs hT
  have hd := S.hd
  have hs0 := S.hs0
  have hsd := S.hsd
  obtain ⟨K', hK'0, hK'⟩ := a34_transport_unif hd S.s hs0 hsd Rg MB Λ VB ν₀ S.T
  have hmono : ∀ N, 1 ≤ N → AdjointData S.s (gammaIdx d) Rg MB Λ VB (S.dyn N) ν₀ S.T (S.ρ N) :=
    fun N hN => HRS.PDE.StabAux.adjointData_mono (by omega) (hcoef.seq_adjoint N hN)
  have hfacts := fun (N : ℕ) (hN : 1 ≤ N) =>
    a34_delta_facts S L (gammaIdx d) N Rg ν₀ MB Λ VB
      (HRS.PDE.StabAux.adjointData_mono (by omega) (hcoef.seq_adjoint N hN))
      (HRS.PDE.StabAux.adjointData_mono (by omega) hcoef.limit_adjoint)
  set Δ : ℕ → ℝ := fun N => S.coeffDiscrepancy L (gammaIdx d) N with hΔ
  have hΔt : Tendsto Δ atTop (𝓝 0) := hcoef.tendsto
  have hev1 : ∀ᶠ N in atTop, Δ N ≤ 1 := (tendsto_order.1 hΔt).2 1 one_pos |>.mono fun N h => h.le
  have hFd : Tendsto (fun N => ‖F N - F₀‖) atTop (𝓝 0) := by
    rw [← tendsto_iff_norm_sub_tendsto_zero]; exact hF
  have hbd : Tendsto (fun N => (|L.A| + 1) * (K' * ‖F N - F₀‖)) atTop (𝓝 0) := by
    simpa using (hFd.const_mul K').const_mul (|L.A| + 1)
  filter_upwards [hfix, eventually_ge_atTop 1, hev1, (tendsto_order.1 hbd).2 (ε / 2) (by positivity)]
    with N hN hN1 hN2 hN3 t ht
  have hA : |S.AN N| ≤ |L.A| + 1 := by
    have := (hfacts N hN1).2.2.2.2
    have h3 : |S.AN N| ≤ |L.A| + |S.AN N - L.A| := by
      have := abs_add_le L.A (S.AN N - L.A)
      simpa using this
    linarith
  have hsub := det16b_transport_sub hd hs0 hsd Rg MB Λ VB ν₀ S.T (S.dyn N) (S.ρ N) (hmono N hN1) ht
    (F N) F₀
  have e : NegSobolev.embed γ' (S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) (F N)) -
        NegSobolev.embed γ' (L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F₀) =
      NegSobolev.embed γ' (S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) (F N - F₀)) +
      (NegSobolev.embed γ' (S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) F₀) -
        NegSobolev.embed γ' (L.A • transportField (L.dyn S) L.ρ t (gammaIdx d : ℝ) F₀)) := by
    rw [hsub, smul_sub, a34_embed_sub hγ.le]
    abel
  rw [e]
  have hb1 : ‖NegSobolev.embed γ' (S.AN N • transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ)
      (F N - F₀))‖ ≤ (|L.A| + 1) * (K' * ‖F N - F₀‖) := by
    refine (NegSobolev.norm_embed_le γ' hγ.le _).trans ?_
    rw [norm_smul, Real.norm_eq_abs]
    have h1 := hK' (S.dyn N) (S.ρ N) (hmono N hN1) t ht (F N - F₀)
    calc |S.AN N| * ‖transportField (S.dyn N) (S.ρ N) t (gammaIdx d : ℝ) (F N - F₀)‖
        ≤ (|L.A| + 1) * (‖F N - F₀‖ * K') :=
          mul_le_mul hA h1 (norm_nonneg _) (by positivity)
      _ = _ := by ring
  have := hN t ht
  calc _ ≤ _ := norm_add_le _ _
    _ < ε / 2 + ε / 2 := add_lt_add_of_le_of_lt (hb1.trans hN3.le) this
    _ = ε := by ring

end HRS.Main.Det16
