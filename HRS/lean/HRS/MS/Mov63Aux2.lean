import HRS.MS.Mov63Aux1

/-!
# S6.3, packet N1 (part 2): representatives and the evaluation functionals on `OscSpace d n`

Namespace `HRS.MS.Mov63`, helper prefix `mn_`.

* `mn_exists_fun` : every element of `OscSpace d n` (`n : ℕ`) is `OscSpace.ofFun n f` for some `f` with `MemOsc n f`.
* `mn_IsRep i n u g` : `g` is a `C^i` representative of `u : OscSpace d n` (`g` is a.e. equal to a function `f` with
  `MemOsc n f`, `ofFun n f = u`).  `mn_rep_unique`, `mn_rep_add`, `mn_rep_smul`, `mn_rep_exists`.
* `mn_repFun i n hn u` : the (unique) `C^i` representative, linear in `u` (`mn_repFun_add`, `mn_repFun_smul`) with
  `‖D^k (repFun u) x‖ ≤ C ‖u‖` (`mn_repFun_bound`, `C` independent of `u`, `x`, `k ≤ i`);
  `mn_repFun_ofFun`: `repFun (ofFun n f) = f` for `MemOsc n f`, `ContDiff i f` (no junk: off `MemOsc` nothing is claimed).
* `mn_evalD i n hn k hk x : OscSpace d n →L[ℝ] (ℝ^d)^k →L ℝ` : the `k`-th derivative at `x` of the representative,
  and `mn_eval0 n hn x : OscSpace d n →L[ℝ] ℝ` : the point evaluation (`n > d/2`).
* `mn_evalD_ofFun`, `mn_eval0_ofFun`: they act on `ofFun n f` as `D^k f x`, resp. `f x`, for `MemOsc n f` and `f` of class `C^i`
  (resp. continuous).
* `mn_continuousOn_deriv`: a path `t ↦ ofFun n (v t)` continuous in `Σ^n` has continuous pointwise derivatives
  `t ↦ D^k (v t) x`, for `v t ∈ Σ^n ∩ C^i` (this is how the class `cont` clause of S6.3 is used).
-/

noncomputable section

open MeasureTheory Filter Topology
open scoped ENNReal NNReal BigOperators ContDiff

namespace HRS.MS.Mov63

open HRS HRS.Whole HRS.MS.MovOsc HRS.MS.MovC1

variable {d : ℕ}

theorem mn_exists_fun (n : ℕ) (u : OscSpace d (n : ℝ)) :
    ∃ f : Euc d → ℝ, MemOsc (n : ℝ) f ∧ OscSpace.ofFun (n : ℝ) f = u := by
  have hm : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  set F := OscSpace.toLp u with hF
  have hL : MemLp (⇑F) 2 (volume : Measure (Euc d)) := Lp.memLp F
  have e : hL.toLp ⇑F = F := Lp.toLp_coeFn F hL
  have hsum := (OscSpace.range_toLp hm F).1 ⟨u, rfl⟩
  have hcoeff : ∀ α, hermiteCoeff (⇑F) α = inner ℝ F (hermiteLpD α) := by
    intro α
    rw [real_inner_comm, ← OscSpace.inner_hermiteLpD_toLp _ hL α, e]
  have hmem : MemOsc (n : ℝ) ⇑F := ⟨hL, hsum.congr fun α => by rw [hcoeff]⟩
  refine ⟨⇑F, hmem, ?_⟩
  exact OscSpace.toLp_injective hm (by rw [OscSpace.toLp_ofFun _ hmem, e])

theorem mn_ofFun_add (m : ℝ) {f g : Euc d → ℝ} (hf : MemOsc m f) (hg : MemOsc m g) :
    OscSpace.ofFun m (fun x => f x + g x) = OscSpace.ofFun m f + OscSpace.ofFun m g := by
  have hfg := (movc1_osc_add m hf hg).1
  rw [OscSpace.ofFun_eq hfg, OscSpace.ofFun_eq hf, OscSpace.ofFun_eq hg]
  apply lp.ext
  funext α
  change oscEigenvalue d α ^ (m / 2) * hermiteCoeff (fun x => f x + g x) α =
    oscEigenvalue d α ^ (m / 2) * hermiteCoeff f α + oscEigenvalue d α ^ (m / 2) * hermiteCoeff g α
  rw [movc1_coeff_add hf.1 hg.1]; ring

theorem mn_ofFun_smul (m c : ℝ) {f : Euc d → ℝ} (hf : MemOsc m f) :
    OscSpace.ofFun m (fun x => c * f x) = c • OscSpace.ofFun m f := by
  have hcf := (movc1_osc_smul m c hf).1
  rw [OscSpace.ofFun_eq hcf, OscSpace.ofFun_eq hf]
  apply lp.ext
  funext α
  change oscEigenvalue d α ^ (m / 2) * hermiteCoeff (fun x => c * f x) α =
    c * (oscEigenvalue d α ^ (m / 2) * hermiteCoeff f α)
  rw [movc1_coeff_smul]; ring

/-- `g` is a `C^i` representative of `u ∈ Σ^n`. -/
def mn_IsRep (i n : ℕ) (u : OscSpace d (n : ℝ)) (g : Euc d → ℝ) : Prop :=
  ContDiff ℝ (i : WithTop ℕ∞) g ∧ ∃ f : Euc d → ℝ, MemOsc (n : ℝ) f ∧ OscSpace.ofFun (n : ℝ) f = u ∧
    f =ᵐ[(volume : Measure (Euc d))] g

theorem mn_rep_unique {i n : ℕ} {u : OscSpace d (n : ℝ)} {g g' : Euc d → ℝ}
    (h : mn_IsRep i n u g) (h' : mn_IsRep i n u g') : g = g' := by
  obtain ⟨hg, f, hf, hfu, hfg⟩ := h
  obtain ⟨hg', f', hf', hfu', hfg'⟩ := h'
  have hm : (0 : ℝ) ≤ n := Nat.cast_nonneg n
  have h1 : OscSpace.toLp (OscSpace.ofFun (n : ℝ) f) = OscSpace.toLp (OscSpace.ofFun (n : ℝ) f') := by
    rw [hfu, hfu']
  rw [OscSpace.toLp_ofFun _ hf, OscSpace.toLp_ofFun _ hf'] at h1
  have h2 : f =ᵐ[(volume : Measure (Euc d))] f' := (MemLp.toLp_eq_toLp_iff hf.1 hf'.1).1 h1
  exact mn_ae_eq_cont hg.continuous hg'.continuous (hfg.symm.trans (h2.trans hfg'))

theorem mn_rep_add {i n : ℕ} {u v : OscSpace d (n : ℝ)} {g g' : Euc d → ℝ}
    (h : mn_IsRep i n u g) (h' : mn_IsRep i n v g') : mn_IsRep i n (u + v) (g + g') := by
  obtain ⟨hg, f, hf, hfu, hfg⟩ := h
  obtain ⟨hg', f', hf', hfu', hfg'⟩ := h'
  refine ⟨hg.add hg', fun x => f x + f' x, (movc1_osc_add _ hf hf').1, ?_, hfg.add hfg'⟩
  rw [mn_ofFun_add _ hf hf', hfu, hfu']

theorem mn_rep_smul {i n : ℕ} {u : OscSpace d (n : ℝ)} {g : Euc d → ℝ} (c : ℝ)
    (h : mn_IsRep i n u g) : mn_IsRep i n (c • u) (c • g) := by
  obtain ⟨hg, f, hf, hfu, hfg⟩ := h
  refine ⟨hg.const_smul c, fun x => c * f x, (movc1_osc_smul _ c hf).1, ?_, ?_⟩
  · rw [mn_ofFun_smul _ _ hf, hfu]
  · filter_upwards [hfg] with x hx
    simp [hx]

theorem mn_rep_ofFun {i n : ℕ} {f : Euc d → ℝ} (hf : MemOsc (n : ℝ) f)
    (hc : ContDiff ℝ (i : WithTop ℕ∞) f) : mn_IsRep i n (OscSpace.ofFun (n : ℝ) f) f :=
  ⟨hc, f, hf, rfl, Filter.EventuallyEq.rfl⟩

/-- Every `u ∈ Σ^n` has a `C^i` representative (`i + d/2 < n`), and all representatives obey the
derivative bound `‖D^k g x‖ ≤ C ‖u‖` with `C` independent of `u`. -/
theorem mn_rep_exists (i n : ℕ) (hn : (i : ℝ) + d / 2 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ u : OscSpace d (n : ℝ), ∃ g : Euc d → ℝ, mn_IsRep i n u g ∧
      ∀ k ≤ i, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := mn_sobolev_emb_gen i n hn
  refine ⟨C, hC0, fun u => ?_⟩
  obtain ⟨f, hf, hfu⟩ := mn_exists_fun n u
  obtain ⟨g, hg, hfg, hb⟩ := hC f hf
  refine ⟨g, ⟨hg, f, hf, hfu, hfg⟩, fun k hk x => ?_⟩
  rw [← hfu, OscSpace.norm_ofFun _ hf]
  exact hb k hk x

theorem mn_rep_bound (i n : ℕ) (hn : (i : ℝ) + d / 2 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : OscSpace d (n : ℝ)) (g : Euc d → ℝ), mn_IsRep i n u g →
      ∀ k ≤ i, ∀ x, ‖iteratedFDeriv ℝ k g x‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := mn_rep_exists i n hn
  refine ⟨C, hC0, fun u g hg k hk x => ?_⟩
  obtain ⟨g', hg', hb⟩ := hC u
  rw [mn_rep_unique hg hg']
  exact hb k hk x

/-- The `C^i` representative of `u ∈ Σ^n` (a fixed choice; unique by `mn_rep_unique`). -/
def mn_repFun (i n : ℕ) (hn : (i : ℝ) + d / 2 < n) (u : OscSpace d (n : ℝ)) : Euc d → ℝ :=
  Classical.choose (let h := mn_rep_exists i n hn
    (Classical.choose_spec h).2 u)

theorem mn_repFun_spec (i n : ℕ) (hn : (i : ℝ) + d / 2 < n) (u : OscSpace d (n : ℝ)) :
    mn_IsRep i n u (mn_repFun i n hn u) :=
  (Classical.choose_spec (let h := mn_rep_exists i n hn
    (Classical.choose_spec h).2 u)).1

theorem mn_repFun_eq {i n : ℕ} (hn : (i : ℝ) + d / 2 < n) {u : OscSpace d (n : ℝ)} {g : Euc d → ℝ}
    (h : mn_IsRep i n u g) : mn_repFun i n hn u = g :=
  mn_rep_unique (mn_repFun_spec i n hn u) h

theorem mn_repFun_add (i n : ℕ) (hn : (i : ℝ) + d / 2 < n) (u v : OscSpace d (n : ℝ)) :
    mn_repFun i n hn (u + v) = mn_repFun i n hn u + mn_repFun i n hn v :=
  mn_repFun_eq hn (mn_rep_add (mn_repFun_spec i n hn u) (mn_repFun_spec i n hn v))

theorem mn_repFun_smul (i n : ℕ) (hn : (i : ℝ) + d / 2 < n) (c : ℝ) (u : OscSpace d (n : ℝ)) :
    mn_repFun i n hn (c • u) = c • mn_repFun i n hn u :=
  mn_repFun_eq hn (mn_rep_smul c (mn_repFun_spec i n hn u))

theorem mn_repFun_ofFun {i n : ℕ} (hn : (i : ℝ) + d / 2 < n) {f : Euc d → ℝ} (hf : MemOsc (n : ℝ) f)
    (hc : ContDiff ℝ (i : WithTop ℕ∞) f) : mn_repFun i n hn (OscSpace.ofFun (n : ℝ) f) = f :=
  mn_repFun_eq hn (mn_rep_ofFun hf hc)

theorem mn_repFun_contDiff (i n : ℕ) (hn : (i : ℝ) + d / 2 < n) (u : OscSpace d (n : ℝ)) :
    ContDiff ℝ (i : WithTop ℕ∞) (mn_repFun i n hn u) := (mn_repFun_spec i n hn u).1

/-- The Sobolev constant is uniform: `‖D^k (repFun u) x‖ ≤ C ‖u‖` for all `u`, `k ≤ i`, `x`. -/
theorem mn_repFun_bound (i n : ℕ) (hn : (i : ℝ) + d / 2 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (u : OscSpace d (n : ℝ)), ∀ k ≤ i, ∀ x,
      ‖iteratedFDeriv ℝ k (mn_repFun i n hn u) x‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := mn_rep_bound i n hn
  exact ⟨C, hC0, fun u k hk x => hC u _ (mn_repFun_spec i n hn u) k hk x⟩

/-! ### Evaluation functionals -/

/-- The `k`-th derivative at `x` of the `C^i` representative, as a linear map on `OscSpace d n` (`k ≤ i`). -/
def mn_evalDL (i n : ℕ) (hn : (i : ℝ) + d / 2 < n) (k : ℕ) (hk : k ≤ i) (x : Euc d) :
    OscSpace d (n : ℝ) →ₗ[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => Euc d) ℝ where
  toFun u := iteratedFDeriv ℝ k (mn_repFun i n hn u) x
  map_add' u v := by
    rw [mn_repFun_add]
    exact iteratedFDeriv_add_apply
      (((mn_repFun_contDiff i n hn u).of_le (by exact_mod_cast hk)).contDiffAt)
      (((mn_repFun_contDiff i n hn v).of_le (by exact_mod_cast hk)).contDiffAt)
  map_smul' c u := by
    rw [mn_repFun_smul]
    exact iteratedFDeriv_const_smul_apply
      (((mn_repFun_contDiff i n hn u).of_le (by exact_mod_cast hk)).contDiffAt)

/-- **The derivative evaluation functional** `u ↦ D^k (rep u)(x)`, a continuous linear map on `Σ^n`. -/
def mn_evalD (i n : ℕ) (hn : (i : ℝ) + d / 2 < n) (k : ℕ) (hk : k ≤ i) (x : Euc d) :
    OscSpace d (n : ℝ) →L[ℝ] ContinuousMultilinearMap ℝ (fun _ : Fin k => Euc d) ℝ :=
  LinearMap.mkContinuous (mn_evalDL i n hn k hk x) (Classical.choose (mn_repFun_bound i n hn))
    (fun u => (Classical.choose_spec (mn_repFun_bound i n hn)).2 u k hk x)

theorem mn_evalD_apply (i n : ℕ) (hn : (i : ℝ) + d / 2 < n) (k : ℕ) (hk : k ≤ i) (x : Euc d)
    (u : OscSpace d (n : ℝ)) :
    mn_evalD i n hn k hk x u = iteratedFDeriv ℝ k (mn_repFun i n hn u) x := rfl

theorem mn_evalD_ofFun {i n : ℕ} (hn : (i : ℝ) + d / 2 < n) (k : ℕ) (hk : k ≤ i) (x : Euc d)
    {f : Euc d → ℝ} (hf : MemOsc (n : ℝ) f) (hc : ContDiff ℝ (i : WithTop ℕ∞) f) :
    mn_evalD i n hn k hk x (OscSpace.ofFun (n : ℝ) f) = iteratedFDeriv ℝ k f x := by
  rw [mn_evalD_apply, mn_repFun_ofFun hn hf hc]

/-- Uniform bound: `‖mn_evalD u‖ ≤ C ‖u‖` with `C` independent of `x`, `k ≤ i`, `u`. -/
theorem mn_evalD_bound (i n : ℕ) (hn : (i : ℝ) + d / 2 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (k : ℕ) (hk : k ≤ i) (x : Euc d) (u : OscSpace d (n : ℝ)),
      ‖mn_evalD i n hn k hk x u‖ ≤ C * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := mn_repFun_bound i n hn
  exact ⟨C, hC0, fun k hk x u => hC u k hk x⟩

theorem mn_hn0 {n : ℕ} (hn : (d : ℝ) / 2 < n) : ((0 : ℕ) : ℝ) + d / 2 < n := by
  simpa using hn

/-- The point evaluation on `Σ^n`, `n > d/2`: `u ↦ (continuous rep of u)(x)`. -/
def mn_eval0 (n : ℕ) (hn : (d : ℝ) / 2 < n) (x : Euc d) : OscSpace d (n : ℝ) →L[ℝ] ℝ :=
  LinearMap.mkContinuous
    { toFun := fun u => mn_repFun 0 n (mn_hn0 hn) u x
      map_add' := fun u v => by rw [mn_repFun_add]; rfl
      map_smul' := fun c u => by rw [mn_repFun_smul]; rfl }
    (Classical.choose (mn_repFun_bound 0 n (mn_hn0 hn)))
    (fun u => by
      have := (Classical.choose_spec (mn_repFun_bound 0 n (mn_hn0 hn))).2 u 0 le_rfl x
      simpa [norm_iteratedFDeriv_zero] using this)

theorem mn_eval0_apply (n : ℕ) (hn : (d : ℝ) / 2 < n) (x : Euc d) (u : OscSpace d (n : ℝ)) :
    mn_eval0 n hn x u = mn_repFun 0 n (mn_hn0 hn) u x := rfl

theorem mn_eval0_ofFun {n : ℕ} (hn : (d : ℝ) / 2 < n) (x : Euc d) {f : Euc d → ℝ}
    (hf : MemOsc (n : ℝ) f) (hc : Continuous f) :
    mn_eval0 n hn x (OscSpace.ofFun (n : ℝ) f) = f x := by
  rw [mn_eval0_apply, mn_repFun_ofFun (mn_hn0 hn) hf (by simpa using hc)]

theorem mn_eval0_bound (n : ℕ) (hn : (d : ℝ) / 2 < n) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ (x : Euc d) (u : OscSpace d (n : ℝ)), |mn_eval0 n hn x u| ≤ C * ‖u‖ := by
  obtain ⟨C, hC0, hC⟩ := mn_repFun_bound 0 n (mn_hn0 hn)
  refine ⟨C, hC0, fun x u => ?_⟩
  have := hC u 0 le_rfl x
  simpa [norm_iteratedFDeriv_zero, mn_eval0_apply] using this

/-- A path continuous in `Σ^n` has continuous pointwise derivatives. -/
theorem mn_continuousOn_deriv {i n : ℕ} (hn : (i : ℝ) + d / 2 < n) {S : Set ℝ} {v : ℝ → Euc d → ℝ}
    (hv : ∀ t ∈ S, MemOsc (n : ℝ) (v t)) (hcd : ∀ t ∈ S, ContDiff ℝ (i : WithTop ℕ∞) (v t))
    (hc : ContinuousOn (fun t => OscSpace.ofFun (n : ℝ) (v t)) S) (k : ℕ) (hk : k ≤ i) (x : Euc d) :
    ContinuousOn (fun t => iteratedFDeriv ℝ k (v t) x) S := by
  have h := (mn_evalD i n hn k hk x).continuous.comp_continuousOn hc
  refine h.congr fun t ht => ?_
  exact (mn_evalD_ofFun hn k hk x (hv t ht) (hcd t ht)).symm

end HRS.MS.Mov63
