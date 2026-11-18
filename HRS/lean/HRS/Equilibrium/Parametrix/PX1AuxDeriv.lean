import HRS.Equilibrium.Parametrix.Defs

/-!
# Prop 4.13 parametrix, packet PX1: calculus of iterated derivatives

Generic facts on iterated Fréchet derivatives used by the calculus of conormal classes:

* `iteratedFDeriv_dirD`: `D^n (f' · h) = D^{n+1} f (· , h)`;
* `iteratedFDeriv_perm`: the `n`-th derivative of a `C^n` function is symmetric (finite smoothness;
  Mathlib only has the analytic case and `n = 2`);
* `mixedDeriv_apply`: the mixed derivative `mixedDeriv a c G X z` (an `X`-jet of a `z`-jet) is the
  `(a+c)`-th derivative evaluated on the pattern `(u_i, 0)_{i<a}, (0, v_j)_{j<c}`.
-/

open MeasureTheory Filter Topology
noncomputable section

namespace HRS.Parx

section Generic
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Directional derivative `y ↦ f'(y) h`. -/
def dirD (h : E) (f : E → F) : E → F := fun y => fderiv ℝ f y h

theorem iteratedFDeriv_dirD {f : E → F} {x : E} {n : ℕ} (hf : ContDiffAt ℝ (n + 1 : ℕ) f x)
    (h : E) (w : Fin n → E) :
    iteratedFDeriv ℝ n (dirD h f) x w = iteratedFDeriv ℝ (n + 1) f x (Fin.snoc w h) := by
  rw [iteratedFDeriv_succ_apply_right]
  simp only [Fin.init_snoc, Fin.snoc_last]
  have hd : ContDiffAt ℝ n (fderiv ℝ f) x := hf.fderiv_right (m := n) (by norm_num)
  have := (ContinuousLinearMap.apply ℝ F h).iteratedFDeriv_comp_left hd (i := n) le_rfl
  have h2 : dirD h f = (ContinuousLinearMap.apply ℝ F h) ∘ fderiv ℝ f := rfl
  rw [h2, this]
  rfl

end Generic

section PermSymm
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Symmetry of the `n`-th derivative at a point. -/
def PermSymm (n : ℕ) (f : E → F) (x : E) : Prop :=
  ∀ (σ : Equiv.Perm (Fin n)) (v : Fin n → E),
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v

theorem permSymm_of_swaps {m : ℕ} {f : E → F} {x : E}
    (h : ∀ (i : Fin m) (v : Fin (m + 1) → E),
      iteratedFDeriv ℝ (m + 1) f x (v ∘ Equiv.swap i.castSucc i.succ) =
        iteratedFDeriv ℝ (m + 1) f x v) : PermSymm (m + 1) f x := by
  intro σ
  have hmem : σ ∈ Submonoid.closure (Set.range fun i : Fin m ↦ Equiv.swap i.castSucc i.succ) := by
    rw [Equiv.Perm.mclosure_swap_castSucc_succ]; trivial
  induction hmem using Submonoid.closure_induction with
  | mem τ hτ =>
    obtain ⟨i, rfl⟩ := hτ
    exact h i
  | one => intro v; rfl
  | mul σ τ _ _ hσ hτ =>
    intro v
    have : v ∘ (σ * τ) = (v ∘ σ) ∘ τ := rfl
    rw [this, hτ (v ∘ σ), hσ v]

end PermSymm

section PermSymm2
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem permSymm_two {f : E → F} {x : E} (hf : ContDiffAt ℝ 2 f x) : PermSymm 2 f x := by
  have hs : IsSymmSndFDerivAt ℝ f x := hf.isSymmSndFDerivAt (by simp)
  refine permSymm_of_swaps (m := 1) ?_
  intro i v
  have hi : i = 0 := Subsingleton.elim _ _
  subst hi
  have e1 : ∀ w : Fin 2 → E, iteratedFDeriv ℝ 2 f x w = fderiv ℝ (fderiv ℝ f) x (w 0) (w 1) := by
    intro w; rw [iteratedFDeriv_two_apply]
  rw [e1, e1]
  have := hs.eq (v 0) (v 1)
  simpa [Equiv.swap_apply_left, Equiv.swap_apply_right] using this.symm

end PermSymm2

section PermSymm3
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem permSymm_step {n : ℕ} (hn : 2 ≤ n)
    (ih : ∀ (g : E → F) (y : E), ContDiffAt ℝ n g y → PermSymm n g y)
    {f : E → F} {x : E} (hf : ContDiffAt ℝ (n + 1 : ℕ) f x) : PermSymm (n + 1) f x := by
  refine permSymm_of_swaps (m := n) ?_
  intro i v
  by_cases hA : i.val + 1 < n
  · -- the swap fixes the last slot: peel on the right
    set i' : Fin n := ⟨i.val + 1, hA⟩ with hi'
    have hσ : Equiv.swap i.castSucc i.succ = Equiv.swap i.castSucc (Fin.castSucc i') := by
      congr 1
    have hlast : (Equiv.swap i.castSucc i.succ) (Fin.last n) = Fin.last n := by
      apply Equiv.swap_apply_of_ne_of_ne
      · exact (Fin.castSucc_lt_last i).ne.symm
      · intro h; have := congrArg Fin.val h; simp at this; omega
    have key : ∀ w : Fin (n + 1) → E, iteratedFDeriv ℝ (n + 1) f x w =
        iteratedFDeriv ℝ n (dirD (w (Fin.last n)) f) x (Fin.init w) := by
      intro w
      have := iteratedFDeriv_dirD hf (w (Fin.last n)) (Fin.init w)
      rw [this, Fin.snoc_init_self]
    rw [key, key v]
    have hinit : Fin.init (v ∘ Equiv.swap i.castSucc i.succ) =
        Fin.init v ∘ Equiv.swap i i' := by
      funext k
      simp only [Fin.init, Function.comp]
      rw [hσ, (Fin.castSucc_injective n).swap_apply]
    have hl : (v ∘ Equiv.swap i.castSucc i.succ) (Fin.last n) = v (Fin.last n) := by
      simp [hlast]
    rw [hinit, hl]
    have hg : ContDiffAt ℝ n (dirD (v (Fin.last n)) f) x := by
      have := (hf.fderiv_right_succ (n := n)).clm_apply (contDiffAt_const (c := v (Fin.last n)))
      exact this
    exact ih _ x hg (Equiv.swap i i') (Fin.init v)
  · -- the swap fixes the first slot: peel on the left
    have hi0 : 0 < i.val := by
      have : i.val + 1 = n := by omega
      omega
    set a' : Fin n := ⟨i.val - 1, by omega⟩ with ha'
    set b' : Fin n := i with hb'
    have hσ : Equiv.swap i.castSucc i.succ = Equiv.swap a'.succ b'.succ := by
      congr 1
      · ext; simp [ha']; omega
    have hnear : ∀ᶠ y in 𝓝 x, ContDiffAt ℝ n f y := by
      filter_upwards [hf.eventually (by simp)] with y hy
      exact hy.of_le (by exact_mod_cast (by omega : n ≤ n + 1))
    have hdiff : DifferentiableAt ℝ (iteratedFDeriv ℝ n f) x :=
      (hf.iteratedFDeriv_right (i := n) (m := 1) (by exact_mod_cast (by omega : 1 + n ≤ n + 1))).differentiableAt (by simp)
    have key : ∀ w : Fin (n + 1) → E, iteratedFDeriv ℝ (n + 1) f x w =
        fderiv ℝ (iteratedFDeriv ℝ n f) x (w 0) (Fin.tail w) := fun w =>
      iteratedFDeriv_succ_apply_left w
    have hsym : ∀ (h : E) (τ : Equiv.Perm (Fin n)) (w : Fin n → E),
        fderiv ℝ (iteratedFDeriv ℝ n f) x h (w ∘ τ) = fderiv ℝ (iteratedFDeriv ℝ n f) x h w := by
      intro h τ w
      rw [← fderiv_continuousMultilinear_apply_const_apply hdiff _ h,
        ← fderiv_continuousMultilinear_apply_const_apply hdiff _ h]
      congr 1
      apply Filter.EventuallyEq.fderiv_eq
      filter_upwards [hnear] with y hy
      exact ih f y hy τ w
    rw [key, key v]
    have h0 : (v ∘ Equiv.swap i.castSucc i.succ) 0 = v 0 := by
      have : (Equiv.swap i.castSucc i.succ) 0 = 0 := by
        apply Equiv.swap_apply_of_ne_of_ne
        · intro h; have := congrArg Fin.val h; simp at this; omega
        · exact (Fin.succ_ne_zero _).symm
      simp [this]
    have htail : Fin.tail (v ∘ Equiv.swap i.castSucc i.succ) =
        Fin.tail v ∘ Equiv.swap a' b' := by
      funext k
      simp only [Fin.tail, Function.comp]
      rw [hσ, (Fin.succ_injective n).swap_apply]
    rw [h0, htail]
    exact hsym _ _ _

end PermSymm3

section PermSymm4
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- The `n`-th Fréchet derivative of a `C^n` function is symmetric. -/
theorem iteratedFDeriv_perm {n : ℕ} {f : E → F} {x : E} (hf : ContDiffAt ℝ n f x)
    (σ : Equiv.Perm (Fin n)) (v : Fin n → E) :
    iteratedFDeriv ℝ n f x (v ∘ σ) = iteratedFDeriv ℝ n f x v := by
  induction n generalizing f x with
  | zero => 
    have : σ = 1 := Subsingleton.elim _ _
    subst this; rfl
  | succ n ih =>
    by_cases hn0 : n = 0
    · subst hn0
      have : σ = 1 := by
        ext k
        have h1 := (σ k).isLt
        have h2 := ((1 : Equiv.Perm (Fin (0 + 1))) k).isLt
        omega
      subst this; rfl
    by_cases hn1 : n = 1
    · subst hn1
      exact permSymm_two hf σ v
    exact permSymm_step (n := n) (by omega) (fun g y hg => fun σ v => ih hg σ v) hf σ v

end PermSymm4

section FactA
variable {d : ℕ}

/-- The pattern tuple: `a` slots in the `X` factor followed by `c` slots in the `z` factor. -/
def pat {a c : ℕ} (u : Fin a → Euc d) (v : Fin c → Euc d) : Fin (a + c) → Euc d × Euc d :=
  Fin.append (fun i => (u i, 0)) (fun j => (0, v j))

theorem pat_snoc_right {a c : ℕ} (u : Fin a → Euc d) (v : Fin c → Euc d) (h : Euc d) :
    pat u (Fin.snoc v h : Fin (c + 1) → Euc d) = (Fin.snoc (pat u v) ((0 : Euc d), h) : Fin (a + c + 1) → Euc d × Euc d) := by
  unfold pat
  have : (fun j => ((0 : Euc d), (Fin.snoc v h : Fin (c + 1) → Euc d) j)) =
      (Fin.snoc (fun j => ((0 : Euc d), v j)) ((0 : Euc d), h) : Fin (c + 1) → Euc d × Euc d) := by
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp
    · simp
  rw [this, Fin.append_snoc]

theorem pat_snoc_left {a : ℕ} (u : Fin a → Euc d) (h : Euc d) :
    pat (Fin.snoc u h : Fin (a + 1) → Euc d) (Fin.elim0 : Fin 0 → Euc d) =
      (Fin.snoc (pat u (Fin.elim0 : Fin 0 → Euc d)) (h, (0 : Euc d)) : Fin (a + 0 + 1) → Euc d × Euc d) := by
  funext k
  unfold pat
  have e : (fun j : Fin 0 => ((0 : Euc d), (Fin.elim0 j : Euc d))) =
      (Fin.elim0 : Fin 0 → Euc d × Euc d) := funext fun j => j.elim0
  rw [e, Fin.append_elim0, Fin.append_elim0]
  refine Fin.lastCases ?_ (fun k => ?_) k
  · simp
  · simp

end FactA

section FactA2
variable {d : ℕ} {F : Type*} [NormedAddCommGroup F] [NormedSpace ℝ F]

theorem fderiv_slice_snd {G : Euc d × Euc d → F} {X z : Euc d} (hG : DifferentiableAt ℝ G (X, z))
    (h : Euc d) :
    fderiv ℝ (fun z' => G (X, z')) z h = fderiv ℝ G (X, z) (0, h) := by
  have h1 : HasFDerivAt (fun z' : Euc d => ((X, z') : Euc d × Euc d))
      ((0 : Euc d →L[ℝ] Euc d).prod (ContinuousLinearMap.id ℝ (Euc d))) z :=
    (hasFDerivAt_const X z).prodMk (hasFDerivAt_id z)
  have h2 : HasFDerivAt (fun z' : Euc d => G (X, z')) _ z := (hG.hasFDerivAt).comp z h1
  rw [h2.fderiv]
  simp

theorem fderiv_slice_fst {G : Euc d × Euc d → F} {X z : Euc d} (hG : DifferentiableAt ℝ G (X, z))
    (h : Euc d) :
    fderiv ℝ (fun X' => G (X', z)) X h = fderiv ℝ G (X, z) (h, 0) := by
  have h1 : HasFDerivAt (fun X' : Euc d => ((X', z) : Euc d × Euc d))
      ((ContinuousLinearMap.id ℝ (Euc d)).prod (0 : Euc d →L[ℝ] Euc d)) X :=
    (hasFDerivAt_id X).prodMk (hasFDerivAt_const z X)
  have h2 : HasFDerivAt (fun X' : Euc d => G (X', z)) _ X := (hG.hasFDerivAt).comp X h1
  rw [h2.fderiv]
  simp

theorem inner_jet {U : Set (Euc d × Euc d)} (hU : IsOpen U) :
    ∀ (c : ℕ) (G : Euc d × Euc d → F), ContDiffOn ℝ (c : WithTop ℕ∞) G U →
      ∀ (X z : Euc d), (X, z) ∈ U → ∀ v : Fin c → Euc d,
        iteratedFDeriv ℝ c (fun z' => G (X, z')) z v =
          iteratedFDeriv ℝ c G (X, z) (fun j => ((0 : Euc d), v j)) := by
  intro c
  induction c with
  | zero =>
    intro G _ X z _ v
    simp [iteratedFDeriv_zero_apply]
  | succ c ih =>
    intro G hG X z hz v
    have hGat : ContDiffAt ℝ ((c + 1 : ℕ) : WithTop ℕ∞) G (X, z) := hG.contDiffAt (hU.mem_nhds hz)
    have hslice : ContDiffAt ℝ ((c + 1 : ℕ) : WithTop ℕ∞) (fun z' => G (X, z')) z :=
      hGat.comp z (contDiffAt_const.prodMk contDiffAt_id)
    set h := v (Fin.last c) with hh
    have hv : v = Fin.snoc (Fin.init v) h := (Fin.snoc_init_self v).symm
    have e1 := iteratedFDeriv_dirD hslice h (Fin.init v)
    rw [← hv] at e1
    rw [← e1]
    have hopen : ∀ᶠ z' in 𝓝 z, (X, z') ∈ U := by
      have : Continuous fun z' : Euc d => ((X, z') : Euc d × Euc d) := by fun_prop
      exact this.continuousAt.eventually (hU.mem_nhds hz)
    have hev : dirD h (fun z' => G (X, z')) =ᶠ[𝓝 z] fun z' => dirD ((0 : Euc d), h) G (X, z') := by
      filter_upwards [hopen] with z' hz'
      have hd : DifferentiableAt ℝ G (X, z') :=
        (hG.differentiableOn (by exact_mod_cast Nat.succ_ne_zero c) |>.differentiableAt (hU.mem_nhds hz'))
      exact fderiv_slice_snd hd h
    rw [(hev.iteratedFDeriv ℝ c).eq_of_nhds]
    have hG' : ContDiffOn ℝ (c : WithTop ℕ∞) (dirD ((0 : Euc d), h) G) U := by
      have := (hG.fderiv_of_isOpen hU (m := c) (by norm_num))
      exact this.clm_apply contDiffOn_const
    rw [ih _ hG' X z hz (Fin.init v)]
    rw [iteratedFDeriv_dirD hGat ((0 : Euc d), h)]
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [hh]
    · simp [Fin.init]

theorem outer_jet {U : Set (Euc d × Euc d)} (hU : IsOpen U) :
    ∀ (a : ℕ) (G : Euc d × Euc d → F), ContDiffOn ℝ (a : WithTop ℕ∞) G U →
      ∀ (X z : Euc d), (X, z) ∈ U → ∀ u : Fin a → Euc d,
        iteratedFDeriv ℝ a (fun X' => G (X', z)) X u =
          iteratedFDeriv ℝ a G (X, z) (fun j => (u j, (0 : Euc d))) := by
  intro a
  induction a with
  | zero =>
    intro G _ X z _ v
    simp [iteratedFDeriv_zero_apply]
  | succ a ih =>
    intro G hG X z hz v
    have hGat : ContDiffAt ℝ ((a + 1 : ℕ) : WithTop ℕ∞) G (X, z) := hG.contDiffAt (hU.mem_nhds hz)
    have hslice : ContDiffAt ℝ ((a + 1 : ℕ) : WithTop ℕ∞) (fun X' => G (X', z)) X :=
      hGat.comp X (contDiffAt_id.prodMk contDiffAt_const)
    set h := v (Fin.last a) with hh
    have hv : v = Fin.snoc (Fin.init v) h := (Fin.snoc_init_self v).symm
    have e1 := iteratedFDeriv_dirD hslice h (Fin.init v)
    rw [← hv] at e1
    rw [← e1]
    have hopen : ∀ᶠ X' in 𝓝 X, (X', z) ∈ U := by
      have : Continuous fun X' : Euc d => ((X', z) : Euc d × Euc d) := by fun_prop
      exact this.continuousAt.eventually (hU.mem_nhds hz)
    have hev : dirD h (fun X' => G (X', z)) =ᶠ[𝓝 X] fun X' => dirD (h, (0 : Euc d)) G (X', z) := by
      filter_upwards [hopen] with X' hX'
      have hd : DifferentiableAt ℝ G (X', z) :=
        (hG.differentiableOn (by exact_mod_cast Nat.succ_ne_zero a) |>.differentiableAt (hU.mem_nhds hX'))
      exact fderiv_slice_fst hd h
    rw [(hev.iteratedFDeriv ℝ a).eq_of_nhds]
    have hG' : ContDiffOn ℝ (a : WithTop ℕ∞) (dirD (h, (0 : Euc d)) G) U := by
      have := (hG.fderiv_of_isOpen hU (m := a) (by norm_num))
      exact this.clm_apply contDiffOn_const
    rw [ih _ hG' X z hz (Fin.init v)]
    rw [iteratedFDeriv_dirD hGat (h, (0 : Euc d))]
    congr 1
    funext j
    refine Fin.lastCases ?_ (fun k => ?_) j
    · simp [hh]
    · simp [Fin.init]

end FactA2

section FactA3
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

theorem iteratedFDeriv_apply_append {U : Set E} (hU : IsOpen U) (a : ℕ) :
    ∀ (c : ℕ) (G : E → F), ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) G U →
      ∀ q ∈ U, ∀ (w : Fin a → E) (ξ : Fin c → E),
        iteratedFDeriv ℝ a (fun y => iteratedFDeriv ℝ c G y ξ) q w =
          iteratedFDeriv ℝ (a + c) G q (Fin.append w ξ) := by
  intro c
  induction c with
  | zero =>
    intro G hG q hq w ξ
    have e : ξ = Fin.elim0 := Subsingleton.elim _ _
    subst e
    simp only [iteratedFDeriv_zero_apply]
    rw [Fin.append_elim0]
    rfl
  | succ c ih =>
    intro G hG q hq w ξ
    have hv : ξ = Fin.snoc (Fin.init ξ) (ξ (Fin.last c)) := (Fin.snoc_init_self ξ).symm
    set h := ξ (Fin.last c) with hh
    have hGat : ∀ y ∈ U, ContDiffAt ℝ ((c + 1 : ℕ) : WithTop ℕ∞) G y := fun y hy =>
      (hG.contDiffAt (hU.mem_nhds hy)).of_le (by exact_mod_cast (by omega : c + 1 ≤ a + (c + 1)))
    have hev : (fun y => iteratedFDeriv ℝ (c + 1) G y ξ) =ᶠ[𝓝 q]
        fun y => iteratedFDeriv ℝ c (dirD h G) y (Fin.init ξ) := by
      filter_upwards [hU.mem_nhds hq] with y hy
      have := iteratedFDeriv_dirD (hGat y hy) h (Fin.init ξ)
      rw [this, ← hv]
    rw [(hev.iteratedFDeriv ℝ a).eq_of_nhds]
    have hG' : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) (dirD h G) U := by
      have := (hG.fderiv_of_isOpen hU (m := ((a + c : ℕ) : WithTop ℕ∞)) (by
        norm_cast))
      exact this.clm_apply contDiffOn_const
    rw [ih _ hG' q hq w (Fin.init ξ)]
    have hq' : ContDiffAt ℝ ((a + c + 1 : ℕ) : WithTop ℕ∞) G q := hG.contDiffAt (hU.mem_nhds hq)
    rw [iteratedFDeriv_dirD hq' h]
    have : (Fin.append w ξ : Fin (a + (c + 1)) → E) = Fin.snoc (Fin.append w (Fin.init ξ)) h := by
      conv_lhs => rw [hv]
      exact Fin.append_snoc _ _ _
    rw [this]
    rfl

end FactA3

section FactA4
variable {d : ℕ}

theorem contDiffOn_iteratedFDeriv_of_isOpen {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E]
    [NormedAddCommGroup F] [NormedSpace ℝ F] {U : Set E} (hU : IsOpen U) {G : E → F} {n : WithTop ℕ∞}
    (hG : ContDiffOn ℝ n G U) {m i : ℕ} (hmn : (m : WithTop ℕ∞) + i ≤ n) :
    ContDiffOn ℝ (m : WithTop ℕ∞) (iteratedFDeriv ℝ i G) U := fun y hy =>
  ((hG.contDiffAt (hU.mem_nhds hy)).iteratedFDeriv_right hmn).contDiffWithinAt

theorem mixedDeriv_apply {U : Set (Euc d × Euc d)} (hU : IsOpen U) {a c : ℕ}
    {G : Euc d × Euc d → ℝ} (hG : ContDiffOn ℝ ((a + c : ℕ) : WithTop ℕ∞) G U) {X z : Euc d}
    (hz : (X, z) ∈ U) (u : Fin a → Euc d) (v : Fin c → Euc d) :
    mixedDeriv a c G X z u v = iteratedFDeriv ℝ (a + c) G (X, z) (pat u v) := by
  set K := iteratedFDeriv ℝ c G with hK
  let Lc : ContinuousMultilinearMap ℝ (fun _ : Fin c => Euc d × Euc d) ℝ →L[ℝ]
      ContinuousMultilinearMap ℝ (fun _ : Fin c => Euc d) ℝ :=
    ContinuousMultilinearMap.compContinuousLinearMapL (fun _ => ContinuousLinearMap.inr ℝ (Euc d) (Euc d))
  have hca : (c : WithTop ℕ∞) ≤ ((a + c : ℕ) : WithTop ℕ∞) := by exact_mod_cast (by omega : c ≤ a + c)
  have hGc : ContDiffOn ℝ (c : WithTop ℕ∞) G U := hG.of_le hca
  have hKa : ContDiffOn ℝ (a : WithTop ℕ∞) K U :=
    contDiffOn_iteratedFDeriv_of_isOpen hU hG (m := a) (i := c) (by exact_mod_cast le_refl (a + c))
  have hopen : ∀ᶠ X' in 𝓝 X, (X', z) ∈ U := by
    have : Continuous fun X' : Euc d => ((X', z) : Euc d × Euc d) := by fun_prop
    exact this.continuousAt.eventually (hU.mem_nhds hz)
  have hJJ' : (fun X' => iteratedFDeriv ℝ c (fun z' => G (X', z')) z) =ᶠ[𝓝 X]
      fun X' => Lc (K (X', z)) := by
    filter_upwards [hopen] with X' hX'
    ext v'
    rw [inner_jet hU c G hGc X' z hX' v']
    simp [Lc, hK]
  have hKι : ContDiffAt ℝ (a : WithTop ℕ∞) (fun X' : Euc d => K (X', z)) X :=
    (hKa.contDiffAt (hU.mem_nhds hz)).comp X (contDiffAt_id.prodMk contDiffAt_const)
  have hJ'd : ContDiffAt ℝ (a : WithTop ℕ∞) (fun X' : Euc d => Lc (K (X', z))) X :=
    Lc.contDiff.contDiffAt.comp X hKι
  have hJd : ContDiffAt ℝ (a : WithTop ℕ∞)
      (fun X' => iteratedFDeriv ℝ c (fun z' => G (X', z')) z) X := hJ'd.congr_of_eventuallyEq hJJ'
  unfold mixedDeriv
  -- evaluate at `v` through the continuous linear map `apply v`
  have hev := (ContinuousMultilinearMap.apply ℝ (fun _ : Fin c => Euc d) ℝ v).iteratedFDeriv_comp_left
    hJd (i := a) le_rfl
  have e1 : (iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ c (fun z' => G (X', z')) z) X u) v =
      iteratedFDeriv ℝ a (fun X' => iteratedFDeriv ℝ c (fun z' => G (X', z')) z v) X u := by
    have h1 := congrArg (fun L => L u) hev
    have h2 : (fun X' => iteratedFDeriv ℝ c (fun z' => G (X', z')) z v) =
        ⇑(ContinuousMultilinearMap.apply ℝ (fun _ : Fin c => Euc d) ℝ v) ∘
          (fun X' => iteratedFDeriv ℝ c (fun z' => G (X', z')) z) := rfl
    rw [h2]
    simpa using h1.symm
  rw [e1]
  have e2 : (fun X' => iteratedFDeriv ℝ c (fun z' => G (X', z')) z v) =ᶠ[𝓝 X]
      fun X' => (fun y => iteratedFDeriv ℝ c G y (fun j => ((0 : Euc d), v j))) (X', z) := by
    filter_upwards [hopen] with X' hX'
    exact inner_jet hU c G hGc X' z hX' v
  rw [(e2.iteratedFDeriv ℝ a).eq_of_nhds]
  have hg : ContDiffOn ℝ (a : WithTop ℕ∞)
      (fun y => iteratedFDeriv ℝ c G y (fun j => ((0 : Euc d), v j))) U :=
    (ContinuousLinearMap.contDiff (ContinuousMultilinearMap.apply ℝ (fun _ : Fin c => Euc d × Euc d) ℝ
      (fun j => ((0 : Euc d), v j)))).comp_contDiffOn hKa
  rw [outer_jet hU a _ hg X z hz u]
  have := iteratedFDeriv_apply_append hU a c G hG (X, z) hz (fun j => (u j, (0 : Euc d)))
    (fun j => ((0 : Euc d), v j))
  rw [this]
  rfl

end FactA4

section Rotate
variable {E F : Type*} [NormedAddCommGroup E] [NormedSpace ℝ E] [NormedAddCommGroup F]
  [NormedSpace ℝ F]

/-- Moving the last argument of the `(n+1)`-th derivative to the front. -/
theorem iteratedFDeriv_cons_eq_snoc {n : ℕ} {f : E → F} {x : E}
    (hf : ContDiffAt ℝ ((n + 1 : ℕ) : WithTop ℕ∞) f x) (h : E) (w : Fin n → E) :
    iteratedFDeriv ℝ (n + 1) f x (Fin.cons h w) = iteratedFDeriv ℝ (n + 1) f x (Fin.snoc w h) := by
  have := iteratedFDeriv_perm hf ((Fin.last n).cycleRange.symm) (Fin.snoc w h : Fin (n + 1) → E)
  rw [← this]
  congr 1
  funext j
  refine Fin.cases ?_ (fun k => ?_) j
  · simp only [Fin.cons_zero, Function.comp, Equiv.toFun_as_coe, Fin.cycleRange_symm_zero,
      Fin.snoc_last]
  · simp only [Fin.cons_succ, Function.comp, Equiv.toFun_as_coe, Fin.cycleRange_symm_succ,
      Fin.succAbove_last, Fin.snoc_castSucc]

theorem iteratedFDeriv_cast {n n' : ℕ} (h : n = n') (f : E → F) (x : E) (m : Fin n' → E) :
    iteratedFDeriv ℝ n f x (m ∘ Fin.cast h) = iteratedFDeriv ℝ n' f x m := by
  subst h; rfl

end Rotate

end HRS.Parx

end
