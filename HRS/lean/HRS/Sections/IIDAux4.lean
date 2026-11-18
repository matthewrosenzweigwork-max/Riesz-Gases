import HRS.Sections.IIDAux3

/-!
# IID helper chain, part 4: lattice boxes, tails (see the chain plan in `IIDAux1`).
-/

noncomputable section

open MeasureTheory ProbabilityTheory
open scoped ENNReal NNReal

namespace HRS.IID

section Lattice

variable {d : ℕ}

/-- Sup norm of an integer lattice point. -/
def supN (k : Lattice d) : ℕ := Finset.univ.sup fun i => (k i).natAbs

lemma natAbs_le_supN (k : Lattice d) (i : Fin d) : (k i).natAbs ≤ supN k :=
  Finset.le_sup (f := fun i => (k i).natAbs) (Finset.mem_univ i)

lemma supN_le_iff (k : Lattice d) (n : ℕ) : supN k ≤ n ↔ ∀ i, (k i).natAbs ≤ n := by
  unfold supN; exact Finset.sup_le_iff.trans (by simp)

lemma supN_eq_zero_iff (k : Lattice d) : supN k = 0 ↔ k = 0 := by
  rw [← Nat.le_zero, supN_le_iff]
  constructor
  · intro h; funext i; have := h i; simpa using this
  · intro h i; simp [h]

lemma exists_natAbs_eq_supN (k : Lattice d) (hk : k ≠ 0) : ∃ i, (k i).natAbs = supN k := by
  have hd : (Finset.univ : Finset (Fin d)).Nonempty := by
    by_contra h
    apply hk
    funext i
    exact absurd ⟨i, Finset.mem_univ i⟩ h
  obtain ⟨i, _, hi⟩ := Finset.exists_mem_eq_sup Finset.univ hd (fun i => (k i).natAbs)
  exact ⟨i, hi.symm⟩

/-- The box of nonzero lattice points of sup norm at most `L`. -/
def boxT (d L : ℕ) : Finset (NonzeroLattice d) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(L : ℤ)) L)).subtype (fun k => k ≠ 0)

lemma mem_boxT {L : ℕ} {k : NonzeroLattice d} : k ∈ boxT d L ↔ supN k.1 ≤ L := by
  unfold boxT
  rw [Finset.mem_subtype, Fintype.mem_piFinset, supN_le_iff]
  refine forall_congr' fun i => ?_
  rw [Finset.mem_Icc]
  omega

lemma card_boxT_le (L : ℕ) : (boxT d L).card ≤ (2 * L + 1) ^ d := by
  unfold boxT
  rw [Finset.card_subtype]
  refine (Finset.card_filter_le _ _).trans ?_
  rw [Fintype.card_piFinset]
  simp only [Int.card_Icc, Finset.prod_const, Finset.card_univ, Fintype.card_fin]
  have : ((L : ℤ) + 1 - -(L : ℤ)).toNat = 2 * L + 1 := by omega
  rw [this]

/-- Lattice points of sup norm exactly `n`. -/
def shellF (d n : ℕ) : Finset (Lattice d) :=
  (Fintype.piFinset (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n)).filter (fun k => supN k = n)

lemma card_piFinset_update (n : ℕ) (i : Fin d) (s : ℤ) :
    (Fintype.piFinset (Function.update (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n) i {s})).card =
      (2 * n + 1) ^ (d - 1) := by
  rw [Fintype.card_piFinset]
  have e : ∀ j, (Function.update (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n) i {s} j).card =
      Function.update (fun _ : Fin d => 2 * n + 1) i 1 j := by
    intro j
    by_cases h : j = i
    · subst h; simp
    · simp only [Function.update_of_ne h, Int.card_Icc]; omega
  simp_rw [e]
  rw [Finset.prod_update_of_mem (Finset.mem_univ i)]
  simp [Finset.prod_const, Finset.card_sdiff]

lemma card_shellF_le {n : ℕ} (hn : 1 ≤ n) : (shellF d n).card ≤ 2 * d * (2 * n + 1) ^ (d - 1) := by
  have hsub : shellF d n ⊆ Finset.univ.biUnion (fun i : Fin d => ({(n : ℤ), -(n : ℤ)} : Finset ℤ).biUnion
      (fun s => Fintype.piFinset (Function.update (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n) i {s}))) := by
    intro k hk
    unfold shellF at hk
    rw [Finset.mem_filter, Fintype.mem_piFinset] at hk
    obtain ⟨hbox, hsn⟩ := hk
    have hk0 : k ≠ 0 := by
      intro h
      have := (supN_eq_zero_iff k).2 h
      omega
    obtain ⟨i, hi⟩ := exists_natAbs_eq_supN k hk0
    rw [hsn] at hi
    simp only [Finset.mem_biUnion, Finset.mem_univ, true_and]
    refine ⟨i, k i, ?_, ?_⟩
    · simp only [Finset.mem_insert, Finset.mem_singleton]; omega
    · rw [Fintype.mem_piFinset]
      intro j
      by_cases h : j = i
      · subst h; simp
      · simp only [Function.update_of_ne h]; exact hbox j
  refine (Finset.card_le_card hsub).trans ?_
  refine Finset.card_biUnion_le.trans ?_
  have : ∀ i : Fin d, (({(n : ℤ), -(n : ℤ)} : Finset ℤ).biUnion
      (fun s => Fintype.piFinset (Function.update (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n) i {s}))).card
      ≤ 2 * (2 * n + 1) ^ (d - 1) := fun i => by
    refine Finset.card_biUnion_le.trans ?_
    calc ∑ s ∈ ({(n : ℤ), -(n : ℤ)} : Finset ℤ),
          (Fintype.piFinset (Function.update (fun _ : Fin d => Finset.Icc (-(n : ℤ)) n) i {s})).card
        = ∑ s ∈ ({(n : ℤ), -(n : ℤ)} : Finset ℤ), (2 * n + 1) ^ (d - 1) :=
          Finset.sum_congr rfl fun s _ => card_piFinset_update n i s
      _ ≤ 2 * (2 * n + 1) ^ (d - 1) := by
          rw [Finset.sum_const]
          simp only [smul_eq_mul]
          exact Nat.mul_le_mul_right _ (Finset.card_le_two)
  calc _ ≤ ∑ i : Fin d, 2 * (2 * n + 1) ^ (d - 1) := Finset.sum_le_sum fun i _ => this i
    _ = 2 * d * (2 * n + 1) ^ (d - 1) := by simp [Finset.sum_const]; ring

lemma abs_le_jp (k : Lattice d) (i : Fin d) : |(k i : ℝ)| ≤ Lattice.jp k := by
  have h1 : |(k i : ℝ)| ≤ Lattice.enorm k := by
    unfold Lattice.enorm Lattice.toEuc
    have := PiLp.norm_apply_le (WithLp.toLp 2 fun i => (k i : ℝ) : Euc d) i
    simpa [Real.norm_eq_abs] using this
  have h2 : Lattice.enorm k ≤ Lattice.jp k := by
    unfold Lattice.jp
    refine Real.le_sqrt_of_sq_le ?_
    have : (1 : ℝ) ≤ 4 * Real.pi ^ 2 := by nlinarith [Real.pi_gt_three]
    nlinarith [sq_nonneg (Lattice.enorm k)]
  exact h1.trans h2

lemma supN_le_jp (k : Lattice d) : (supN k : ℝ) ≤ Lattice.jp k := by
  by_cases hk : k = 0
  · subst hk
    rw [(supN_eq_zero_iff (0 : Lattice d)).2 rfl, Nat.cast_zero]
    exact (Torus.jp_pos _).le
  · obtain ⟨i, hi⟩ := exists_natAbs_eq_supN k hk
    rw [← hi]
    have := abs_le_jp k i
    have e : ((k i).natAbs : ℝ) = |(k i : ℝ)| := by
      rw [Nat.cast_natAbs, Int.cast_abs]
    rw [e]; exact this

lemma pseries_tail_le {s : ℝ} (hs : 1 < s) {L : ℕ} (hL : 1 ≤ L) (M : ℕ) :
    ∑ n ∈ Finset.Ico (L + 1) (M + 1), (n : ℝ) ^ (-s) ≤ (L : ℝ) ^ (1 - s) / (s - 1) := by
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  rcases Nat.lt_or_ge M L with hlt | hge
  · rw [Finset.Ico_eq_empty (by omega)]
    simp only [Finset.sum_empty]
    positivity
  set a : ℕ := M - L with ha
  have hsum : ∑ n ∈ Finset.Ico (L + 1) (M + 1), (n : ℝ) ^ (-s) =
      ∑ i ∈ Finset.range a, ((L : ℝ) + ((i + 1 : ℕ) : ℝ)) ^ (-s) := by
    rw [Finset.sum_Ico_eq_sum_range]
    have : M + 1 - (L + 1) = a := by omega
    rw [this]
    refine Finset.sum_congr rfl fun i _ => ?_
    push_cast; ring_nf
  rw [hsum]
  have hanti : AntitoneOn (fun x : ℝ => x ^ (-s)) (Set.Icc (L : ℝ) ((L : ℝ) + a)) := by
    intro x hx y hy hxy
    exact Real.rpow_le_rpow_of_nonpos (by linarith [hx.1]) hxy (by linarith)
  have h1 := hanti.sum_le_integral
  have hint : ∫ x in (L : ℝ)..(L : ℝ) + a, x ^ (-s) =
      (((L : ℝ) + a) ^ (-s + 1) - (L : ℝ) ^ (-s + 1)) / (-s + 1) := by
    refine integral_rpow (Or.inr ⟨by linarith, ?_⟩)
    rw [Set.uIcc_of_le (by linarith [(Nat.cast_nonneg a : (0 : ℝ) ≤ a)])]
    intro h0
    linarith [h0.1]
  refine h1.trans ?_
  rw [hint]
  have hpos : 0 ≤ ((L : ℝ) + a) ^ (-s + 1) := Real.rpow_nonneg (by positivity) _
  have e : (((L : ℝ) + a) ^ (-s + 1) - (L : ℝ) ^ (-s + 1)) / (-s + 1) =
      ((L : ℝ) ^ (-s + 1) - ((L : ℝ) + a) ^ (-s + 1)) / (s - 1) := by
    have : -s + 1 = -(s - 1) := by ring
    rw [this, div_neg, ← neg_div, neg_sub]
  rw [e, show 1 - s = -s + 1 by ring]
  gcongr
  linarith

theorem tail_boxT_le {m : ℝ} (hm : (d : ℝ) < 2 * m) :
    ∃ C : ℝ, 0 ≤ C ∧ ∀ L : ℕ, 1 ≤ L →
      ∑' k : NonzeroLattice d, (if k ∈ boxT d L then 0 else Lattice.jp k.1 ^ (-(2 * m))) ≤
        C * (L : ℝ) ^ ((d : ℝ) - 2 * m) := by
  have hd0 : (0 : ℝ) ≤ d := Nat.cast_nonneg d
  have ha : (d : ℝ) < 2 * m := hm
  refine ⟨2 * d * 3 ^ (d - 1) / (2 * m - d), by
    have : 0 < 2 * m - (d : ℝ) := by linarith
    positivity, fun L hL => ?_⟩
  have hLpos : (0 : ℝ) < L := by exact_mod_cast hL
  rcases Nat.eq_zero_or_pos d with rfl | hdpos
  · -- no nonzero lattice points
    have : IsEmpty (NonzeroLattice 0) := ⟨fun k => k.2 (funext fun i => i.elim0)⟩
    simp [tsum_empty]
  obtain ⟨e, rfl⟩ : ∃ e, d = e + 1 := ⟨d - 1, by omega⟩
  simp only [Nat.add_sub_cancel]
  have hden : 0 < 2 * m - ((e + 1 : ℕ) : ℝ) := by linarith
  refine tsum_le_of_sum_le' (by positivity) fun F => ?_
  set a : ℝ := 2 * m with hadef
  set f : NonzeroLattice (e + 1) → ℝ := fun k =>
    if k ∈ boxT (e + 1) L then 0 else Lattice.jp k.1 ^ (-a) with hf
  set S : Finset (NonzeroLattice (e + 1)) := F.filter (fun k => k ∉ boxT (e + 1) L) with hS
  have h1 : ∑ k ∈ F, f k = ∑ k ∈ S, Lattice.jp k.1 ^ (-a) := by
    rw [hS, Finset.sum_filter]
    refine Finset.sum_congr rfl fun k _ => ?_
    by_cases h : k ∈ boxT (e + 1) L <;> simp [hf, h]
  rw [h1]
  set M : ℕ := F.sup (fun k => supN k.1) with hM
  have hmaps : ∀ k ∈ S, supN k.1 ∈ Finset.Ico (L + 1) (M + 1) := by
    intro k hk
    rw [hS, Finset.mem_filter] at hk
    rw [Finset.mem_Ico]
    have h1 : ¬ supN k.1 ≤ L := fun h => hk.2 (mem_boxT.2 h)
    have h2 : supN k.1 ≤ M := Finset.le_sup (f := fun k : NonzeroLattice (e + 1) => supN k.1) hk.1
    omega
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  have hterm : ∀ n ∈ Finset.Ico (L + 1) (M + 1),
      ∑ k ∈ S with supN k.1 = n, Lattice.jp k.1 ^ (-a) ≤
        2 * ((e + 1 : ℕ) : ℝ) * 3 ^ e * (n : ℝ) ^ (-(a - e)) := by
    intro n hn
    have hn1 : 1 ≤ n := by rw [Finset.mem_Ico] at hn; omega
    have hnpos : (0 : ℝ) < n := by exact_mod_cast hn1
    have h1 : ∀ k ∈ S.filter (fun k => supN k.1 = n), Lattice.jp k.1 ^ (-a) ≤ (n : ℝ) ^ (-a) := by
      intro k hk
      rw [Finset.mem_filter] at hk
      have : (n : ℝ) ≤ Lattice.jp k.1 := by rw [← hk.2]; exact supN_le_jp k.1
      exact Real.rpow_le_rpow_of_nonpos hnpos this (by linarith)
    have hcard : (S.filter (fun k => supN k.1 = n)).card ≤ (shellF (e + 1) n).card := by
      refine Finset.card_le_card_of_injOn (fun k => k.1) (fun k hk => ?_) (fun k _ k' _ h => Subtype.ext h)
      rw [Finset.mem_coe, Finset.mem_filter] at hk
      have hs := hk.2
      unfold shellF
      rw [Finset.mem_coe, Finset.mem_filter, Fintype.mem_piFinset]
      refine ⟨fun i => ?_, hs⟩
      have := (supN_le_iff k.1 n).1 hs.le i
      rw [Finset.mem_Icc]
      beta_reduce
      omega
    have hc2 := card_shellF_le (d := e + 1) hn1
    calc ∑ k ∈ S with supN k.1 = n, Lattice.jp k.1 ^ (-a)
        ≤ ∑ k ∈ S.filter (fun k => supN k.1 = n), (n : ℝ) ^ (-a) := Finset.sum_le_sum h1
      _ = ((S.filter (fun k => supN k.1 = n)).card : ℝ) * (n : ℝ) ^ (-a) := by
          rw [Finset.sum_const, nsmul_eq_mul]
      _ ≤ ((2 * (e + 1) * (2 * n + 1) ^ e : ℕ) : ℝ) * (n : ℝ) ^ (-a) := by
          gcongr
          exact_mod_cast hcard.trans (by simpa using hc2)
      _ ≤ (2 * ((e + 1 : ℕ) : ℝ) * 3 ^ e * (n : ℝ) ^ e) * (n : ℝ) ^ (-a) := by
          gcongr
          push_cast
          have : (2 * (n : ℝ) + 1) ^ e ≤ (3 * (n : ℝ)) ^ e := by
            gcongr
            have : (1 : ℝ) ≤ n := by exact_mod_cast hn1
            linarith
          calc 2 * ((e : ℝ) + 1) * (2 * (n : ℝ) + 1) ^ e ≤ 2 * ((e : ℝ) + 1) * (3 * (n : ℝ)) ^ e := by gcongr
            _ = 2 * ((e : ℝ) + 1) * 3 ^ e * (n : ℝ) ^ e := by rw [mul_pow]; ring
      _ = 2 * ((e + 1 : ℕ) : ℝ) * 3 ^ e * (n : ℝ) ^ (-(a - e)) := by
          have h5 : (n : ℝ) ^ e = (n : ℝ) ^ ((e : ℕ) : ℝ) := (Real.rpow_natCast _ _).symm
          rw [mul_assoc (2 * ((e + 1 : ℕ) : ℝ) * 3 ^ e), h5, ← Real.rpow_add hnpos]
          congr 3; ring
  have hsum := Finset.sum_le_sum hterm
  refine hsum.trans ?_
  rw [← Finset.mul_sum]
  have hp := pseries_tail_le (s := a - e) (by simp only [hadef]; push_cast at hden; linarith) hL M
  have hden' : 0 < a - e - 1 := by simp only [hadef]; push_cast at hden; linarith
  calc 2 * ((e + 1 : ℕ) : ℝ) * 3 ^ e * ∑ n ∈ Finset.Ico (L + 1) (M + 1), (n : ℝ) ^ (-(a - e))
      ≤ 2 * ((e + 1 : ℕ) : ℝ) * 3 ^ e * ((L : ℝ) ^ (1 - (a - e)) / (a - e - 1)) := by gcongr
    _ = 2 * ((e + 1 : ℕ) : ℝ) * 3 ^ e / (2 * m - ((e + 1 : ℕ) : ℝ)) * (L : ℝ) ^ (((e + 1 : ℕ) : ℝ) - 2 * m) := by
        have e1 : (1 : ℝ) - (a - e) = ((e + 1 : ℕ) : ℝ) - 2 * m := by simp only [hadef]; push_cast; ring
        have e2 : a - e - 1 = 2 * m - ((e + 1 : ℕ) : ℝ) := by simp only [hadef]; push_cast; ring
        rw [e1, e2]; ring

end Lattice

section Embed

variable {d : ℕ}

open HRS.InitialDataAux

lemma kOf_mem (T : Finset (NonzeroLattice d)) (j : Fin T.card) : kOf T j ∈ T :=
  ((T.equivFin).symm j).2

lemma kOf_injective (T : Finset (NonzeroLattice d)) : Function.Injective (kOf T) := fun j j' h =>
  (T.equivFin).symm.injective (Subtype.ext h)

lemma exists_kOf (T : Finset (NonzeroLattice d)) {k : NonzeroLattice d} (hk : k ∈ T) :
    ∃ j, kOf T j = k := ⟨T.equivFin ⟨k, hk⟩, by simp [kOf]⟩

/-- The coordinate vector of `F ∈ E_m` on the modes of `T`. -/
def coordVec {m : ℝ} (T : Finset (NonzeroLattice d)) (F : NegSobolev d m) :
    EuclideanSpace ℝ (Fin T.card) :=
  WithLp.toLp 2 fun j : Fin T.card => NegSobolev.coord F (kOf T j)

/-- The isometric embedding `ℝ^T → E_m`. -/
def embedT (m : ℝ) (T : Finset (NonzeroLattice d)) :
    EuclideanSpace ℝ (Fin T.card) →L[ℝ] NegSobolev d m :=
  LinearMap.toContinuousLinearMap
    { toFun := fun v =>
        (∑ j : Fin T.card, lp.single 2 (kOf T j) (v j) : lp (fun _ : NonzeroLattice d => ℝ) 2)
      map_add' := fun v w => by
        show (∑ j : Fin T.card, lp.single 2 (kOf T j) ((v + w) j) : lp (fun _ : NonzeroLattice d => ℝ) 2) =
          (∑ j : Fin T.card, lp.single 2 (kOf T j) (v j) : lp (fun _ : NonzeroLattice d => ℝ) 2) +
          (∑ j : Fin T.card, lp.single 2 (kOf T j) (w j) : lp (fun _ : NonzeroLattice d => ℝ) 2)
        rw [← Finset.sum_add_distrib]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← lp.single_add]; rfl
      map_smul' := fun c v => by
        show (∑ j : Fin T.card, lp.single 2 (kOf T j) ((c • v) j) : lp (fun _ : NonzeroLattice d => ℝ) 2) =
          c • (∑ j : Fin T.card, lp.single 2 (kOf T j) (v j) : lp (fun _ : NonzeroLattice d => ℝ) 2)
        rw [Finset.smul_sum]
        refine Finset.sum_congr rfl fun j _ => ?_
        rw [← lp.single_smul]; rfl }

lemma coord_embedT (m : ℝ) (T : Finset (NonzeroLattice d)) (v : EuclideanSpace ℝ (Fin T.card))
    (k : NonzeroLattice d) :
    NegSobolev.coord (embedT m T v) k =
      ∑ j : Fin T.card, if k = kOf T j then v j else 0 := by
  show ((∑ j : Fin T.card, lp.single 2 (kOf T j) (v j) : lp (fun _ : NonzeroLattice d => ℝ) 2) :
    NonzeroLattice d → ℝ) k = _
  simp only [lp.coeFn_sum, Finset.sum_apply, lp.single_apply, Pi.single_apply]

lemma coord_embedT_kOf (m : ℝ) (T : Finset (NonzeroLattice d)) (v : EuclideanSpace ℝ (Fin T.card))
    (j : Fin T.card) : NegSobolev.coord (embedT m T v) (kOf T j) = v j := by
  rw [coord_embedT]
  rw [Finset.sum_eq_single j]
  · simp
  · intro j' _ hj'
    have : kOf T j ≠ kOf T j' := fun h => hj' (kOf_injective T h).symm
    simp [this]
  · simp

lemma coord_embedT_notMem (m : ℝ) (T : Finset (NonzeroLattice d)) (v : EuclideanSpace ℝ (Fin T.card))
    {k : NonzeroLattice d} (hk : k ∉ T) : NegSobolev.coord (embedT m T v) k = 0 := by
  rw [coord_embedT]
  refine Finset.sum_eq_zero fun j _ => ?_
  have : k ≠ kOf T j := fun h => hk (h ▸ kOf_mem T j)
  simp [this]

lemma projT_eq_embedT {m : ℝ} (T : Finset (NonzeroLattice d)) (F : NegSobolev d m) :
    projT T F = embedT m T (coordVec T F) := by
  refine Subtype.ext (funext fun k => ?_)
  show NegSobolev.coord (projT T F) k = NegSobolev.coord (embedT m T (coordVec T F)) k
  rw [coord_projT]
  by_cases hk : k ∈ T
  · obtain ⟨j, rfl⟩ := exists_kOf T hk
    rw [coord_embedT_kOf, if_pos hk]; rfl
  · rw [coord_embedT_notMem m T _ hk, if_neg hk]

lemma norm_embedT {m : ℝ} (T : Finset (NonzeroLattice d)) (v : EuclideanSpace ℝ (Fin T.card)) :
    ‖embedT m T v‖ = ‖v‖ := by
  have h1 : ‖embedT m T v‖ ^ 2 = ∑ k ∈ T, NegSobolev.coord (embedT m T v) k ^ 2 := by
    rw [norm_sq_eq_tsum, tsum_eq_sum (s := T)]
    intro k hk
    rw [coord_embedT_notMem m T v hk]; simp
  have h2 : ∑ k ∈ T, NegSobolev.coord (embedT m T v) k ^ 2 = ‖v‖ ^ 2 := by
    rw [← sum_kOf T (fun k => NegSobolev.coord (embedT m T v) k ^ 2), EuclideanSpace.norm_eq,
      Real.sq_sqrt (Finset.sum_nonneg fun j _ => by positivity)]
    refine Finset.sum_congr rfl fun j _ => ?_
    rw [coord_embedT_kOf, Real.norm_eq_abs, sq_abs]
  exact (sq_eq_sq₀ (norm_nonneg _) (norm_nonneg _)).1 (h1.trans h2)

lemma embedT_opNorm_le (m : ℝ) (T : Finset (NonzeroLattice d)) : ‖embedT m T‖ ≤ 1 :=
  ContinuousLinearMap.opNorm_le_bound _ zero_le_one fun v => by rw [norm_embedT]; simp

lemma embed_comp_bounds {m : ℝ} (T : Finset (NonzeroLattice d)) {Φ : NegSobolev d m → ℝ}
    (hΦ : Φ ∈ CbUnitBall (NegSobolev d m) 2) :
    ContDiff ℝ 2 (fun v => Φ (embedT m T v)) ∧ (∀ z, |Φ (embedT m T z)| ≤ 1) ∧
      (∀ z, ‖fderiv ℝ (fun v => Φ (embedT m T v)) z‖ ≤ 1) ∧
      (∀ z, ‖iteratedFDeriv ℝ 2 (fun v => Φ (embedT m T v)) z‖ ≤ 1) := by
  have hcd : ContDiff ℝ 2 (fun v => Φ (embedT m T v)) := hΦ.1.comp_continuousLinearMap (g := embedT m T)
  have hit : ∀ j : ℕ, j ≤ 2 → ∀ z, ‖iteratedFDeriv ℝ j (fun v => Φ (embedT m T v)) z‖ ≤ 1 := by
    intro j hj z
    have := (embedT m T).iteratedFDeriv_comp_right (f := Φ) (n := 2) hΦ.1 z (i := j) (by exact_mod_cast hj)
    have e : (fun v => Φ (embedT m T v)) = Φ ∘ (embedT m T) := rfl
    rw [e, this]
    refine (ContinuousMultilinearMap.norm_compContinuousLinearMap_le _ _).trans ?_
    have h1 := iteratedFDeriv_norm_le_of_mem hΦ hj (embedT m T z)
    have h2 : ∏ _i : Fin j, ‖embedT m T‖ ≤ 1 := by
      rw [Finset.prod_const]
      exact pow_le_one₀ (norm_nonneg _) (embedT_opNorm_le m T)
    calc _ ≤ 1 * 1 := mul_le_mul h1 h2 (Finset.prod_nonneg fun _ _ => norm_nonneg _) zero_le_one
      _ = 1 := by norm_num
  refine ⟨hcd, fun z => ?_, fun z => ?_, hit 2 le_rfl⟩
  · have := hit 0 (by norm_num) z
    simpa [norm_iteratedFDeriv_zero] using this
  · have := hit 1 (by norm_num) z
    simpa [norm_iteratedFDeriv_one] using this

end Embed

section Whiten

open scoped Matrix MatrixOrder

theorem exists_whiten {p : ℕ} (S : Matrix (Fin p) (Fin p) ℝ) (hS : S.PosSemidef)
    (hpos : ∀ w : EuclideanSpace ℝ (Fin p), w ≠ 0 → 0 < w ⬝ᵥ S *ᵥ w) :
    ∃ B binv : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p),
      (∀ x y, inner ℝ (B x) y = inner ℝ x (B y)) ∧ (∀ y, B (binv y) = y) ∧
      (∀ y, binv (B y) = y) ∧
      (∀ w w', inner ℝ (B w) (B w') = w ⬝ᵥ S *ᵥ w') ∧
      nuS B 1 = multivariateGaussian (0 : EuclideanSpace ℝ (Fin p)) S := by
  set A : Matrix (Fin p) (Fin p) ℝ := CFC.sqrt S with hA
  have hAA : A * A = S := CFC.sqrt_mul_sqrt_self S hS.nonneg
  have hAsa : IsSelfAdjoint A := (CFC.sqrt_nonneg S).isSelfAdjoint
  set B : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p) :=
    Matrix.toEuclideanCLM (𝕜 := ℝ) A with hB
  have hBsa : IsSelfAdjoint B := hAsa.map _
  have hBs : ∀ x y, inner ℝ (B x) y = inner ℝ x (B y) := fun x y => by
    have := ContinuousLinearMap.isSelfAdjoint_iff_isSymmetric.1 hBsa
    exact this x y
  have hBB : ∀ w w', inner ℝ (B w) (B w') = w ⬝ᵥ S *ᵥ w' := fun w w' => by
    rw [hBs, ← ContinuousLinearMap.mul_apply, hB, ← map_mul, hAA, Matrix.inner_toEuclideanCLM]
  have hinj : Function.Injective B := by
    refine (injective_iff_map_eq_zero B).2 fun w hw => ?_
    by_contra hne
    have h1 := hpos w hne
    have h2 : inner ℝ (B w) (B w) = 0 := by
      have : B w = 0 := hw
      rw [this]; simp
    rw [hBB] at h2
    linarith
  have hinjL : Function.Injective (B : EuclideanSpace ℝ (Fin p) →ₗ[ℝ] EuclideanSpace ℝ (Fin p)) := hinj
  have hsurj : Function.Surjective B := LinearMap.injective_iff_surjective.1 hinjL
  let e : EuclideanSpace ℝ (Fin p) ≃L[ℝ] EuclideanSpace ℝ (Fin p) :=
    ContinuousLinearEquiv.ofBijective B (LinearMap.ker_eq_bot.2 hinj) (LinearMap.range_eq_top.2 hsurj)
  refine ⟨B, (e.symm : EuclideanSpace ℝ (Fin p) →L[ℝ] EuclideanSpace ℝ (Fin p)), hBs, ?_, ?_, hBB, ?_⟩
  · intro y
    have := e.apply_symm_apply y
    simpa [e] using this
  · intro y
    have := e.symm_apply_apply y
    simpa [e] using this
  · unfold nuS
    simp only [one_smul]
    rw [multivariateGaussian]
    show (stdGaussian (EuclideanSpace ℝ (Fin p))).map ⇑B = _
    simp [hB, hA]

end Whiten

section Cov

open scoped Matrix
open HRS.InitialDataAux

variable {d : ℕ}

lemma withDensityReal_ge_smul {q : Torus d → ℝ} {c₀ : ℝ} (hqc : ∀ x, c₀ ≤ q x) :
    ENNReal.ofReal c₀ • (volume : Measure (Torus d)) ≤ withDensityReal q := by
  unfold withDensityReal
  rw [← withDensity_const]
  exact withDensity_mono (Filter.Eventually.of_forall fun x => ENNReal.ofReal_le_ofReal (hqc x))

lemma quad_momentMatrix {p : ℕ} (ρ : Measure (EuclideanSpace ℝ (Fin p)))
    (h2 : Integrable (fun x : EuclideanSpace ℝ (Fin p) => ‖x‖ ^ 2) ρ) (v : Fin p → ℝ) :
    v ⬝ᵥ (Yurinskii.momentMatrix ρ *ᵥ v) = ∫ x, (∑ c, v c * x c) ^ 2 ∂ρ := by
  have hI := Yurinskii.integrable_coord_mul h2
  have e : ∀ x : EuclideanSpace ℝ (Fin p), (∑ c, v c * x c) ^ 2 = ∑ c, ∑ d, (v c * v d) * (x c * x d) :=
    fun x => by
      rw [sq, Finset.sum_mul_sum]
      refine Finset.sum_congr rfl fun c _ => Finset.sum_congr rfl fun d _ => by ring
  simp_rw [e]
  rw [integral_finsetSum _ fun c _ => integrable_finsetSum _ fun d _ => (hI c d).const_mul _]
  simp only [dotProduct, Matrix.mulVec, Yurinskii.momentMatrix, Matrix.of_apply, Finset.mul_sum]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [integral_finsetSum _ fun d _ => (hI c d).const_mul _]
  refine Finset.sum_congr rfl fun d _ => ?_
  rw [integral_const_mul]; ring

/-- Coefficients of the trigonometric polynomial `∑_c w_c ⟨k_c⟩^{-m} e_{k_c}`. -/
def coefW (m : ℝ) (T : Finset (NonzeroLattice d)) (w : EuclideanSpace ℝ (Fin T.card))
    (k : NonzeroLattice d) : ℝ :=
  if h : k ∈ T then w (T.equivFin ⟨k, h⟩) * Lattice.jp k.1 ^ (-m) else 0

lemma coefW_kOf (m : ℝ) (T : Finset (NonzeroLattice d)) (w : EuclideanSpace ℝ (Fin T.card))
    (c : Fin T.card) : coefW m T w (kOf T c) = w c * Lattice.jp (kOf T c).1 ^ (-m) := by
  unfold coefW
  rw [dif_pos (kOf_mem T c)]
  have : T.equivFin ⟨kOf T c, kOf_mem T c⟩ = c := by
    have : (⟨kOf T c, kOf_mem T c⟩ : T) = (T.equivFin).symm c := Subtype.ext rfl
    rw [this]; simp
  rw [this]

lemma sum_scMode_eq_trigPoly (m : ℝ) (T : Finset (NonzeroLattice d)) (w : EuclideanSpace ℝ (Fin T.card))
    (x : Torus d) :
    ∑ c, w c * scMode m (kOf T c) x = trigPoly T (coefW m T w) x := by
  unfold trigPoly
  rw [← sum_kOf T (fun k => coefW m T w k * Torus.realMode k x)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [coefW_kOf]
  unfold scMode
  ring

lemma sum_coefW_sq (m : ℝ) (T : Finset (NonzeroLattice d)) (w : EuclideanSpace ℝ (Fin T.card)) :
    ∑ k ∈ T, coefW m T w k ^ 2 = ∑ c, (w c * Lattice.jp (kOf T c).1 ^ (-m)) ^ 2 := by
  rw [← sum_kOf T (fun k => coefW m T w k ^ 2)]
  refine Finset.sum_congr rfl fun c _ => ?_
  rw [coefW_kOf]

lemma sum_coefW_sq_pos (m : ℝ) (T : Finset (NonzeroLattice d)) {w : EuclideanSpace ℝ (Fin T.card)}
    (hw : w ≠ 0) : 0 < ∑ k ∈ T, coefW m T w k ^ 2 := by
  rw [sum_coefW_sq]
  obtain ⟨c, hc⟩ : ∃ c, w c ≠ 0 := by
    by_contra h
    push Not at h
    exact hw (by ext c; simpa using h c)
  refine lt_of_lt_of_le ?_ (Finset.single_le_sum (f := fun c => (w c * Lattice.jp (kOf T c).1 ^ (-m)) ^ 2)
    (fun c _ => sq_nonneg _) (Finset.mem_univ c))
  have : w c * Lattice.jp (kOf T c).1 ^ (-m) ≠ 0 :=
    mul_ne_zero hc (Real.rpow_pos_of_pos (Torus.jp_pos _) _).ne'
  positivity

lemma integral_trigPoly_zero (m : ℝ) (T : Finset (NonzeroLattice d)) (w : EuclideanSpace ℝ (Fin T.card)) :
    ∫ x, trigPoly T (coefW m T w) x = 0 := by
  unfold trigPoly
  rw [integral_finsetSum _ fun k _ => ((continuous_realMode k).const_mul _).integrable_of_hasCompactSupport
    (HasCompactSupport.of_compactSpace _)]
  refine Finset.sum_eq_zero fun k _ => ?_
  rw [integral_const_mul, Torus.integral_realMode, mul_zero]

theorem Sigma_quad_pos {m : ℝ} {q : Torus d → ℝ} (hq : IsProbDensity q) {c₀ : ℝ} (hc₀ : 0 < c₀)
    (hqc : ∀ x, c₀ ≤ q x) (T : Finset (NonzeroLattice d)) {N : ℕ} (hN : 1 ≤ N)
    {w : EuclideanSpace ℝ (Fin T.card)} (hw : w ≠ 0) :
    0 < w.ofLp ⬝ᵥ (∑ _i : Fin N, Yurinskii.momentMatrix
      ((withDensityReal q).map (xiVec (withDensityReal q) N (blk m T)))) *ᵥ w.ofLp := by
  set μ := withDensityReal q with hμ
  haveI : IsProbabilityMeasure μ := isProb_withDensityReal hq
  have hNpos : (0 : ℝ) < N := by exact_mod_cast hN
  set f := blk m T with hf
  have hfc : ∀ a, Continuous (f a) := fun a => continuous_scMode m _
  set ξ := xiVec μ N f with hξ
  have hξc : Continuous ξ := continuous_xiVec μ N f hfc
  set ρ0 := μ.map ξ with hρ0
  set S : ℝ := ∑ k ∈ T, Lattice.jp k.1 ^ (-(2 * m)) with hS
  have hb : ∀ x, ‖ξ x‖ ^ 2 ≤ 8 * S / N := fun x => norm_xiBlk_sq_le hN T x S le_rfl
  have h2 : Integrable (fun y : EuclideanSpace ℝ (Fin T.card) => ‖y‖ ^ 2) ρ0 := by
    rw [hρ0, integrable_map_measure (by fun_prop) hξc.aemeasurable]
    refine Integrable.of_bound ((by fun_prop : Continuous fun x => ‖ξ x‖ ^ 2).aestronglyMeasurable) (8 * S / N)
      (Filter.Eventually.of_forall fun x => ?_)
    simp only [Function.comp, Real.norm_eq_abs, abs_of_nonneg (by positivity : 0 ≤ ‖ξ x‖ ^ 2)]
    exact hb x
  have hsum : ∑ _i : Fin N, Yurinskii.momentMatrix ρ0 = (N : ℝ) • Yurinskii.momentMatrix ρ0 := by
    rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin, ← Nat.cast_smul_eq_nsmul ℝ]
  rw [hsum, Matrix.smul_mulVec, dotProduct_smul, smul_eq_mul, quad_momentMatrix ρ0 h2,
    hρ0, integral_map hξc.aemeasurable (by fun_prop)]
  set gm : ℝ := ∑ c, w c * pair μ (f c) with hgm
  set g : Torus d → ℝ := trigPoly T (coefW m T w) with hg
  have hgc : Continuous g := continuous_trigPoly _ _
  have e : ∀ x, (∑ c, w c * ξ x c) ^ 2 = (N : ℝ)⁻¹ * (g x - gm) ^ 2 := by
    intro x
    have h1 : ∑ c, w c * ξ x c = (Real.sqrt N)⁻¹ * (g x - gm) := by
      have : g x = ∑ c, w c * f c x := (sum_scMode_eq_trigPoly m T w x).symm
      rw [this, hgm, ← Finset.sum_sub_distrib, Finset.mul_sum]
      refine Finset.sum_congr rfl fun c _ => ?_
      simp only [hξ, xiVec_apply]; ring
    rw [h1, mul_pow, inv_pow, Real.sq_sqrt hNpos.le]
  simp_rw [e]
  rw [integral_const_mul, ← mul_assoc, mul_inv_cancel₀ hNpos.ne', one_mul]
  -- lower bound by Lebesgue measure
  have hle := withDensityReal_ge_smul hqc
  have hint : Integrable (fun x => (g x - gm) ^ 2) μ :=
    integrable_contA μ ((hgc.sub continuous_const).pow 2)
  have hmono := integral_mono_measure hle (Filter.Eventually.of_forall fun x => sq_nonneg (g x - gm)) hint
  rw [integral_smul_measure, ENNReal.toReal_ofReal hc₀.le, smul_eq_mul] at hmono
  have hvol : ∫ x, (g x - gm) ^ 2 = (∑ k ∈ T, coefW m T w k ^ 2) + gm ^ 2 := by
    have e2 : ∀ x : Torus d, (g x - gm) ^ 2 = g x ^ 2 - 2 * gm * g x + gm ^ 2 := fun x => by ring
    simp_rw [e2]
    have ig : Integrable g := (hgc).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have ig2 : Integrable (fun x => g x ^ 2) :=
      (hgc.pow 2).integrable_of_hasCompactSupport (HasCompactSupport.of_compactSpace _)
    have i3 : Integrable (fun x => g x ^ 2 - 2 * gm * g x) := ig2.sub (ig.const_mul _)
    rw [integral_add i3 (integrable_const _), integral_sub ig2 (ig.const_mul _), integral_const_mul,
      integral_trigPoly_zero, integral_trigPoly_sq]
    simp
  rw [hvol] at hmono
  have hpos := sum_coefW_sq_pos m T hw
  have : 0 < c₀ * ((∑ k ∈ T, coefW m T w k ^ 2) + gm ^ 2) := by positivity
  linarith

end Cov

end HRS.IID
