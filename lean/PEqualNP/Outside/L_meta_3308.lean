import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds

namespace PEqualNP.Outside.L_meta_3308

-- Wires of a gate list on an input, as in Circuit.wires.
def W {n : ℕ} (gs : List Gate) (x : Fin n → Bool) : List Bool :=
  gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) (List.ofFn x)

theorem W_snoc {n : ℕ} (gs : List Gate) (g : Gate) (x : Fin n → Bool) :
    W (gs ++ [g]) x = W gs x ++ [g.op.eval (g.inputs.map fun i => (W gs x).getD i false)] := by
  simp [W, List.foldl_append]

theorem W_length {n : ℕ} (gs : List Gate) (x : Fin n → Bool) :
    (W gs x).length = n + gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [W]
  | append_singleton gs g ih =>
    rw [W_snoc]
    simp [ih]
    omega

theorem getD_snoc (L : List Bool) (b : Bool) (i : ℕ) :
    (L ++ [b]).getD i false =
      if i < L.length then L.getD i false else if i = L.length then b else false := by
  simp only [List.getD_eq_getElem?_getD]
  split_ifs with h1 h2
  · rw [List.getElem?_append_left h1]
  · subst h2; simp
  · rw [List.getElem?_eq_none (by simp; omega)]
    simp only [Option.getD_none]

-- The input is zero on every variable of Z.
def Van {n : ℕ} (Z : List (Fin n)) (x : Fin n → Bool) : Prop := ∀ i ∈ Z, x i = false

-- Gate j is an OR gate one of whose wires is zero on all inputs that vanish on Z.
def Dead {n : ℕ} (gs : List Gate) (Z : List (Fin n)) (j : ℕ) : Prop :=
  ∃ g, gs[j]? = some g ∧ g.op.eval [true, false] = true ∧
    ∃ a ∈ g.inputs, ∀ x : Fin n → Bool, Van Z x → (W (gs.take j) x).getD a false = false

theorem Van_update {n : ℕ} (Z : List (Fin n)) (x : Fin n → Bool) (v : Fin n) (h : Van Z x) :
    Van Z (Function.update x v false) := by
  intro i hi
  by_cases e : i = v
  · subst e; simp
  · simp [Function.update_of_ne e, h i hi]

theorem Dead_mono {n : ℕ} (gs : List Gate) (Z Z' : List (Fin n)) (j : ℕ)
    (hs : ∀ i ∈ Z, i ∈ Z') (h : Dead gs Z j) : Dead gs Z' j := by
  obtain ⟨g, hg, ho, a, ha, hx⟩ := h
  exact ⟨g, hg, ho, a, ha, fun x hv => hx x (fun i hi => hv i (hs i hi))⟩

theorem Dead_snoc {n : ℕ} (gs : List Gate) (g : Gate) (Z : List (Fin n)) (j : ℕ)
    (hj : j < gs.length) : Dead (gs ++ [g]) Z j ↔ Dead gs Z j := by
  unfold Dead
  rw [List.getElem?_append_left hj, List.take_append_of_le_length (le_of_lt hj)]

theorem two_inputs (l : List ℕ) (hl : l.length ≤ 2) (a b : ℕ) (ha : a ∈ l) (hb : b ∈ l)
    (hab : a ≠ b) : ∀ c ∈ l, c = a ∨ c = b := by
  match l, hl with
  | [], _ => simp at ha
  | [c], _ =>
    simp at ha hb
    omega
  | [c, d], _ =>
    intro e he
    simp at ha hb he
    omega
  | _ :: _ :: _ :: _, h => simp at h

-- Setting one more variable to zero kills a new OR gate, when the wire depends on the
-- variable and is not below it.
theorem key {n : ℕ} (Z : List (Fin n)) (v : Fin n) (gs : List Gate)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ i : ℕ,
      (∃ x, Van Z x ∧
        (W gs x).getD i false ≠ (W gs (Function.update x v false)).getD i false) →
      (∃ y, Van Z y ∧ y v = false ∧ (W gs y).getD i false = true) →
      ∃ j, Dead gs (v :: Z) j ∧ ¬ Dead gs Z j := by
  induction gs using List.reverseRecOn with
  | nil =>
    rintro i ⟨x, hx, hne⟩ ⟨y, hy, hyv, hyt⟩
    exfalso
    simp only [W, List.foldl_nil, List.getD_eq_getElem?_getD] at hne hyt
    by_cases h : i < n
    · rw [List.getElem?_eq_getElem (by simpa using h)] at hne hyt
      rw [List.getElem?_eq_getElem (by simpa using h)] at hne
      simp only [List.getElem_ofFn, Option.getD_some] at hne hyt
      by_cases e : (⟨i, h⟩ : Fin n) = v
      · rw [e, hyv] at hyt
        exact absurd hyt (by simp)
      · exact hne (by rw [Function.update_of_ne e])
    · rw [List.getElem?_eq_none (by simpa using h)] at hyt
      simp at hyt
  | append_singleton gs g ih =>
    have hm' : ∀ g' ∈ gs, (g'.op = GateOp.and ∨ g'.op = GateOp.or) ∧ g'.inputs.length ≤ 2 :=
      fun g' hg' => hm g' (by simp [hg'])
    have hg := hm g (by simp)
    have ih := ih hm'
    have lift : (∃ j, Dead gs (v :: Z) j ∧ ¬ Dead gs Z j) →
        ∃ j, Dead (gs ++ [g]) (v :: Z) j ∧ ¬ Dead (gs ++ [g]) Z j := by
      rintro ⟨j, h1, h2⟩
      have hj : j < gs.length := by
        obtain ⟨g', hg', _⟩ := h1
        exact (List.getElem?_eq_some_iff.mp hg').1
      exact ⟨j, (Dead_snoc gs g _ j hj).mpr h1, fun h => h2 ((Dead_snoc gs g _ j hj).mp h)⟩
    rintro i ⟨x, hx, hne⟩ ⟨y, hy, hyv, hyt⟩
    rw [W_snoc, W_snoc, getD_snoc, getD_snoc, W_length, W_length] at hne
    rw [W_snoc, getD_snoc, W_length] at hyt
    by_cases h1 : i < n + gs.length
    · rw [if_pos h1, if_pos h1] at hne
      rw [if_pos h1] at hyt
      exact lift (ih i ⟨x, hx, hne⟩ ⟨y, hy, hyv, hyt⟩)
    · rw [if_neg h1, if_neg h1] at hne
      rw [if_neg h1] at hyt
      by_cases h2 : i = n + gs.length
      · rw [if_pos h2, if_pos h2] at hne
        rw [if_pos h2] at hyt
        by_cases hA : ∃ a ∈ g.inputs,
            (∃ x, Van Z x ∧
              (W gs x).getD a false ≠ (W gs (Function.update x v false)).getD a false) ∧
            (∃ y, Van Z y ∧ y v = false ∧ (W gs y).getD a false = true)
        · obtain ⟨a, _, hq, hr⟩ := hA
          exact lift (ih a hq hr)
        · have hex : ∃ a ∈ g.inputs,
              (W gs x).getD a false ≠ (W gs (Function.update x v false)).getD a false := by
            by_contra hcon
            push_neg at hcon
            apply hne
            congr 1
            exact List.map_congr_left hcon
          obtain ⟨a, ha, hane⟩ := hex
          have hRa : ∀ y, Van Z y → y v = false → (W gs y).getD a false = false := by
            intro y' hy' hv'
            by_contra hcon
            exact hA ⟨a, ha, ⟨x, hx, hane⟩, ⟨y', hy', hv', by simpa using hcon⟩⟩
          rcases hg.1 with hop | hop
          · exfalso
            rw [hop] at hyt
            simp only [GateOp.eval, List.all_map, List.all_eq_true] at hyt
            have h3 : (W gs y).getD a false = true := hyt a ha
            rw [hRa y hy hyv] at h3
            exact absurd h3 (by simp)
          · rw [hop] at hyt
            simp only [GateOp.eval, List.any_map, List.any_eq_true] at hyt
            obtain ⟨b, hb, hbt⟩ := hyt
            have hbt' : (W gs y).getD b false = true := hbt
            have hab : a ≠ b := by
              rintro rfl
              rw [hRa y hy hyv] at hbt'
              exact absurd hbt' (by simp)
            have htake : (gs ++ [g]).take gs.length = gs := by simp
            have hget : (gs ++ [g])[gs.length]? = some g := by simp
            refine ⟨gs.length, ⟨g, hget, by rw [hop]; rfl, a, ha, ?_⟩, ?_⟩
            · intro x' hx'
              rw [htake]
              exact hRa x' (fun i hi => hx' i (List.mem_cons_of_mem _ hi))
                (hx' v List.mem_cons_self)
            · rintro ⟨g', hg', _, c, hc, hcx⟩
              rw [hget] at hg'
              have hgg : g = g' := Option.some.inj hg'
              subst hgg
              rw [htake] at hcx
              rcases two_inputs g.inputs hg.2 a b ha hb hab c hc with rfl | rfl
              · apply hane
                rw [hcx x hx, hcx _ (Van_update Z x v hx)]
              · rw [hcx y hy] at hbt'
                exact absurd hbt' (by simp)
      · rw [if_neg h2, if_neg h2] at hne
        exact absurd rfl hne

theorem count_aux : ∀ (gs : List Gate) (S : Finset ℕ),
    (∀ j ∈ S, ∃ g, gs[j]? = some g ∧ g.op.eval [true, false] = true) →
    S.card ≤ (gs.filter fun g => g.op.eval [true, false]).length := by
  intro gs
  induction gs using List.reverseRecOn with
  | nil =>
    intro S hS
    have hE : S = ∅ := by
      apply Finset.eq_empty_of_forall_notMem
      intro j hj
      obtain ⟨g, hg, _⟩ := hS j hj
      simp at hg
    simp [hE]
  | append_singleton gs g ih =>
    intro S hS
    have hS' : ∀ j ∈ S.erase gs.length,
        ∃ g', gs[j]? = some g' ∧ g'.op.eval [true, false] = true := by
      intro j hj
      rw [Finset.mem_erase] at hj
      obtain ⟨g', hg', ho⟩ := hS j hj.2
      have hlt : j < (gs ++ [g]).length := (List.getElem?_eq_some_iff.mp hg').1
      have hj' : j < gs.length := by
        simp at hlt
        omega
      rw [List.getElem?_append_left hj'] at hg'
      exact ⟨g', hg', ho⟩
    have h1 := ih _ hS'
    rw [List.filter_append, List.length_append]
    by_cases hmem : gs.length ∈ S
    · obtain ⟨g', hg', ho⟩ := hS _ hmem
      have hget : (gs ++ [g])[gs.length]? = some g := by simp
      rw [hget] at hg'
      have hgg : g = g' := Option.some.inj hg'
      subst hgg
      have hc : (S.erase gs.length).card = S.card - 1 := Finset.card_erase_of_mem hmem
      have hpos : 0 < S.card := Finset.card_pos.mpr ⟨_, hmem⟩
      have hone : ([g].filter fun g => g.op.eval [true, false]).length = 1 := by
        simp [List.filter, ho]
      omega
    · rw [Finset.erase_eq_of_notMem hmem] at h1
      omega

-- A removal order: each variable in turn still matters and is not forced.
def Good {n : ℕ} (f : (Fin n → Bool) → Bool) : List (Fin n) → List (Fin n) → Prop
  | [], _ => True
  | v :: r, Z => ((∃ x, Van Z x ∧ f x ≠ f (Function.update x v false)) ∧
      (∃ y, Van Z y ∧ y v = false ∧ f y = true)) ∧ Good f r (v :: Z)

theorem chain {n : ℕ} (gs : List Gate) (out : ℕ)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) :
    ∀ (vs Z : List (Fin n)), Good (fun x => (W gs x).getD out false) vs Z →
      ∃ S : Finset ℕ, S.card = vs.length ∧
        ∀ j ∈ S, Dead gs (vs.reverse ++ Z) j ∧ ¬ Dead gs Z j := by
  intro vs
  induction vs with
  | nil =>
    intro Z _
    exact ⟨∅, by simp⟩
  | cons v r ih =>
    intro Z hG
    simp only [Good] at hG
    obtain ⟨⟨hq, hr⟩, hG'⟩ := hG
    obtain ⟨S, hc, hS⟩ := ih (v :: Z) hG'
    obtain ⟨j0, hj1, hj2⟩ := key Z v gs hm out hq hr
    have hnot : j0 ∉ S := fun h => (hS j0 h).2 hj1
    refine ⟨insert j0 S, by simp [Finset.card_insert_of_notMem hnot, hc], ?_⟩
    intro j hj
    rw [Finset.mem_insert] at hj
    rcases hj with rfl | hj
    · refine ⟨Dead_mono gs _ _ _ ?_ hj1, hj2⟩
      intro i hi
      simp at hi ⊢
      tauto
    · refine ⟨Dead_mono gs _ _ _ ?_ (hS j hj).1, fun h => (hS j hj).2
        (Dead_mono gs _ _ _ (fun i hi => List.mem_cons_of_mem _ hi) h)⟩
      intro i hi
      simp at hi ⊢
      tauto

theorem or_lower {n : ℕ} (gs : List Gate) (out : ℕ)
    (hm : ∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2)
    (vs : List (Fin n)) (hG : Good (fun x => (W gs x).getD out false) vs []) :
    vs.length ≤ (gs.filter fun g => g.op.eval [true, false]).length := by
  obtain ⟨S, hc, hS⟩ := chain gs out hm vs [] hG
  rw [← hc]
  apply count_aux
  intro j hj
  obtain ⟨g, hg, ho, _⟩ := (hS j hj).1
  exact ⟨g, hg, ho⟩

theorem Good_append {n : ℕ} (f : (Fin n → Bool) → Bool) :
    ∀ (xs ys Z : List (Fin n)), Good f xs Z → Good f ys (xs.reverse ++ Z) →
      Good f (xs ++ ys) Z := by
  intro xs
  induction xs with
  | nil =>
    intro ys Z _ h
    simpa using h
  | cons v r ih =>
    intro ys Z h1 h2
    simp only [List.cons_append, Good] at h1 ⊢
    refine ⟨h1.1, ih ys (v :: Z) h1.2 ?_⟩
    simpa using h2

theorem cn {N : ℕ} (p l : Fin N) : Fin.castAdd N p ≠ Fin.natAdd N l := by
  intro h
  have h' := congrArg Fin.val h
  simp at h'
  omega

theorem nat_inj {N : ℕ} {a b : Fin N} (h : Fin.natAdd N a = Fin.natAdd N b) : a = b := by
  have h' := congrArg Fin.val h
  simp at h'
  exact Fin.ext h'

theorem cast_inj {N : ℕ} {a b : Fin N} (h : Fin.castAdd N a = Fin.castAdd N b) : a = b := by
  have h' := congrArg Fin.val h
  simp at h'
  exact Fin.ext h'

theorem dec_false {α : Type} [DecidableEq α] {i a b : α} (h1 : i ≠ a) (h2 : i ≠ b) :
    decide (i = a ∨ i = b) = false := by
  apply decide_eq_false
  rintro (h | h)
  · exact h1 h
  · exact h2 h

theorem nat_notin_cast {N : ℕ} (l : Fin N) (s : List (Fin N)) :
    Fin.natAdd N l ∉ s.map (Fin.castAdd N) := by
  intro h
  obtain ⟨p, _, hp⟩ := List.mem_map.mp h
  exact cn p l hp

theorem cast_notin_nat {N : ℕ} (p : Fin N) (s : List (Fin N)) :
    Fin.castAdd N p ∉ s.map (Fin.natAdd N) := by
  intro h
  obtain ⟨l, _, hl⟩ := List.mem_map.mp h
  exact cn p l hl.symm

theorem nat_mem_map {N : ℕ} {l : Fin N} {s : List (Fin N)}
    (h : Fin.natAdd N l ∈ s.map (Fin.natAdd N)) : l ∈ s := by
  obtain ⟨m, hm, e⟩ := List.mem_map.mp h
  rw [← nat_inj e]
  exact hm

theorem cast_mem_map {N : ℕ} {p : Fin N} {s : List (Fin N)}
    (h : Fin.castAdd N p ∈ s.map (Fin.castAdd N)) : p ∈ s := by
  obtain ⟨m, hm, e⟩ := List.mem_map.mp h
  rw [← cast_inj e]
  exact hm

theorem stage {N : ℕ} (I : Fin N → Fin N → Prop) (f : (Fin (N + N) → Bool) → Bool)
    (acc : ∀ p l, I p l →
      f (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true)
    (rejP : ∀ x : Fin (N + N) → Bool, (∀ p, x (Fin.castAdd N p) = false) →
      (∀ l m, x (Fin.natAdd N l) = true → x (Fin.natAdd N m) = true → l = m) → f x = false)
    (rejL : ∀ x : Fin (N + N) → Bool, (∀ l, x (Fin.natAdd N l) = false) → f x = false)
    (p0 l0 : Fin N) (h0 : I p0 l0) :
    ∀ (vs Z : List (Fin (N + N))), vs.Nodup →
      Fin.castAdd N p0 ∉ Z → Fin.natAdd N l0 ∉ Z →
      Fin.castAdd N p0 ∉ vs → Fin.natAdd N l0 ∉ vs →
      (∀ v ∈ vs, ∃ p l, I p l ∧ Fin.castAdd N p ∉ Z ∧ Fin.natAdd N l ∉ Z ∧
        ((v = Fin.castAdd N p ∧ Fin.natAdd N l ∉ vs) ∨
          (v = Fin.natAdd N l ∧ Fin.castAdd N p ∉ vs))) →
      Good f vs Z := by
  intro vs
  induction vs with
  | nil =>
    intro Z _ _ _ _ _ _
    trivial
  | cons v r ih =>
    intro Z hnd hpZ hlZ hpv hlv hpart
    simp only [Good]
    rw [List.nodup_cons] at hnd
    rw [List.mem_cons, not_or] at hpv hlv
    refine ⟨⟨?_, ?_⟩, ?_⟩
    · obtain ⟨p, l, hI, hp, hl, hcase⟩ := hpart v List.mem_cons_self
      refine ⟨fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l), ?_, ?_⟩
      · intro i hi
        exact dec_false (fun e => hp (e ▸ hi)) (fun e => hl (e ▸ hi))
      · rw [acc p l hI]
        have hrej : f (Function.update
            (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) v false) = false := by
          rcases hcase with ⟨rfl, _⟩ | ⟨rfl, _⟩
          · apply rejP
            · intro a
              by_cases e : Fin.castAdd N a = Fin.castAdd N p
              · rw [e, Function.update_self]
              · rw [Function.update_of_ne e]
                exact dec_false e (cn a l)
            · intro a b ha hb
              rw [Function.update_of_ne (cn p a).symm] at ha
              rw [Function.update_of_ne (cn p b).symm] at hb
              have ha' : Fin.natAdd N a = Fin.castAdd N p ∨ Fin.natAdd N a = Fin.natAdd N l :=
                of_decide_eq_true ha
              have hb' : Fin.natAdd N b = Fin.castAdd N p ∨ Fin.natAdd N b = Fin.natAdd N l :=
                of_decide_eq_true hb
              rcases ha' with h | h
              · exact absurd h (cn p a).symm
              · rcases hb' with h' | h'
                · exact absurd h' (cn p b).symm
                · exact (nat_inj h).trans (nat_inj h').symm
          · apply rejL
            intro a
            by_cases e : Fin.natAdd N a = Fin.natAdd N l
            · rw [e, Function.update_self]
            · rw [Function.update_of_ne e]
              exact dec_false (cn p a).symm e
        rw [hrej]
        simp
    · refine ⟨fun i => decide (i = Fin.castAdd N p0 ∨ i = Fin.natAdd N l0), ?_, ?_, acc p0 l0 h0⟩
      · intro i hi
        exact dec_false (fun e => hpZ (e ▸ hi)) (fun e => hlZ (e ▸ hi))
      · exact dec_false (fun e => hpv.1 e.symm) (fun e => hlv.1 e.symm)
    · apply ih (v :: Z) hnd.2
      · simp only [List.mem_cons, not_or]
        exact ⟨hpv.1, hpZ⟩
      · simp only [List.mem_cons, not_or]
        exact ⟨hlv.1, hlZ⟩
      · exact hpv.2
      · exact hlv.2
      · intro w hw
        have hwv : w ≠ v := fun e => hnd.1 (e ▸ hw)
        obtain ⟨p, l, hI, hp, hl, hcase⟩ := hpart w (List.mem_cons_of_mem _ hw)
        refine ⟨p, l, hI, ?_, ?_, ?_⟩
        · simp only [List.mem_cons, not_or]
          refine ⟨?_, hp⟩
          rcases hcase with ⟨rfl, _⟩ | ⟨_, h⟩
          · exact hwv
          · exact fun e => h (by rw [e]; exact List.mem_cons_self)
        · simp only [List.mem_cons, not_or]
          refine ⟨?_, hl⟩
          rcases hcase with ⟨_, h⟩ | ⟨rfl, _⟩
          · exact fun e => h (by rw [e]; exact List.mem_cons_self)
          · exact hwv
        · rcases hcase with ⟨e, h⟩ | ⟨e, h⟩
          · exact Or.inl ⟨e, fun h' => h (List.mem_cons_of_mem _ h')⟩
          · exact Or.inr ⟨e, fun h' => h (List.mem_cons_of_mem _ h')⟩

theorem deg_le {q N : ℕ} (I : Fin N → Fin N → Prop) [DecidableRel I] (hq : 0 < q)
    (hN : N = q ^ 2 + q + 1)
    (hcard : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1)
    (huniq : ∀ p r : Fin N, p ≠ r → ∃! l : Fin N, I p l ∧ I r l) (p0 : Fin N) :
    (Finset.univ.filter fun l => I p0 l).card ≤ q + 1 := by
  have hA : ∀ l ∈ Finset.univ.filter (fun l => I p0 l),
      ((Finset.univ.filter fun p => I p l).erase p0).card = q := by
    intro l hl
    have hp : p0 ∈ Finset.univ.filter fun p => I p l := by simpa using hl
    rw [Finset.card_erase_of_mem hp, hcard l]
    rfl
  have hsub : (Finset.univ.filter fun l => I p0 l).biUnion
      (fun l => (Finset.univ.filter fun p => I p l).erase p0) ⊆ Finset.univ.erase p0 := by
    intro r hr
    simp only [Finset.mem_biUnion, Finset.mem_erase] at hr
    obtain ⟨l, _, hne, _⟩ := hr
    simp [hne]
  have h1 := Finset.card_le_card hsub
  rw [Finset.card_biUnion, Finset.sum_congr rfl hA, Finset.sum_const, smul_eq_mul,
    Finset.card_erase_of_mem (Finset.mem_univ _), Finset.card_univ, Fintype.card_fin] at h1
  · by_contra hcon
    push_neg at hcon
    have h2 : (q + 2) * q ≤ (Finset.univ.filter fun l => I p0 l).card * q :=
      Nat.mul_le_mul_right q hcon
    have h3 : N - 1 = q * q + q := by
      rw [hN, pow_two]
      omega
    rw [h3] at h1
    nlinarith
  · intro l hl m hm hlm
    refine Finset.disjoint_left.mpr ?_
    intro r hr1 hr2
    simp only [Finset.mem_erase, Finset.mem_filter, Finset.mem_univ, true_and, Finset.coe_filter,
      Set.mem_setOf_eq] at hr1 hr2 hl hm
    obtain ⟨u, _, hu⟩ := huniq p0 r (Ne.symm hr1.1)
    exact hlm ((hu l ⟨hl, hr1.2⟩).trans (hu m ⟨hm, hr2.2⟩).symm)

theorem main : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false]) x5.gates).length := by
  intro q N I _ C hq hN hcard huniq hmono hacc hsound
  have hm : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
    intro g hg
    have h := hmono g hg
    simpa [Set.mem_insert_iff] using h
  have hf : ∀ x : Fin (N + N) → Bool,
      PEqualNP.MetaComplexity.circuitFun (N + N) C x = (W C.gates x).getD C.output false :=
    fun x => rfl
  have acc : ∀ p l, I p l → (fun x : Fin (N + N) → Bool => (W C.gates x).getD C.output false)
      (fun i => decide (i = Fin.castAdd N p ∨ i = Fin.natAdd N l)) = true := by
    intro p l hI
    exact (hf _).symm.trans (hacc p l hI)
  have rejL : ∀ x : Fin (N + N) → Bool, (∀ l, x (Fin.natAdd N l) = false) →
      (fun x : Fin (N + N) → Bool => (W C.gates x).getD C.output false) x = false := by
    intro x hx
    refine (hf x).symm.trans (hsound x ?_ ?_)
    · have hE : IsEmpty { l : Fin N // x (Fin.natAdd N l) = true } :=
        ⟨fun a => by have h := a.2; rw [hx a.1] at h; exact Bool.false_ne_true h⟩
      rw [Fintype.card_eq_zero_iff.mpr hE]
      exact Nat.zero_le _
    · rintro ⟨p, l, _, _, hl⟩
      rw [hx l] at hl
      exact Bool.false_ne_true hl
  have rejP : ∀ x : Fin (N + N) → Bool, (∀ p, x (Fin.castAdd N p) = false) →
      (∀ l m, x (Fin.natAdd N l) = true → x (Fin.natAdd N m) = true → l = m) →
      (fun x : Fin (N + N) → Bool => (W C.gates x).getD C.output false) x = false := by
    intro x hx hone
    refine (hf x).symm.trans (hsound x ?_ ?_)
    · have hS : Subsingleton { l : Fin N // x (Fin.natAdd N l) = true } :=
        ⟨fun a b => Subtype.ext (hone a.1 b.1 a.2 b.2)⟩
      exact (Fintype.card_le_one_iff_subsingleton.mpr hS).trans (by omega)
    · rintro ⟨p, l, _, hp, _⟩
      rw [hx p] at hp
      exact Bool.false_ne_true hp
  have hNpos : 0 < N := by
    rw [hN]
    exact Nat.succ_pos _
  have hcard' : ∀ l : Fin N, (Finset.univ.filter fun p => I p l).card = q + 1 := by
    intro l
    rw [← hcard l, Fintype.card_subtype]
  have l0 : Fin N := ⟨0, hNpos⟩
  have h2 : 1 < (Finset.univ.filter fun p => I p l0).card := by
    rw [hcard' l0]
    omega
  obtain ⟨p0, hp0, r, hr, hpr⟩ := Finset.one_lt_card.mp h2
  simp only [Finset.mem_filter, Finset.mem_univ, true_and] at hp0 hr
  have hdeg := deg_le I (by omega) hN hcard' huniq p0
  obtain ⟨A1, hA1nd, hA1, hA1len⟩ : ∃ A : List (Fin N), A.Nodup ∧ (∀ l, l ∈ A → ¬ I p0 l) ∧
      A.length = (Finset.univ.filter fun l => ¬ I p0 l).card :=
    ⟨_, Finset.nodup_toList _, fun l hl => by simpa using hl, Finset.length_toList _⟩
  obtain ⟨A2, hA2nd, hA2, hA2len⟩ : ∃ A : List (Fin N), A.Nodup ∧ (∀ p, p ∈ A → ¬ I p l0) ∧
      A.length = (Finset.univ.filter fun p => ¬ I p l0).card :=
    ⟨_, Finset.nodup_toList _, fun l hl => by simpa using hl, Finset.length_toList _⟩
  have hZ1 : ∀ u, u ∈ (A1.map (Fin.natAdd N)).reverse ++ [] → u ∈ A1.map (Fin.natAdd N) := by
    intro u hu
    simpa only [List.append_nil, List.mem_reverse] using hu
  have hZ2 : ∀ u, u ∈ (A2.map (Fin.castAdd N)).reverse ++ ((A1.map (Fin.natAdd N)).reverse ++ []) →
      u ∈ A2.map (Fin.castAdd N) ∨ u ∈ A1.map (Fin.natAdd N) := by
    intro u hu
    simpa only [List.mem_append, List.mem_reverse, List.append_nil] using hu
  have n1 : ∀ l, I p0 l → Fin.natAdd N l ∉ A1.map (Fin.natAdd N) :=
    fun l hl h => hA1 l (nat_mem_map h) hl
  have c2 : ∀ p, I p l0 → Fin.castAdd N p ∉ A2.map (Fin.castAdd N) :=
    fun p hp h => hA2 p (cast_mem_map h) hp
  have hG : Good (fun x : Fin (N + N) → Bool => (W C.gates x).getD C.output false)
      ((A1.map (Fin.natAdd N)) ++ ((A2.map (Fin.castAdd N)) ++ [Fin.castAdd N r])) [] := by
    apply Good_append
    · apply stage I _ acc rejP rejL p0 l0 hp0
      · exact hA1nd.map (Fin.natAdd_injective _ _)
      · exact List.not_mem_nil
      · exact List.not_mem_nil
      · exact cast_notin_nat p0 A1
      · exact n1 l0 hp0
      · intro v hv
        obtain ⟨l, _, rfl⟩ := List.mem_map.mp hv
        have hpos : 0 < (Finset.univ.filter fun p => I p l).card := by
          rw [hcard' l]
          omega
        obtain ⟨a, ha⟩ := Finset.card_pos.mp hpos
        simp only [Finset.mem_filter, Finset.mem_univ, true_and] at ha
        exact ⟨a, l, ha, List.not_mem_nil, List.not_mem_nil, Or.inr ⟨rfl, cast_notin_nat a A1⟩⟩
    · apply Good_append
      · apply stage I _ acc rejP rejL p0 l0 hp0
        · exact hA2nd.map (Fin.castAdd_injective _ _)
        · exact fun h => cast_notin_nat p0 A1 (hZ1 _ h)
        · exact fun h => n1 l0 hp0 (hZ1 _ h)
        · exact c2 p0 hp0
        · exact nat_notin_cast l0 A2
        · intro v hv
          obtain ⟨p, hp, rfl⟩ := List.mem_map.mp hv
          have hne : p ≠ p0 := fun e => hA2 p hp (e ▸ hp0)
          obtain ⟨m, ⟨hm1, hm2⟩, _⟩ := huniq p p0 hne
          exact ⟨p, m, hm1, fun h => cast_notin_nat p A1 (hZ1 _ h),
            fun h => n1 m hm2 (hZ1 _ h), Or.inl ⟨rfl, nat_notin_cast m A2⟩⟩
      · have hcz : ∀ p, I p l0 → Fin.castAdd N p ∉
            (A2.map (Fin.castAdd N)).reverse ++ ((A1.map (Fin.natAdd N)).reverse ++ []) := by
          intro p hp h
          rcases hZ2 _ h with h | h
          · exact c2 p hp h
          · exact cast_notin_nat p A1 h
        have hnz : Fin.natAdd N l0 ∉
            (A2.map (Fin.castAdd N)).reverse ++ ((A1.map (Fin.natAdd N)).reverse ++ []) := by
          intro h
          rcases hZ2 _ h with h | h
          · exact nat_notin_cast l0 A2 h
          · exact n1 l0 hp0 h
        have hn3 : Fin.natAdd N l0 ∉ [Fin.castAdd N r] :=
          fun h => cn r l0 (List.mem_singleton.mp h).symm
        apply stage I _ acc rejP rejL p0 l0 hp0
        · exact List.nodup_singleton _
        · exact hcz p0 hp0
        · exact hnz
        · exact fun h => hpr (cast_inj (List.mem_singleton.mp h))
        · exact hn3
        · intro v hv
          exact ⟨r, l0, hr, hcz r hr, hnz, Or.inl ⟨List.mem_singleton.mp hv, hn3⟩⟩
  have hfin := or_lower C.gates C.output hm _ hG
  simp only [List.length_append, List.length_map, List.length_singleton] at hfin
  rw [hA1len, hA2len] at hfin
  have e1 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (fun l => I p0 l)
  have e2 := Finset.card_filter_add_card_filter_not (s := (Finset.univ : Finset (Fin N)))
    (fun p => I p l0)
  rw [Finset.card_univ, Fintype.card_fin] at e1 e2
  rw [hcard' l0] at e2
  generalize q ^ 2 = Q at hN ⊢
  omega

end PEqualNP.Outside.L_meta_3308

theorem PEqualNP.Outside.L_meta_3308 : ∀ (x1 x2 : ℕ) (x3 : Fin x2 → Fin x2 → Prop) [x4 : DecidableRel x3] (x5 : PEqualNP.CircuitLowerBounds.Circuit), (200 : ℕ) ≤ x1 → x2 = x1 ^ (2 : ℕ) + x1 + (1 : ℕ) → (∀ (x8 : Fin x2), Fintype.card { x9 : Fin x2 // x3 x9 x8 } = x1 + (1 : ℕ)) → (∀ (x9 x10 : Fin x2), x9 ≠ x10 → ∃! x12 : Fin x2, x3 x9 x12 ∧ x3 x10 x12) → PEqualNP.MetaComplexity.Monotone2 x5 → (∀ (x11 x12 : Fin x2), x3 x11 x12 → (PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 fun (x14 : Fin (x2 + x2)) => Decidable.decide (x14 = Fin.castAdd x2 x11 ∨ x14 = Fin.natAdd x2 x12)) = Bool.true) → (∀ (x12 : Fin (x2 + x2) → Bool), Fintype.card { x13 : Fin x2 // x12 (Fin.natAdd x2 x13) = Bool.true } ≤ x1 → (¬∃ (x14 : Fin x2) (x15 : Fin x2), x3 x14 x15 ∧ x12 (Fin.castAdd x2 x14) = Bool.true ∧ x12 (Fin.natAdd x2 x15) = Bool.true) → PEqualNP.MetaComplexity.circuitFun (x2 + x2) x5 x12 = Bool.false) → (2 : ℕ) * x1 ^ (2 : ℕ) + (1 : ℕ) ≤ (List.filter (fun (x13 : PEqualNP.CircuitLowerBounds.Gate) => x13.op.eval [Bool.true, Bool.false]) x5.gates).length :=
  PEqualNP.Outside.L_meta_3308.main
