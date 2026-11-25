import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.CoverPromise PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_612_363
    (leastTop : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      NoFourCycle G → (∃ u v, G.Adj u v) →
      ∀ D : Circuit, IsLeastAO G D →
        ∃ D' : Circuit, IsLeastAO G D' ∧ TopForm G D' ∧ D'.size ≤ D.size)
    (charge : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      NoFourCycle G → (∃ u v, G.Adj u v) →
      ∀ C : Circuit, IsLeastAO G C → TopForm G C →
        ∃ S : Finset (Fin n), IsVertexCover G S ∧ G.edgeSet.ncard + S.card ≤ C.size + 1) :
    (∀ (n t : ℕ) (G : SimpleGraph (Fin n)) (C : PEqualNP.CircuitLowerBounds.Circuit), (∃ u v : Fin n, G.Adj u v) → (∀ a b c d : Fin n, a ≠ b → a ≠ c → a ≠ d → b ≠ c → b ≠ d → c ≠ d → G.Adj a b → G.Adj b c → G.Adj c d → ¬ G.Adj d a) → (∃ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S ∧ S.card = t) → (∀ S : Finset (Fin n), PEqualNP.MetaComplexity.CoverPromise.IsVertexCover G S → t ≤ S.card) → PEqualNP.MetaComplexity.Monotone2 C → (∀ x : Fin n → Bool, (C.eval (List.ofFn x) = true ↔ ∃ u v : Fin n, G.Adj u v ∧ x u = true ∧ x v = true)) → G.edgeSet.ncard + t ≤ C.size + 1) := by
  classical
  intro n t G C hasEdge noCycle _ minCover monotone computes
  have squareFree : NoFourCycle G := by
    intro a b hab
    apply Finset.card_le_one.mpr
    intro c hc d hd
    have hac := (Finset.mem_filter.mp hc).2.1
    have hbc := (Finset.mem_filter.mp hc).2.2
    have had := (Finset.mem_filter.mp hd).2.1
    have hbd := (Finset.mem_filter.mp hd).2.2
    by_contra hcd
    exact noCycle a c b d hac.ne hab had.ne hbc.symm.ne hcd hbd.ne hac hbc.symm hbd had.symm
  have computesGraph : circuitFun n C = graphFun G ∅ := by
    funext x
    delta circuitFun graphFun
    apply Bool.eq_iff_iff.mpr
    simpa using computes x
  -- normalization into the model IsAO2, without growing
  have ao2 : ∃ D : Circuit, IsAO2 n D ∧ circuitFun n D = graphFun G ∅ ∧ D.size ≤ C.size := by
    have eval_and : ∀ l : List Bool, GateOp.and.eval l = l.all id := fun _ => rfl
    have eval_or : ∀ l : List Bool, GateOp.or.eval l = l.any id := fun _ => rfl
    let step : List Bool → Gate → List Bool :=
      fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]
    let W : List Gate → (Fin n → Bool) → List Bool := fun gs x => gs.foldl step (List.ofFn x)
    have step_len : ∀ (w : List Bool) (g : Gate), (step w g).length = w.length + 1 := by
      intro w g
      simp [step]
    have step_lt : ∀ (w : List Bool) (g : Gate) (i : ℕ), i < w.length →
        (step w g).getD i false = w.getD i false := by
      intro w g i hi
      simp [step, List.getD, List.getElem?_append_left hi]
    have step_last : ∀ (w : List Bool) (g : Gate) (k : ℕ), k = w.length →
        (step w g).getD k false = g.op.eval (g.inputs.map fun i => w.getD i false) := by
      intro w g k hk
      subst hk
      simp [step, List.getD]
    have W_len : ∀ (gs : List Gate) (x : Fin n → Bool), (W gs x).length = n + gs.length := by
      have h : ∀ (gs : List Gate) (w : List Bool),
          (gs.foldl step w).length = w.length + gs.length := by
        intro gs
        induction gs with
        | nil => intro w; simp
        | cons g gs ih =>
          intro w
          rw [List.foldl_cons, ih, step_len, List.length_cons]
          omega
      intro gs x
      show (gs.foldl step (List.ofFn x)).length = _
      rw [h]
      simp
    have W_snoc : ∀ (gs : List Gate) (g : Gate) (x : Fin n → Bool),
        W (gs ++ [g]) x = step (W gs x) g := by
      intro gs g x
      simp [W, List.foldl_append]
    have W_val : ∀ (gs : List Gate) (g : Gate) (x : Fin n → Bool) (t : ℕ),
        (W (gs ++ [g]) x).getD t false =
          if t = n + gs.length then g.op.eval (g.inputs.map fun i => (W gs x).getD i false)
          else (W gs x).getD t false := by
      intro gs g x t
      rw [W_snoc]
      by_cases ht : t = n + gs.length
      · rw [if_pos ht, step_last _ _ _ (by rw [W_len]; exact ht)]
      · rw [if_neg ht]
        by_cases hlt : t < n + gs.length
        · exact step_lt _ _ _ (by rw [W_len]; exact hlt)
        · rw [List.getD_eq_default _ _ (by rw [step_len, W_len]; omega),
            List.getD_eq_default _ _ (by rw [W_len]; omega)]
    let Rep : List Gate → ((Fin n → Bool) → Bool) → Prop := fun new f =>
      (∃ c : Bool, ∀ x : Fin n → Bool, f x = c) ∨
        (∃ j : ℕ, j < n + new.length ∧ ∀ x : Fin n → Bool, (W new x).getD j false = f x)
    let Fan : Gate → Prop := fun g =>
      (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length = 2
    let Ext : List Gate → List Gate → Prop := fun new new' =>
      new' = new ∨ ∃ h : Gate, new' = new ++ [h] ∧ Fan h ∧ ∀ i ∈ h.inputs, i < n + new.length
    have rep_congr : ∀ (new : List Gate) (f g : (Fin n → Bool) → Bool),
        (∀ x, f x = g x) → Rep new f → Rep new g := by
      intro new f g h hf
      obtain rfl : f = g := funext h
      exact hf
    have rep_mono : ∀ (new new' : List Gate), Ext new new' →
        ∀ (f : (Fin n → Bool) → Bool), Rep new f → Rep new' f := by
      intro new new' he f h
      rcases he with rfl | ⟨k, rfl, _⟩
      · exact h
      · rcases h with hc | ⟨j, hj, hv⟩
        · exact Or.inl hc
        · have hne : ¬ j = n + new.length := by omega
          refine Or.inr ⟨j, by rw [List.length_append, List.length_singleton]; omega, fun x => ?_⟩
          rw [W_val, if_neg hne]
          exact hv x
    have rep_and : ∀ (new : List Gate) (f g : (Fin n → Bool) → Bool), Rep new f → Rep new g →
        ∃ new', Ext new new' ∧ Rep new' (fun x => f x && g x) := by
      intro new f g hf hg
      rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
      · cases c1 with
        | false =>
          exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
            show (f x && g x) = false
            simp [h1 x]⟩⟩
        | true =>
          exact ⟨new, Or.inl rfl, rep_congr _ _ _ (fun x => by
            show g x = (f x && g x)
            simp [h1 x]) hg⟩
      · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
        · cases c2 with
          | false =>
            exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by
              show (f x && g x) = false
              simp [h2 x]⟩⟩
          | true =>
            exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
              show (W new x).getD j false = (f x && g x)
              rw [hjv x]
              simp [h2 x]⟩⟩
        · refine ⟨new ++ [⟨GateOp.and, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inl rfl, rfl⟩,
            (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
            Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
              fun x => ?_⟩⟩
          show (W (new ++ [⟨GateOp.and, [j, k]⟩]) x).getD (n + new.length) false = (f x && g x)
          rw [W_val, if_pos rfl]
          show GateOp.and.eval [(W new x).getD j false, (W new x).getD k false] = _
          rw [hjv x, hkv x]
          simp [eval_and, eval_or]
    have rep_or : ∀ (new : List Gate) (f g : (Fin n → Bool) → Bool), Rep new f → Rep new g →
        ∃ new', Ext new new' ∧ Rep new' (fun x => f x || g x) := by
      intro new f g hf hg
      rcases hf with ⟨c1, h1⟩ | ⟨j, hj, hjv⟩
      · cases c1 with
        | true =>
          exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
            show (f x || g x) = true
            simp [h1 x]⟩⟩
        | false =>
          exact ⟨new, Or.inl rfl, rep_congr _ _ _ (fun x => by
            show g x = (f x || g x)
            simp [h1 x]) hg⟩
      · rcases hg with ⟨c2, h2⟩ | ⟨k, hk, hkv⟩
        · cases c2 with
          | true =>
            exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by
              show (f x || g x) = true
              simp [h2 x]⟩⟩
          | false =>
            exact ⟨new, Or.inl rfl, Or.inr ⟨j, hj, fun x => by
              show (W new x).getD j false = (f x || g x)
              rw [hjv x]
              simp [h2 x]⟩⟩
        · refine ⟨new ++ [⟨GateOp.or, [j, k]⟩], Or.inr ⟨_, rfl, ⟨Or.inr rfl, rfl⟩,
            (by intro i hi; simp at hi; rcases hi with rfl | rfl <;> assumption)⟩,
            Or.inr ⟨n + new.length, by rw [List.length_append, List.length_singleton]; omega,
              fun x => ?_⟩⟩
          show (W (new ++ [⟨GateOp.or, [j, k]⟩]) x).getD (n + new.length) false = (f x || g x)
          rw [W_val, if_pos rfl]
          show GateOp.or.eval [(W new x).getD j false, (W new x).getD k false] = _
          rw [hjv x, hkv x]
          simp [eval_and, eval_or]
    have rep_input : ∀ t : ℕ, Rep ([] : List Gate) (fun x => (W [] x).getD t false) := by
      intro t
      by_cases ht : t < n
      · exact Or.inr ⟨t, by simpa using ht, fun x => rfl⟩
      · exact Or.inl ⟨false, fun x =>
          List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)⟩
    have gate_rep : ∀ (old new : List Gate) (op : GateOp) (l : List ℕ),
        (op = GateOp.and ∨ op = GateOp.or) → l.length ≤ 2 →
        (∀ t : ℕ, Rep new (fun x => (W old x).getD t false)) →
        ∃ new', Ext new new' ∧
          Rep new' (fun x => op.eval (l.map fun i => (W old x).getD i false)) := by
      intro old new op l hop hlen h
      rcases l with _ | ⟨a, _ | ⟨b, _ | ⟨c3, rest⟩⟩⟩
      · rcases hop with rfl | rfl
        · exact ⟨new, Or.inl rfl, Or.inl ⟨true, fun x => by simp [eval_and, eval_or]⟩⟩
        · exact ⟨new, Or.inl rfl, Or.inl ⟨false, fun x => by simp [eval_and, eval_or]⟩⟩
      · rcases hop with rfl | rfl
        · exact ⟨new, Or.inl rfl, rep_congr _ _ _ (fun x => by simp [eval_and, eval_or]) (h a)⟩
        · exact ⟨new, Or.inl rfl, rep_congr _ _ _ (fun x => by simp [eval_and, eval_or]) (h a)⟩
      · rcases hop with rfl | rfl
        · obtain ⟨new', he, hr⟩ := rep_and new _ _ (h a) (h b)
          exact ⟨new', he, rep_congr _ _ _ (fun x => by simp [eval_and, eval_or]) hr⟩
        · obtain ⟨new', he, hr⟩ := rep_or new _ _ (h a) (h b)
          exact ⟨new', he, rep_congr _ _ _ (fun x => by simp [eval_and, eval_or]) hr⟩
      · simp only [List.length_cons] at hlen
        omega
    let RB : List Gate → Prop := fun new =>
      ∀ j < new.length, ∀ i ∈ (new.getD j ⟨GateOp.or, []⟩).inputs, i < n + j
    have rb_snoc : ∀ (new : List Gate) (h : Gate), RB new →
        (∀ i ∈ h.inputs, i < n + new.length) → RB (new ++ [h]) := by
      intro new h hrb hh j hj i hi
      rw [List.length_append, List.length_singleton] at hj
      by_cases hlt : j < new.length
      · have e : (new ++ [h]).getD j ⟨GateOp.or, []⟩ = new.getD j ⟨GateOp.or, []⟩ := by
          simp [List.getD, List.getElem?_append_left hlt]
        rw [e] at hi
        exact hrb j hlt i hi
      · have hj' : j = new.length := by omega
        subst hj'
        have e : (new ++ [h]).getD new.length ⟨GateOp.or, []⟩ = h := by simp [List.getD]
        rw [e] at hi
        exact hh i hi
    let Inv : List Gate → Prop := fun old =>
      ∃ new : List Gate, (∀ g ∈ new, Fan g) ∧ RB new ∧ new.length ≤ old.length ∧
        ∀ t : ℕ, Rep new (fun x => (W old x).getD t false)
    have inv_step : ∀ (old : List Gate) (g : Gate),
        (g.op = GateOp.and ∨ g.op = GateOp.or) → g.inputs.length ≤ 2 →
        Inv old → Inv (old ++ [g]) := by
      intro old g hop hlen h
      obtain ⟨new, hfan, hrb, hl, hrep⟩ := h
      obtain ⟨new', he, hr⟩ := gate_rep old new g.op g.inputs hop hlen hrep
      refine ⟨new', ?_, ?_, ?_, ?_⟩
      · rcases he with rfl | ⟨k, rfl, hk, _⟩
        · exact hfan
        · intro q hq
          rcases List.mem_append.mp hq with hq | hq
          · exact hfan q hq
          · rw [List.mem_singleton] at hq
            rw [hq]
            exact hk
      · rcases he with rfl | ⟨k, rfl, _, hkb⟩
        · exact hrb
        · exact rb_snoc _ _ hrb hkb
      · rcases he with rfl | ⟨k, rfl, hk, _⟩
        · rw [List.length_append, List.length_singleton]
          omega
        · rw [List.length_append, List.length_append, List.length_singleton, List.length_singleton]
          omega
      · intro t
        by_cases ht : t = n + old.length
        · exact rep_congr _ _ _ (fun x => by
            show _ = (W (old ++ [g]) x).getD t false
            rw [W_val, if_pos ht]) hr
        · exact rep_congr _ _ _ (fun x => by
            show _ = (W (old ++ [g]) x).getD t false
            rw [W_val, if_neg ht]) (rep_mono _ _ he _ (hrep t))
    have inv_all : ∀ gates : List Gate,
        (∀ g ∈ gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2) →
        Inv gates := by
      intro gates hg
      have hall : ∀ (post pre : List Gate), pre ++ post = gates → Inv pre → Inv gates := by
        intro post
        induction post with
        | nil =>
          intro pre h hinv
          rw [List.append_nil] at h
          rw [← h]
          exact hinv
        | cons g post ih =>
          intro pre h hinv
          have hmem : g ∈ gates := by
            rw [← h]
            simp
          exact ih (pre ++ [g]) (by rw [List.append_assoc]; exact h)
            (inv_step pre g (hg g hmem).1 (hg g hmem).2 hinv)
      exact hall gates [] (List.nil_append _)
        ⟨[], by simp, (by intro j hj; simp at hj), le_refl _, rep_input⟩
    have hg : ∀ g ∈ C.gates, (g.op = GateOp.and ∨ g.op = GateOp.or) ∧ g.inputs.length ≤ 2 := by
      intro g hgm
      have h := monotone g hgm
      refine ⟨?_, h.2⟩
      have h1 := h.1
      simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
      exact h1
    obtain ⟨new, hfan, hrb, hl, hrep⟩ := inv_all C.gates hg
    have hev : ∀ x : Fin n → Bool, circuitFun n C x = (W C.gates x).getD C.output false :=
      fun x => rfl
    rcases hrep C.output with ⟨c, hc⟩ | ⟨j, _, hj⟩
    · have hc' : ∀ x : Fin n → Bool, circuitFun n C x = c := fun x => (hev x).trans (hc x)
      have hcf : c = false := by
        have h0 := computes (fun _ => false)
        have h1 : C.eval (List.ofFn fun _ : Fin n => false) = c := hc' _
        rw [h1] at h0
        cases c with
        | false => rfl
        | true =>
          obtain ⟨u, v, _, hu, _⟩ := h0.mp rfl
          exact absurd hu (by simp)
      subst hcf
      refine ⟨⟨[], n⟩, ⟨?_, ?_, ?_⟩, ?_, Nat.zero_le _⟩
      · intro g hgm
        simp at hgm
      · intro k hk
        simp at hk
      · intro g hgm
        simp at hgm
      · funext x
        rw [← computesGraph, hc' x]
        show (W ([] : List Gate) x).getD n false = false
        exact List.getD_eq_default _ _ (by rw [W_len, List.length_nil]; omega)
    · refine ⟨⟨new, j⟩, ⟨?_, ?_, ?_⟩, ?_, hl⟩
      · intro g hgm
        exact (hfan g hgm).1
      · exact hrb
      · intro g hgm
        exact (hfan g hgm).2
      · funext x
        rw [← computesGraph, hev x]
        exact hj x
  -- a least circuit of the model, no larger than the normalized one
  have leastEx : ∃ D : Circuit, IsLeastAO G D ∧ D.size ≤ C.size := by
    have hex : ∃ s, ∃ D : Circuit, IsAO2 n D ∧ D.size = s ∧ circuitFun n D = graphFun G ∅ := by
      obtain ⟨D, hD, hf, _⟩ := ao2
      exact ⟨D.size, D, hD, rfl, hf⟩
    obtain ⟨D, hD, hs, hf⟩ := Nat.find_spec hex
    refine ⟨D, ⟨hD, hf, fun D' hD' hf' => ?_⟩, ?_⟩
    · rw [hs]
      exact Nat.find_min' hex ⟨D', hD', rfl, hf'⟩
    · obtain ⟨E, hE, hEf, hEs⟩ := ao2
      rw [hs]
      exact (Nat.find_min' hex ⟨E, hE, rfl, hEf⟩).trans hEs
  obtain ⟨D0, least0, size0⟩ := leastEx
  obtain ⟨D, least, top, size⟩ := leastTop n G squareFree hasEdge D0 least0
  obtain ⟨S, cover, bound⟩ := charge n G squareFree hasEdge D least top
  exact (Nat.add_le_add_left (minCover S cover) _).trans
    (bound.trans (Nat.add_le_add_right (size.trans size0) 1))
