import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity
open PEqualNP.MetaComplexity.CoverPromise PEqualNP.MetaComplexity.NestedCover
open PEqualNP.TopForm

theorem PEqualNP.Outside.R_meta_612_341
    (normalize : ∀ (n : ℕ) (G : SimpleGraph (Fin n)) [DecidableRel G.Adj],
      NoFourCycle G → (∃ u v, G.Adj u v) →
      ∀ C : Circuit, Monotone2 C → circuitFun n C = graphFun G ∅ →
        ∃ D : Circuit, IsLeastAO G D ∧ TopForm G D ∧ D.size ≤ C.size)
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
  obtain ⟨D, least, top, size⟩ := normalize n G squareFree hasEdge C monotone computesGraph
  obtain ⟨S, cover, bound⟩ := charge n G squareFree hasEdge D least top
  exact (Nat.add_le_add_left (minCover S cover) _).trans (bound.trans (Nat.add_le_add_right size 1))
