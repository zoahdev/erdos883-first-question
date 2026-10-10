import CanonicalTarget
import Mathlib.Combinatorics.SimpleGraph.Maps

/-!
Independent statement and representation work for Erdős problem 883, part (ii).
This file does not assert or assume a proof of the full second question.
It uses the original problem and standard Mathlib graph definitions. No existing
second-question proof source has been copied or consulted in writing this file.
The imported first-question statement retains its existing attribution.
-/

namespace Erdos883Second

/-- One vertex in the apex part and `l` vertices in each of the other parts. -/
abbrev TripartiteVertex (l : ℕ) := Unit ⊕ (Fin l ⊕ Fin l)

def part {l : ℕ} : TripartiteVertex l → Fin 3
  | .inl _ => 0
  | .inr (.inl _) => 1
  | .inr (.inr _) => 2

/-- The complete `(1,l,l)` tripartite graph. -/
def tripartiteGraph (l : ℕ) : SimpleGraph (TripartiteVertex l) :=
  SimpleGraph.comap part ⊤

@[simp] theorem tripartiteGraph_adj {l : ℕ} (u v : TripartiteVertex l) :
    (tripartiteGraph l).Adj u v ↔ part u ≠ part v := Iff.rfl

@[simp] theorem tripartiteVertex_card (l : ℕ) :
    Fintype.card (TripartiteVertex l) = 2 * l + 1 := by
  simp [TripartiteVertex]
  omega

/-- An injective homomorphism means a (possibly non-induced) subgraph copy.
Graph `↪g` would incorrectly require no edges within either large part. -/
def ContainsTripartite (A : Finset ℕ) (l : ℕ) : Prop :=
  ∃ f : tripartiteGraph l →g
      (Erdos883Target.coprimeGraph.induce (A : Set ℕ)),
    Function.Injective f

/-- Precisely the original fixed-`l`, sufficiently-large-`n` second question. -/
def SecondQuestion : Prop :=
  ∀ l : ℕ, 1 ≤ l → ∃ N : ℕ, ∀ n : ℕ, N ≤ n →
    ∀ A : Finset ℕ, A ⊆ Finset.Icc 1 n →
      n / 2 + n / 3 - n / 6 < A.card → ContainsTripartite A l

/-- Concrete evidence: distinct apex, two injectively indexed disjoint parts,
and coprimality across each pair of different parts. -/
structure Witness (A : Finset ℕ) (l : ℕ) where
  apex : ℕ
  left : Fin l → ℕ
  right : Fin l → ℕ
  apex_mem : apex ∈ A
  left_mem : ∀ i, left i ∈ A
  right_mem : ∀ i, right i ∈ A
  left_injective : Function.Injective left
  right_injective : Function.Injective right
  apex_left_ne : ∀ i, apex ≠ left i
  apex_right_ne : ∀ i, apex ≠ right i
  left_right_ne : ∀ i j, left i ≠ right j
  apex_left_coprime : ∀ i, Nat.Coprime apex (left i)
  apex_right_coprime : ∀ i, Nat.Coprime apex (right i)
  left_right_coprime : ∀ i j, Nat.Coprime (left i) (right j)

def Witness.eval {A : Finset ℕ} {l : ℕ} (W : Witness A l) :
    TripartiteVertex l → ℕ
  | .inl _ => W.apex
  | .inr (.inl i) => W.left i
  | .inr (.inr i) => W.right i

theorem Witness.eval_mem {A : Finset ℕ} {l : ℕ} (W : Witness A l)
    (u : TripartiteVertex l) : W.eval u ∈ A := by
  rcases u with u | (i | i)
  · exact W.apex_mem
  · exact W.left_mem i
  · exact W.right_mem i

theorem Witness.eval_injective {A : Finset ℕ} {l : ℕ} (W : Witness A l) :
    Function.Injective W.eval := by
  intro u v h
  rcases u with u | (i | i) <;> rcases v with v | (j | j)
  · exact congrArg Sum.inl (Subsingleton.elim u v)
  · exact False.elim (W.apex_left_ne j h)
  · exact False.elim (W.apex_right_ne j h)
  · exact False.elim (W.apex_left_ne i h.symm)
  · exact congrArg (fun i => Sum.inr (Sum.inl i)) (W.left_injective h)
  · exact False.elim (W.left_right_ne i j h)
  · exact False.elim (W.apex_right_ne i h.symm)
  · exact False.elim (W.left_right_ne j i h.symm)
  · exact congrArg (fun i => Sum.inr (Sum.inr i)) (W.right_injective h)

theorem Witness.eval_coprime {A : Finset ℕ} {l : ℕ} (W : Witness A l)
    {u v : TripartiteVertex l} (h : part u ≠ part v) :
    Nat.Coprime (W.eval u) (W.eval v) := by
  rcases u with u | (i | i) <;> rcases v with v | (j | j)
  · exact False.elim (h rfl)
  · exact W.apex_left_coprime j
  · exact W.apex_right_coprime j
  · exact (W.apex_left_coprime i).symm
  · exact False.elim (h rfl)
  · exact W.left_right_coprime i j
  · exact (W.apex_right_coprime i).symm
  · exact (W.left_right_coprime j i).symm
  · exact False.elim (h rfl)

def Witness.toHom {A : Finset ℕ} {l : ℕ} (W : Witness A l) :
    tripartiteGraph l →g (Erdos883Target.coprimeGraph.induce (A : Set ℕ)) where
  toFun u := ⟨W.eval u, W.eval_mem u⟩
  map_rel' := by
    intro u v huv
    have hp : part u ≠ part v := huv
    have hc := W.eval_coprime hp
    have hn : W.eval u ≠ W.eval v := by
      intro h
      exact hp (congrArg part (W.eval_injective h))
    exact ⟨hn, Or.inl hc⟩

/-- Concrete arithmetic evidence produces the required graph copy. -/
theorem Witness.contains {A : Finset ℕ} {l : ℕ} (W : Witness A l) :
    ContainsTripartite A l := by
  refine ⟨W.toHom, ?_⟩
  intro u v huv
  exact W.eval_injective (congrArg Subtype.val huv)

/-- Extract concrete arithmetic evidence from any injective graph homomorphism. -/
noncomputable def witnessOfContains {A : Finset ℕ} {l : ℕ}
    (h : ContainsTripartite A l) : Witness A l := by
  classical
  let f := h.choose
  have hf := h.choose_spec
  let a : TripartiteVertex l := .inl ()
  let b : Fin l → TripartiteVertex l := fun i => .inr (.inl i)
  let c : Fin l → TripartiteVertex l := fun i => .inr (.inr i)
  have hn {u v : TripartiteVertex l} (huv : u ≠ v) :
      (f u).val ≠ (f v).val := by
    intro he
    exact huv (hf (Subtype.ext he))
  have hc {u v : TripartiteVertex l} (huv : part u ≠ part v) :
      Nat.Coprime (f u).val (f v).val :=
    ((f.map_rel' huv).2).elim id Nat.Coprime.symm
  refine {
    apex := (f a).val
    left := fun i => (f (b i)).val
    right := fun i => (f (c i)).val
    apex_mem := (f a).property
    left_mem := fun i => (f (b i)).property
    right_mem := fun i => (f (c i)).property
    left_injective := ?_
    right_injective := ?_
    apex_left_ne := ?_
    apex_right_ne := ?_
    left_right_ne := ?_
    apex_left_coprime := ?_
    apex_right_coprime := ?_
    left_right_coprime := ?_ }
  · intro i j hij
    have he := hf (Subtype.ext hij)
    simpa [b] using he
  · intro i j hij
    have he := hf (Subtype.ext hij)
    simpa [c] using he
  · intro i; apply hn; simp [a, b]
  · intro i; apply hn; simp [a, c]
  · intro i j; apply hn; simp [b, c]
  · intro i; apply hc; simp [a, b, part]
  · intro i; apply hc; simp [a, c, part]
  · intro i j; apply hc; simp [b, c, part]

theorem contains_iff_witness {A : Finset ℕ} {l : ℕ} :
    ContainsTripartite A l ↔ Nonempty (Witness A l) :=
  ⟨fun h => ⟨witnessOfContains h⟩, fun ⟨W⟩ => W.contains⟩

#print axioms contains_iff_witness

end Erdos883Second
