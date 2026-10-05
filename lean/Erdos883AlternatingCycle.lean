import Erdos883CycleWitness

namespace Erdos883Verified

/-- The alternating enumeration of a skeleton and its intermediate vertices. -/
def alternatingVertex {V : Type*} {k : ℕ}
    (o : Fin (k + 1) → V) (w : Fin k → V) (i : Fin (2 * k + 1)) : V :=
  if h : i.val % 2 = 0 then
    o ⟨i.val / 2, by omega⟩
  else
    w ⟨i.val / 2, by omega⟩

theorem alternatingVertex_injective {V : Type*} {k : ℕ}
    (o : Fin (k + 1) → V) (w : Fin k → V)
    (ho : Function.Injective o) (hw : Function.Injective w)
    (hd : ∀ i j, o i ≠ w j) :
    Function.Injective (alternatingVertex o w) := by
  intro i j hij
  unfold alternatingVertex at hij
  split_ifs at hij with hi hj hj
  · have he := congrArg Fin.val (ho hij)
    apply Fin.ext
    dsimp at he
    omega
  · exact False.elim (hd _ _ hij)
  · exact False.elim (hd _ _ hij.symm)
  · have he := congrArg Fin.val (hw hij)
    apply Fin.ext
    dsimp at he
    omega

theorem alternatingVertex_successors {V : Type*} (G : SimpleGraph V)
    {k : ℕ} (hk : 1 ≤ k) (o : Fin (k + 1) → V) (w : Fin k → V)
    (hl : ∀ i, G.Adj (w i) (o i.castSucc))
    (hr : ∀ i, G.Adj (w i) (o i.succ))
    (hc : G.Adj (o (Fin.last k)) (o 0)) :
    ∀ i, G.Adj (alternatingVertex o w i) (alternatingVertex o w (i + 1)) := by
  intro i
  have hone : (1 : Fin (2 * k + 1)).val = 1 := by
    change 1 % (2 * k + 1) = 1
    exact Nat.mod_eq_of_lt (by omega)
  by_cases hlt : i.val + 1 < 2 * k + 1
  · have hs : (i + 1).val = i.val + 1 := by
      simpa only [hone] using
        (Fin.val_add_eq_of_add_lt (a := i) (b := 1) (by simpa only [hone] using hlt))
    by_cases hi : i.val % 2 = 0
    · have hj : (i + 1).val % 2 ≠ 0 := by omega
      let q : Fin k := ⟨i.val / 2, by omega⟩
      have fi : alternatingVertex o w i = o q.castSucc := by
        simp only [alternatingVertex, hi, dite_true]
        rfl
      have fj : alternatingVertex o w (i + 1) = w q := by
        simp only [alternatingVertex, hj, dite_false]
        congr 1
        apply Fin.ext
        dsimp [q]
        omega
      rw [fi, fj]
      exact (hl q).symm
    · have hj : (i + 1).val % 2 = 0 := by omega
      let q : Fin k := ⟨i.val / 2, by omega⟩
      have fi : alternatingVertex o w i = w q := by
        simp only [alternatingVertex, hi, dite_false]
        rfl
      have fj : alternatingVertex o w (i + 1) = o q.succ := by
        simp only [alternatingVertex, hj, dite_true]
        congr 1
        apply Fin.ext
        dsimp [q]
        omega
      rw [fi, fj]
      exact hr q
  · have hi : i.val = 2 * k := by omega
    have hs : (i + 1).val = 0 := by
      rw [Fin.val_add_eq_ite, hone]
      split_ifs <;> omega
    have hp : i.val % 2 = 0 := by omega
    have hj : (i + 1).val % 2 = 0 := by omega
    have fi : alternatingVertex o w i = o (Fin.last k) := by
      simp only [alternatingVertex, hp, dite_true]
      congr 1
      apply Fin.ext
      dsimp
      omega
    have fj : alternatingVertex o w (i + 1) = o 0 := by
      simp only [alternatingVertex, hj, dite_true]
      congr 1
      apply Fin.ext
      dsimp
      omega
    rw [fi, fj]
    exact hc

/-- An injective skeleton, disjoint injective connectors, and a closing edge form
an odd cycle of exactly `2 * k + 1` edges. -/
theorem oddCycleLength_of_alternating {V : Type*} (G : SimpleGraph V)
    {k : ℕ} (hk : 1 ≤ k) (o : Fin (k + 1) → V) (w : Fin k → V)
    (ho : Function.Injective o) (hw : Function.Injective w)
    (hd : ∀ i j, o i ≠ w j)
    (hl : ∀ i, G.Adj (w i) (o i.castSucc))
    (hr : ∀ i, G.Adj (w i) (o i.succ))
    (hc : G.Adj (o (Fin.last k)) (o 0)) :
    2 * k + 1 ∈ G.oddCycleLengths := by
  apply oddCycleLength_of_injective_successors G (by omega) ⟨k, by omega⟩
    (alternatingVertex o w)
  · exact alternatingVertex_injective o w ho hw hd
  · exact alternatingVertex_successors G hk o w hl hr hc

#print axioms alternatingVertex
#print axioms oddCycleLength_of_alternating
#print axioms alternatingVertex_injective
#print axioms alternatingVertex_successors

end Erdos883Verified
