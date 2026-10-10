import Erdos883SecondLinkCounts
import Mathlib.Tactic.Ring

/-! Explicit finite density thresholds for the independent star argument.
The relation may be directed and may use the same left and right vertex type.
No graph regularity or asymptotic extremal theorem is assumed.
-/

namespace Erdos883Second.Link

open scoped BigOperators

variable {α β : Type*}

theorem high_degree_power_bound_of_no_biclique (L : Finset α) (R H : Finset β)
    (E : α → β → Prop) (l d : ℕ) (hH : H ⊆ R)
    (hdegree : ∀ r ∈ H, d ≤ (neighbors L E r).card)
    (hno : ¬ HasBiclique L R E l) :
    H.card * (d + 1 - l) ^ l ≤ (l - 1) * L.card ^ l := by
  calc
    _ ≤ H.card * d.descFactorial l :=
      Nat.mul_le_mul_left H.card (Nat.pow_sub_le_descFactorial d l)
    _ = l.factorial * (H.card * d.choose l) := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      ring
    _ ≤ l.factorial * ((l - 1) * L.card.choose l) :=
      Nat.mul_le_mul_left l.factorial
        (high_degree_bound_of_no_biclique L R H E l d hH hdegree hno)
    _ = (l - 1) * L.card.descFactorial l := by
      rw [Nat.descFactorial_eq_factorial_mul_choose]
      ring
    _ ≤ _ := Nat.mul_le_mul_left (l - 1) (Nat.descFactorial_le_pow L.card l)

/-- An explicit finite certificate for density at least `1/k`. Bounds on `q`
are supplied separately so integer rounding is visible. It suffices to take
`q = n/(4*k)` once `n` is sufficiently large. -/
theorem biclique_of_dense_relation_certificate (L : Finset α) (R : Finset β)
    (E : α → β → Prop) (n k l q : ℕ)
    (hk : 1 ≤ k) (_hl : 1 ≤ l) (hL : L.card ≤ n) (hR : R.card ≤ n)
    (hq : l ≤ q) (hnlower : 4 * k * q ≤ n) (hnupper : n ≤ 8 * k * q)
    (hqbig : (l - 1) * (8 * k) ^ l < 2 * q)
    (hdense : n * n ≤ k * (∑ r ∈ R, (neighbors L E r).card)) :
    HasBiclique L R E l := by
  classical
  let H := highCenters L R E (2 * q)
  have hHR : H ⊆ R := Finset.filter_subset _ _
  have hHdegree : ∀ r ∈ H, 2 * q ≤ (neighbors L E r).card := by
    intro r hr
    exact (Finset.mem_filter.mp hr).2
  have hqpos : 0 < q := by omega
  have hnpos : 0 < n := by
    have : 0 < 4 * k * q := Nat.mul_pos (by omega) hqpos
    omega
  have hedge : (∑ r ∈ R, (neighbors L E r).card) ≤
      H.card * n + n * (2 * q - 1) := by
    exact (edge_count_le_highCenters L R E (2 * q)).trans
      (Nat.add_le_add (Nat.mul_le_mul_left H.card hL)
        (Nat.mul_le_mul_right _ hR))
  have hcancel : n ≤ k * (H.card + (2 * q - 1)) := by
    have hmul : n * n ≤ n * (k * (H.card + (2 * q - 1))) := by
      calc
        _ ≤ k * (∑ r ∈ R, (neighbors L E r).card) := hdense
        _ ≤ k * (H.card * n + n * (2 * q - 1)) := Nat.mul_le_mul_left k hedge
        _ = _ := by ring
    exact Nat.le_of_mul_le_mul_left hmul hnpos
  have hHcard : 2 * q ≤ H.card := by
    by_contra h
    have hs : H.card + (2 * q - 1) < 4 * q := by omega
    have hm := Nat.mul_lt_mul_of_pos_left hs (by omega : 0 < k)
    have he : k * (4 * q) = 4 * k * q := by ring
    rw [he] at hm
    omega
  by_contra hno
  have hb := high_degree_power_bound_of_no_biclique L R H E l (2 * q)
    hHR hHdegree hno
  have hbase : q ≤ 2 * q + 1 - l := by omega
  have hp : q ^ l ≤ (2 * q + 1 - l) ^ l := Nat.pow_le_pow_left hbase l
  have hbound : (2 * q) * q ^ l ≤ ((l - 1) * (8 * k) ^ l) * q ^ l := by
    calc
      _ ≤ H.card * q ^ l := Nat.mul_le_mul_right _ hHcard
      _ ≤ H.card * (2 * q + 1 - l) ^ l := Nat.mul_le_mul_left _ hp
      _ ≤ (l - 1) * L.card ^ l := hb
      _ ≤ (l - 1) * n ^ l := Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hL l)
      _ ≤ (l - 1) * (8 * k * q) ^ l :=
        Nat.mul_le_mul_left _ (Nat.pow_le_pow_left hnupper l)
      _ = _ := by rw [Nat.mul_pow]; ring
  have hlast : 2 * q ≤ (l - 1) * (8 * k) ^ l :=
    Nat.le_of_mul_le_mul_right hbound (Nat.pow_pos hqpos)
  omega

/-- A uniform explicit threshold for a relation of density at least `1/k`. -/
def denseThreshold (k l : ℕ) : ℕ :=
  4 * k * max l ((l - 1) * (8 * k) ^ l + 1)

theorem biclique_of_dense_relation (L : Finset α) (R : Finset β)
    (E : α → β → Prop) (n k l : ℕ)
    (hk : 1 ≤ k) (hl : 1 ≤ l) (hL : L.card ≤ n) (hR : R.card ≤ n)
    (hn : denseThreshold k l ≤ n)
    (hdense : n * n ≤ k * (∑ r ∈ R, (neighbors L E r).card)) :
    HasBiclique L R E l := by
  let q := n / (4 * k)
  have hkpos : 0 < 4 * k := by omega
  have hqmax : max l ((l - 1) * (8 * k) ^ l + 1) ≤ q := by
    apply (Nat.le_div_iff_mul_le hkpos).mpr
    simpa only [denseThreshold, Nat.mul_comm] using hn
  have hql : l ≤ q := (Nat.le_max_left _ _).trans hqmax
  have hqpos : 0 < q := by omega
  have hnlow : 4 * k * q ≤ n := by
    simpa only [q, Nat.mul_comm] using Nat.div_mul_le_self n (4 * k)
  have hnup : n ≤ 8 * k * q := by
    have hsucc : q + 1 ≤ 2 * q := by omega
    calc
      n ≤ 4 * k * (q + 1) := (Nat.lt_mul_div_succ n hkpos).le
      _ ≤ 4 * k * (2 * q) := Nat.mul_le_mul_left _ hsucc
      _ = _ := by ring
  have hqbig : (l - 1) * (8 * k) ^ l < 2 * q := by
    have hB : (l - 1) * (8 * k) ^ l + 1 ≤ q :=
      (Nat.le_max_right _ _).trans hqmax
    omega
  exact biclique_of_dense_relation_certificate L R E n k l q
    hk hl hL hR hql hnlow hnup hqbig hdense

theorem edge_count_small_of_no_biclique (L : Finset α) (R : Finset β)
    (E : α → β → Prop) (n k l : ℕ)
    (hk : 1 ≤ k) (hl : 1 ≤ l) (hL : L.card ≤ n) (hR : R.card ≤ n)
    (hn : denseThreshold k l ≤ n) (hno : ¬ HasBiclique L R E l) :
    k * (∑ r ∈ R, (neighbors L E r).card) < n * n := by
  by_contra h
  exact hno (biclique_of_dense_relation L R E n k l hk hl hL hR hn (by omega))

#print axioms high_degree_power_bound_of_no_biclique
#print axioms biclique_of_dense_relation_certificate
#print axioms biclique_of_dense_relation
#print axioms edge_count_small_of_no_biclique

end Erdos883Second.Link
