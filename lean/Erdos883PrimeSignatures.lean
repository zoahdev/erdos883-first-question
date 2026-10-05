import Erdos883SortedSignatures

namespace Erdos883Verified

/-- The most significant bit comes first; leading zero bits are allowed. -/
def binarySignatureCode : List Bool → ℕ
  | [] => 0
  | b :: bs => (if b then 1 else 0) * 2 ^ bs.length + binarySignatureCode bs

@[simp] theorem binarySignatureCode_nil : binarySignatureCode [] = 0 := rfl

@[simp] theorem binarySignatureCode_cons (b : Bool) (bs : List Bool) :
    binarySignatureCode (b :: bs) =
      (if b then 1 else 0) * 2 ^ bs.length + binarySignatureCode bs := rfl

/-- Every bit string of length `r` has code strictly less than `2^r`. -/
theorem binarySignatureCode_lt (bs : List Bool) :
    binarySignatureCode bs < 2 ^ bs.length := by
  induction bs with
  | nil => simp
  | cons b bs ih =>
    cases b <;> simp only [binarySignatureCode, List.length_cons,
      Bool.false_eq_true, if_false, if_true, Nat.zero_mul, Nat.zero_add,
      Nat.one_mul, Nat.pow_succ] <;> omega

/-- Concatenation corresponds to shifting the first code past the second. -/
theorem binarySignatureCode_append (xs ys : List Bool) :
    binarySignatureCode (xs ++ ys) =
      binarySignatureCode xs * 2 ^ ys.length + binarySignatureCode ys := by
  induction xs with
  | nil => simp
  | cons b xs ih =>
    simp only [List.cons_append, binarySignatureCode, List.length_append, ih,
      Nat.pow_add, Nat.add_mul, Nat.mul_assoc, Nat.add_assoc]

/-- Taking a prefix is exactly division by the power of two corresponding
 to the omitted suffix, including prefixes longer than the whole string. -/
theorem binarySignatureCode_take (bs : List Bool) (s : ℕ) :
    binarySignatureCode bs / 2 ^ (bs.length - s) =
      binarySignatureCode (bs.take s) := by
  have happ := binarySignatureCode_append (bs.take s) (bs.drop s)
  rw [List.take_append_drop] at happ
  rw [happ, List.length_drop]
  rw [Nat.add_comm, Nat.add_mul_div_right _ _ (Nat.pow_pos (by decide))]
  have hbound := binarySignatureCode_lt (bs.drop s)
  rw [List.length_drop] at hbound
  rw [Nat.div_eq_of_lt hbound, Nat.zero_add]

/-- The code determines all bits when their number is fixed. -/
theorem binarySignatureCode_injective_of_length_eq
    {xs ys : List Bool} (hlen : xs.length = ys.length)
    (hcode : binarySignatureCode xs = binarySignatureCode ys) : xs = ys := by
  induction xs generalizing ys with
  | nil =>
    cases ys with
    | nil => rfl
    | cons b ys => simp at hlen
  | cons b xs ih =>
    cases ys with
    | nil => simp at hlen
    | cons c ys =>
      have htail : xs.length = ys.length := by simpa using hlen
      have hx := binarySignatureCode_lt xs
      have hy := binarySignatureCode_lt ys
      have hhead : b = c := by
        cases b <;> cases c <;> simp_all [binarySignatureCode] <;> omega
      subst c
      have htailcode : binarySignatureCode xs = binarySignatureCode ys := by
        simp only [binarySignatureCode, htail] at hcode
        omega
      rw [ih htail htailcode]

/-- A finite list of divisors records its Boolean divisibility signature.
 No primality or distinctness assumption is needed for the encoding. -/
def divisorSignatureBits (ps : List ℕ) (v : ℕ) : List Bool :=
  ps.map (fun p => decide (p ∣ v))

/-- A numerical encoding of the finite divisibility signature. -/
def divisorSignatureCode (ps : List ℕ) (v : ℕ) : ℕ :=
  binarySignatureCode (divisorSignatureBits ps v)

@[simp] theorem divisorSignatureBits_length (ps : List ℕ) (v : ℕ) :
    (divisorSignatureBits ps v).length = ps.length := by
  simp [divisorSignatureBits]

@[simp] theorem divisorSignatureCode_nil (v : ℕ) :
    divisorSignatureCode [] v = 0 := by
  simp [divisorSignatureCode, divisorSignatureBits]

/-- Divisibility codes have the required uniform bit bound. -/
theorem divisorSignatureCode_lt (ps : List ℕ) (v : ℕ) :
    divisorSignatureCode ps v < 2 ^ ps.length := by
  simpa [divisorSignatureCode] using binarySignatureCode_lt (divisorSignatureBits ps v)

/-- Prefix quotients of the full divisibility code are exactly the codes of
 the corresponding initial lists of divisors. -/
theorem divisorSignatureCode_take (ps : List ℕ) (v s : ℕ) :
    divisorSignatureCode ps v / 2 ^ (ps.length - s) =
      divisorSignatureCode (ps.take s) v := by
  simpa [divisorSignatureCode, divisorSignatureBits, List.map_take]
    using binarySignatureCode_take (divisorSignatureBits ps v) s

/-- Equal codes force equal divisibility by every divisor in the list. -/
theorem divisorSignatureCode_eq_imp_dvd_iff
    (ps : List ℕ) (u v : ℕ)
    (hcode : divisorSignatureCode ps u = divisorSignatureCode ps v)
    {p : ℕ} (hp : p ∈ ps) : (p ∣ u ↔ p ∣ v) := by
  have hbits : divisorSignatureBits ps u = divisorSignatureBits ps v :=
    binarySignatureCode_injective_of_length_eq (by simp) hcode
  have hdecide : decide (p ∣ u) = decide (p ∣ v) := by
    exact List.map_eq_map_iff.mp hbits p hp
  simpa only [decide_eq_decide] using hdecide

/-- Equality of codes is equivalent to equality of every recorded
 divisibility predicate, including repeated divisors. -/
theorem divisorSignatureCode_eq_iff (ps : List ℕ) (u v : ℕ) :
    divisorSignatureCode ps u = divisorSignatureCode ps v ↔
      ∀ p ∈ ps, (p ∣ u ↔ p ∣ v) := by
  constructor
  · intro h p hp
    exact divisorSignatureCode_eq_imp_dvd_iff ps u v h hp
  · intro h
    unfold divisorSignatureCode divisorSignatureBits
    congr 1
    apply List.map_congr_left
    intro p hp
    exact decide_eq_decide.mpr (h p hp)

/-- Equal prefix quotients are precisely matching divisibility signatures
 on the first `s` divisors. -/
theorem divisorSignatureCode_prefix_eq_iff (ps : List ℕ) (u v s : ℕ) :
    divisorSignatureCode ps u / 2 ^ (ps.length - s) =
        divisorSignatureCode ps v / 2 ^ (ps.length - s) ↔
      ∀ p ∈ ps.take s, (p ∣ u ↔ p ∣ v) := by
  rw [divisorSignatureCode_take, divisorSignatureCode_take,
    divisorSignatureCode_eq_iff]

/-- In particular, equal prefix quotients match the divisibility predicate
 at every indexed position in the first `s` entries. -/
theorem divisorSignatureCode_prefix_eq_imp_index_dvd_iff
    (ps : List ℕ) (u v s : ℕ)
    (hcode : divisorSignatureCode ps u / 2 ^ (ps.length - s) =
      divisorSignatureCode ps v / 2 ^ (ps.length - s))
    (i : ℕ) (hi : i < s) (hip : i < ps.length) :
    (ps[i] ∣ u ↔ ps[i] ∣ v) := by
  apply (divisorSignatureCode_prefix_eq_iff ps u v s).mp hcode
  exact List.mem_take_iff_getElem.mpr ⟨i, by omega, rfl⟩

/-- The one ordering by complete divisibility signatures gives the sharp
 sorted transition bound for every initial divisor list simultaneously. -/
theorem divisorSignatureOrder_all_prefix_bounds (ps xs : List ℕ) :
    ∀ s ≤ ps.length, signatureTransitions
      ((fullSignatureOrder (divisorSignatureCode ps) xs).map
        (divisorSignatureCode (ps.take s))) ≤ 2 ^ s - 1 := by
  have h := fullSignatureOrder_binaryPrefix_bounds (divisorSignatureCode ps)
    xs ps.length (fun v _ => divisorSignatureCode_lt ps v)
  simpa only [divisorSignatureCode_take] using h

/-- Moving two entries of the full-signature order to the endpoints preserves
 every prefix bound, now with at most two additional transitions. -/
theorem divisorSignatureCode_move_endpoints_le
    (ps xs ys zs : List ℕ) (a b : ℕ)
    (hsorted : (xs ++ a :: (ys ++ b :: zs)).Pairwise
      (fun u v => divisorSignatureCode ps u ≤ divisorSignatureCode ps v)) :
    ∀ s ≤ ps.length, signatureTransitions
      ((a :: ((xs ++ ys ++ zs) ++ [b])).map
        (divisorSignatureCode (ps.take s))) ≤ 2 ^ s + 1 := by
  have h := binaryPrefixQuotient_move_endpoints_le (divisorSignatureCode ps)
    xs ys zs a b ps.length hsorted (fun v _ => divisorSignatureCode_lt ps v)
  simpa only [divisorSignatureCode_take] using h

/-- The empty divisor prefix causes no transitions in any vertex order. -/
theorem divisorSignatureCode_zeroPrefix_transitions_eq_zero
    (ps xs : List ℕ) :
    signatureTransitions (xs.map (divisorSignatureCode (ps.take 0))) = 0 := by
  change signatureTransitions (xs.map (fun _ => 0)) = 0
  rw [List.map_const', signatureTransitions_replicate]

#print axioms binarySignatureCode_nil
#print axioms binarySignatureCode_cons
#print axioms binarySignatureCode_lt
#print axioms binarySignatureCode_append
#print axioms binarySignatureCode_take
#print axioms binarySignatureCode_injective_of_length_eq
#print axioms divisorSignatureBits_length
#print axioms divisorSignatureCode_nil
#print axioms divisorSignatureCode_lt
#print axioms divisorSignatureCode_take
#print axioms divisorSignatureCode_eq_imp_dvd_iff
#print axioms divisorSignatureCode_eq_iff
#print axioms divisorSignatureCode_prefix_eq_iff
#print axioms divisorSignatureCode_prefix_eq_imp_index_dvd_iff
#print axioms divisorSignatureOrder_all_prefix_bounds
#print axioms divisorSignatureCode_move_endpoints_le
#print axioms divisorSignatureCode_zeroPrefix_transitions_eq_zero

end Erdos883Verified
