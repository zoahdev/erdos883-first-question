import Erdos883AdaptiveCertificateCore
import Erdos883DegreeCriterion
namespace Erdos883Verified

theorem AdaptiveMinTree.cache_sound {t : AdaptiveMinTree} (h : t.cacheCheck = true) :
    ∀ iv ∈ t.entries, t.low ≤ iv.1 ∧ iv.1 ≤ t.high ∧ t.minimum ≤ iv.2 := by
  induction t with
  | leaf i v =>
      intro iv hiv
      simp only [entries, List.mem_singleton] at hiv
      subst iv
      exact ⟨le_rfl, le_rfl, le_rfl⟩
  | node lo hi m l r hl hr =>
      simp only [cacheCheck, Bool.and_eq_true, decide_eq_true_eq] at h
      rcases h with ⟨⟨hc, hlc⟩, hrc⟩
      intro iv hiv
      simp only [entries, List.mem_append] at hiv
      rcases hiv with hiv | hiv
      · obtain ⟨hlo,hhi,hm⟩ := hl hlc iv hiv
        exact ⟨hc.1.trans hlo, hhi.trans hc.2.2.1, hc.2.2.2.2.1.trans hm⟩
      · obtain ⟨hlo,hhi,hm⟩ := hr hrc iv hiv
        exact ⟨hc.2.1.trans hlo, hhi.trans hc.2.2.2.1, hc.2.2.2.2.2.trans hm⟩

theorem AdaptiveMinTree.rangeGe_sound {t : AdaptiveMinTree} (hc : t.cacheCheck = true)
    {lo hi bound : Nat} (h : t.rangeGe lo hi bound = true) :
    ∀ iv ∈ t.entries, lo ≤ iv.1 → iv.1 ≤ hi → bound ≤ iv.2 := by
  induction t with
  | leaf i v =>
      intro iv hiv hlo hhi
      simp only [entries, List.mem_singleton] at hiv
      subst iv
      change decide (hi < i ∨ i < lo ∨ bound ≤ v) = true at h
      have hx := of_decide_eq_true h
      omega
  | node lidx hidx m l r hl hr =>
      intro iv hiv hlo hhi
      by_cases hx : hi < lidx ∨ hidx < lo ∨ bound ≤ m
      · obtain ⟨htlo,hthi,htm⟩ := cache_sound hc iv hiv
        simp only [low, high, minimum] at htlo hthi htm
        omega
      · simp only [rangeGe, low, high, minimum, hx, ↓reduceIte, Bool.and_eq_true] at h
        simp only [cacheCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
        simp only [entries, List.mem_append] at hiv
        rcases hiv with hiv | hiv
        · exact hl hc.1.2 h.1 iv hiv hlo hhi
        · exact hr hc.2 h.2 iv hiv hlo hhi

/-- Arithmetic behind the compressed split witness. -/
theorem adaptiveRankWitnessCheck_sound
    {H bmax D j h : Nat} {w : AdaptiveRankWitness} {even whole : AdaptiveMinTree}
    (hcE : even.cacheCheck = true) (hcR : whole.cacheCheck = true)
    (hc : adaptiveRankWitnessCheck H bmax D j h w even whole = true)
    {b : Nat} (hb : b ≤ bmax)
    {e r : Nat}
    (hE : (b + (j-h-1)/2, e + H - (b + (j-h-1)/2)) ∈ even.entries)
    (hR : (w.split + (j-h-1)/2, r) ∈ whole.entries)
    (hrank : b + (j-h-1)/2 ≤ H) :
    h < j ∧ (b < w.split → b+j ≤ e) ∧ (w.split ≤ b → D+j ≤ r) := by
  simp only [adaptiveRankWitnessCheck, Bool.and_eq_true, decide_eq_true_eq] at hc
  rcases hc with ⟨⟨hh, hs⟩, he, hr⟩
  refine ⟨hh, ?_, ?_⟩
  · intro hbs
    have hs0 : w.split ≠ 0 := by omega
    simp only [hs0, ↓reduceIte] at he
    have hge := even.rangeGe_sound hcE he _ hE (by omega) (by omega)
    omega
  · intro hsb
    have hneq : w.split ≠ bmax+1 := by omega
    simp only [hneq, ↓reduceIte] at hr
    have hge := whole.rangeGe_sound hcR hr _ hR (by omega) (by omega)
    exact hge
end Erdos883Verified
