import Erdos883SmallCertificateHelpers
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder55 : List ℕ := [1, 53, 47, 43, 41, 37, 31, 29, 23, 19, 17, 13, 11, 7, 49, 5, 25, 55, 35, 3, 9, 27, 51, 39, 33, 21, 15, 45]
theorem smallOrder55_nodup : smallOrder55.Nodup := by decide +kernel
theorem smallOrder55_set : smallOrder55.toFinset = oddUniverse 55 := by decide +kernel

private def resources55 (i : Fin 12) : PrefixResourceData :=
  match i.val with
  | 0 => ⟨28, 0, 9, true⟩
  | 1 => ⟨24, 0, 10, true⟩
  | 2 => ⟨22, 0, 11, true⟩
  | 3 => ⟨23, 1, 15, true⟩
  | 4 => ⟨19, 0, 15, true⟩
  | 5 => ⟨17, 0, 17, true⟩
  | 6 => ⟨15, 0, 20, true⟩
  | 7 => ⟨13, 0, 22, true⟩
  | 8 => ⟨12, 0, 23, true⟩
  | 9 => ⟨9, 0, 24, true⟩
  | 10 => ⟨8, 0, 25, true⟩
  | _ => ⟨7, 0, 48, false⟩

private theorem validResource55_0 :
    PrefixResourceValid 50 smallOrder55 [3, 5, 7, 11] (resources55 0) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource55_1 :
    PrefixResourceValid 50 smallOrder55 [3, 5, 7, 11] (resources55 1) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource55_2 :
    PrefixResourceValid 50 smallOrder55 [3, 5, 7, 11] (resources55 2) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource55_3 :
    PrefixResourceValid 50 smallOrder55 [3, 5, 7, 11] (resources55 3) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource55_4 :
    PrefixResourceValid 50 smallOrder55 [3, 5, 7, 11] (resources55 4) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource55_5 :
    PrefixResourceValid 50 smallOrder55 [3, 5, 7, 11] (resources55 5) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource55_6 :
    PrefixResourceValid 50 smallOrder55 [3, 5, 7, 11] (resources55 6) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource55_7 :
    PrefixResourceValid 50 smallOrder55 [3, 5, 7, 11] (resources55 7) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource55_8 :
    PrefixResourceValid 50 smallOrder55 [3, 5, 7, 11] (resources55 8) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource55_9 :
    PrefixResourceValid 50 smallOrder55 [3, 5, 7, 11] (resources55 9) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource55_10 :
    PrefixResourceValid 50 smallOrder55 [3, 5, 7, 11] (resources55 10) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private theorem validResource55_11 :
    PrefixResourceValid 50 smallOrder55 [3, 5, 7, 11] (resources55 11) := by
  unfold PrefixResourceValid prefixResourceBound
  decide +kernel

private def resourceSelector55_0 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 0
  | 7 => 0
  | _ => 1

private theorem resourceRequirements50_55_b0 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 0 (j.val + 1)
      (resources55 (resourceSelector55_0 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_1 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 0
  | 5 => 0
  | 6 => 1
  | 7 => 1
  | _ => 1

private theorem resourceRequirements50_55_b1 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 1 (j.val + 1)
      (resources55 (resourceSelector55_1 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_2 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 0
  | 3 => 0
  | 4 => 1
  | 5 => 1
  | 6 => 1
  | 7 => 1
  | _ => 2

private theorem resourceRequirements50_55_b2 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 2 (j.val + 1)
      (resources55 (resourceSelector55_2 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_3 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 0
  | 1 => 0
  | 2 => 1
  | 3 => 1
  | 4 => 1
  | 5 => 1
  | 6 => 2
  | 7 => 2
  | _ => 3

private theorem resourceRequirements50_55_b3 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 3 (j.val + 1)
      (resources55 (resourceSelector55_3 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_4 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => 1
  | 3 => 1
  | 4 => 2
  | 5 => 2
  | 6 => 2
  | 7 => 3
  | _ => 3

private theorem resourceRequirements50_55_b4 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 4 (j.val + 1)
      (resources55 (resourceSelector55_4 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_5 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 1
  | 1 => 1
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 2
  | 6 => 3
  | 7 => 3
  | _ => 4

private theorem resourceRequirements50_55_b5 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 5 (j.val + 1)
      (resources55 (resourceSelector55_5 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_6 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 2
  | 5 => 3
  | 6 => 4
  | 7 => 4
  | _ => 4

private theorem resourceRequirements50_55_b6 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 6 (j.val + 1)
      (resources55 (resourceSelector55_6 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_7 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 2
  | 1 => 2
  | 2 => 2
  | 3 => 2
  | 4 => 4
  | 5 => 4
  | 6 => 4
  | 7 => 4
  | _ => 5

private theorem resourceRequirements50_55_b7 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 7 (j.val + 1)
      (resources55 (resourceSelector55_7 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_8 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 2
  | 1 => 2
  | 2 => 4
  | 3 => 4
  | 4 => 4
  | 5 => 4
  | 6 => 5
  | 7 => 5
  | _ => 5

private theorem resourceRequirements50_55_b8 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 8 (j.val + 1)
      (resources55 (resourceSelector55_8 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_9 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 4
  | 1 => 4
  | 2 => 4
  | 3 => 4
  | 4 => 5
  | 5 => 5
  | 6 => 5
  | 7 => 5
  | _ => 6

private theorem resourceRequirements50_55_b9 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 9 (j.val + 1)
      (resources55 (resourceSelector55_9 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_10 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 4
  | 1 => 4
  | 2 => 5
  | 3 => 5
  | 4 => 5
  | 5 => 5
  | 6 => 6
  | 7 => 6
  | _ => 6

private theorem resourceRequirements50_55_b10 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 10 (j.val + 1)
      (resources55 (resourceSelector55_10 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_11 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 5
  | 3 => 5
  | 4 => 6
  | 5 => 6
  | 6 => 6
  | 7 => 6
  | _ => 7

private theorem resourceRequirements50_55_b11 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 11 (j.val + 1)
      (resources55 (resourceSelector55_11 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_12 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 5
  | 1 => 5
  | 2 => 6
  | 3 => 6
  | 4 => 6
  | 5 => 6
  | 6 => 7
  | 7 => 7
  | _ => 8

private theorem resourceRequirements50_55_b12 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 12 (j.val + 1)
      (resources55 (resourceSelector55_12 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_13 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 6
  | 1 => 6
  | 2 => 6
  | 3 => 6
  | 4 => 7
  | 5 => 7
  | 6 => 8
  | 7 => 8
  | _ => 8

private theorem resourceRequirements50_55_b13 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 13 (j.val + 1)
      (resources55 (resourceSelector55_13 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_14 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 6
  | 1 => 6
  | 2 => 7
  | 3 => 7
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | 7 => 8
  | _ => 8

private theorem resourceRequirements50_55_b14 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 14 (j.val + 1)
      (resources55 (resourceSelector55_14 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_15 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 7
  | 1 => 7
  | 2 => 8
  | 3 => 8
  | 4 => 8
  | 5 => 8
  | 6 => 8
  | 7 => 8
  | _ => 9

private theorem resourceRequirements50_55_b15 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 15 (j.val + 1)
      (resources55 (resourceSelector55_15 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_16 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 8
  | 1 => 8
  | 2 => 8
  | 3 => 8
  | 4 => 8
  | 5 => 8
  | 6 => 9
  | 7 => 9
  | _ => 10

private theorem resourceRequirements50_55_b16 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 16 (j.val + 1)
      (resources55 (resourceSelector55_16 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_17 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 8
  | 1 => 8
  | 2 => 8
  | 3 => 8
  | 4 => 9
  | 5 => 9
  | 6 => 10
  | 7 => 10
  | _ => 11

private theorem resourceRequirements50_55_b17 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 17 (j.val + 1)
      (resources55 (resourceSelector55_17 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55_18 (j : Fin 9) : Fin 12 :=
  match j.val with
  | 0 => 8
  | 1 => 8
  | 2 => 9
  | 3 => 9
  | 4 => 10
  | 5 => 10
  | 6 => 10
  | 7 => 11
  | _ => 11

private theorem resourceRequirements50_55_b18 :
    ∀ j : Fin 9, ResourceRequirements 55 [3, 5, 7, 11] 18 (j.val + 1)
      (resources55 (resourceSelector55_18 j)) := by
  unfold ResourceRequirements
  decide +kernel

private def resourceSelector55 (b : Fin 19) (j : Fin 9) : Fin 12 :=
  match b.val with
  | 0 => resourceSelector55_0 j
  | 1 => resourceSelector55_1 j
  | 2 => resourceSelector55_2 j
  | 3 => resourceSelector55_3 j
  | 4 => resourceSelector55_4 j
  | 5 => resourceSelector55_5 j
  | 6 => resourceSelector55_6 j
  | 7 => resourceSelector55_7 j
  | 8 => resourceSelector55_8 j
  | 9 => resourceSelector55_9 j
  | 10 => resourceSelector55_10 j
  | 11 => resourceSelector55_11 j
  | 12 => resourceSelector55_12 j
  | 13 => resourceSelector55_13 j
  | 14 => resourceSelector55_14 j
  | 15 => resourceSelector55_15 j
  | 16 => resourceSelector55_16 j
  | 17 => resourceSelector55_17 j
  | _ => resourceSelector55_18 j

theorem finiteCheck50_55 : finiteIntervalCheck 50 55 smallOrder55 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 50) (U := 55) (O := smallOrder55) (ps := [3, 5, 7, 11]) resources55 resourceSelector55
  · intro i
    fin_cases i
    · exact validResource55_0
    · exact validResource55_1
    · exact validResource55_2
    · exact validResource55_3
    · exact validResource55_4
    · exact validResource55_5
    · exact validResource55_6
    · exact validResource55_7
    · exact validResource55_8
    · exact validResource55_9
    · exact validResource55_10
    · exact validResource55_11
  · intro b j
    fin_cases b
    · exact resourceRequirements50_55_b0 j
    · exact resourceRequirements50_55_b1 j
    · exact resourceRequirements50_55_b2 j
    · exact resourceRequirements50_55_b3 j
    · exact resourceRequirements50_55_b4 j
    · exact resourceRequirements50_55_b5 j
    · exact resourceRequirements50_55_b6 j
    · exact resourceRequirements50_55_b7 j
    · exact resourceRequirements50_55_b8 j
    · exact resourceRequirements50_55_b9 j
    · exact resourceRequirements50_55_b10 j
    · exact resourceRequirements50_55_b11 j
    · exact resourceRequirements50_55_b12 j
    · exact resourceRequirements50_55_b13 j
    · exact resourceRequirements50_55_b14 j
    · exact resourceRequirements50_55_b15 j
    · exact resourceRequirements50_55_b16 j
    · exact resourceRequirements50_55_b17 j
    · exact resourceRequirements50_55_b18 j

theorem exactCertificate50_55 : ExactIntervalCertificate 50 55 smallOrder55 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck50_55
#print axioms smallOrder55_nodup
#print axioms smallOrder55_set
#print axioms finiteCheck50_55
#print axioms exactCertificate50_55
end Erdos883Verified
