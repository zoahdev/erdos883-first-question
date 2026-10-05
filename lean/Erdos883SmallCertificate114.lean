import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate114OrderCheck
import Erdos883SmallCertificate114Metadata000
import Erdos883SmallCertificate114Resource000
import Erdos883SmallCertificate114Resource001
import Erdos883SmallCertificate114Resource002
import Erdos883SmallCertificate114Resource003
import Erdos883SmallCertificate114Resource004
import Erdos883SmallCertificate114Resource005
import Erdos883SmallCertificate114Resource006
import Erdos883SmallCertificate114Resource007
import Erdos883SmallCertificate114Resource008
import Erdos883SmallCertificate114Resource009
import Erdos883SmallCertificate114Resource010
import Erdos883SmallCertificate114Resource011
import Erdos883SmallCertificate114Resource012
import Erdos883SmallCertificate114Resource013
import Erdos883SmallCertificate114Resource014
import Erdos883SmallCertificate114Resource015
import Erdos883SmallCertificate114Resource016
import Erdos883SmallCertificate114Resource017
import Erdos883SmallCertificate114Resource018
import Erdos883SmallCertificate114Resource019Chunk000
import Erdos883SmallCertificate114Resource019Chunk001
import Erdos883SmallCertificate114Resource019Chunk002
import Erdos883SmallCertificate114Resource019
import Erdos883SmallCertificate114Resource020Chunk000
import Erdos883SmallCertificate114Resource020Chunk001
import Erdos883SmallCertificate114Resource020Chunk002
import Erdos883SmallCertificate114Resource020
import Erdos883SmallCertificate114Resource021
import Erdos883SmallCertificate114Resource022
import Erdos883SmallCertificate114Resource023
import Erdos883SmallCertificate114Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder114 : List ℕ := coreData114.map (·.value)
theorem smallOrder114_nodup : smallOrder114.Nodup := (coreOrderPermutationCheck_sound coreOrderCheck114).1
theorem smallOrder114_set : smallOrder114.toFinset = oddUniverse 114 := (coreOrderPermutationCheck_sound coreOrderCheck114).2
private def resources114 (i : Fin 24) : PrefixResourceData := resourceOfCore (coreResources114 i)
private theorem dataValid114 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData114.map oddDataOfCore) := by
  apply oddCertificateDataValid_of_coreChunks coreMetadataChunks114 coreMetadataFlatten114
  intro c
  fin_cases c
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck114_0
#print axioms dataValid114

private theorem validResource114_0 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 0) 0 102
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 104 smallOrder114 [3, 5, 7, 11] 0 102 false) coreChunks114_0 coreFlatten114_0 coreCheck114_0

private theorem validResource114_1 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 1) 0 52
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 104 smallOrder114 [3, 5, 7, 11] 0 52 true) coreChunks114_1 coreFlatten114_1 coreCheck114_1

private theorem validResource114_2 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 2) 16 52
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_1 coreChunks114_2 coreFlatten114_2 coreCheck114_2

private theorem validResource114_3 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 3) 17 51
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_2 coreChunks114_3 coreFlatten114_3 coreCheck114_3

private theorem validResource114_4 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 4) 22 50
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_3 coreChunks114_4 coreFlatten114_4 coreCheck114_4

private theorem validResource114_5 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 5) 23 49
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_4 coreChunks114_5 coreFlatten114_5 coreCheck114_5

private theorem validResource114_6 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 6) 24 48
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_5 coreChunks114_6 coreFlatten114_6 coreCheck114_6

private theorem validResource114_7 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 7) 25 47
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_6 coreChunks114_7 coreFlatten114_7 coreCheck114_7

private theorem validResource114_8 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 8) 26 45
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_7 coreChunks114_8 coreFlatten114_8 coreCheck114_8

private theorem validResource114_9 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 9) 27 44
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_8 coreChunks114_9 coreFlatten114_9 coreCheck114_9

private theorem validResource114_10 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 10) 29 41
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_9 coreChunks114_10 coreFlatten114_10 coreCheck114_10

private theorem validResource114_11 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 11) 31 36
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_10 coreChunks114_11 coreFlatten114_11 coreCheck114_11

private theorem validResource114_12 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 12) 33 32
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_11 coreChunks114_12 coreFlatten114_12 coreCheck114_12

private theorem validResource114_13 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 13) 34 30
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_12 coreChunks114_13 coreFlatten114_13 coreCheck114_13

private theorem validResource114_14 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 14) 35 29
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_13 coreChunks114_14 coreFlatten114_14 coreCheck114_14

private theorem validResource114_15 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 15) 38 28
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_14 coreChunks114_15 coreFlatten114_15 coreCheck114_15

private theorem validResource114_16 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 16) 42 24
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_15 coreChunks114_16 coreFlatten114_16 coreCheck114_16

private theorem validResource114_17 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 17) 45 23
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_16 coreChunks114_17 coreFlatten114_17 coreCheck114_17

private theorem validResource114_18 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 18) 48 22
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_17 coreChunks114_18 coreFlatten114_18 coreCheck114_18

private theorem validResource114_19 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 19) 0 28
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 104 smallOrder114 [3, 5, 7, 11] 1 28 true) coreChunks114_19 coreFlatten114_19 coreCheck114_19

private theorem validResource114_20 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 20) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 20) 0 37
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 104 smallOrder114 [3, 5, 7, 11] 2 37 true) coreChunks114_20 coreFlatten114_20 coreCheck114_20

private theorem validResource114_21 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 21) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 21) 35 37
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_20 coreChunks114_21 coreFlatten114_21 coreCheck114_21

private theorem validResource114_22 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 22) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 22) 36 35
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_21 coreChunks114_22 coreFlatten114_22 coreCheck114_22

private theorem validResource114_23 :
    PrefixResourceValid 104 smallOrder114 [3, 5, 7, 11] (resources114 23) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 104) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) (r := coreResources114 23) 37 34
    dataValid114 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource114_22 coreChunks114_23 coreFlatten114_23 coreCheck114_23

theorem finiteCheck104_114 : finiteIntervalCheck 104 114 smallOrder114 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 104) (U := 114) (O := smallOrder114)
    (ps := [3, 5, 7, 11]) resources114 coreSelector114
  · intro i
    fin_cases i
    · exact validResource114_0
    · exact validResource114_1
    · exact validResource114_2
    · exact validResource114_3
    · exact validResource114_4
    · exact validResource114_5
    · exact validResource114_6
    · exact validResource114_7
    · exact validResource114_8
    · exact validResource114_9
    · exact validResource114_10
    · exact validResource114_11
    · exact validResource114_12
    · exact validResource114_13
    · exact validResource114_14
    · exact validResource114_15
    · exact validResource114_16
    · exact validResource114_17
    · exact validResource114_18
    · exact validResource114_19
    · exact validResource114_20
    · exact validResource114_21
    · exact validResource114_22
    · exact validResource114_23
  · intro b j
    exact resourceRequirements_of_core (coreRequirements114_0 b j)


theorem exactCertificate104_114 : ExactIntervalCertificate 104 114 smallOrder114 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck104_114
#print axioms smallOrder114_nodup
#print axioms smallOrder114_set
#print axioms finiteCheck104_114
#print axioms exactCertificate104_114
end Erdos883Verified
