import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate93OrderCheck
import Erdos883SmallCertificate93Metadata000
import Erdos883SmallCertificate93Resource000
import Erdos883SmallCertificate93Resource001
import Erdos883SmallCertificate93Resource002
import Erdos883SmallCertificate93Resource003
import Erdos883SmallCertificate93Resource004
import Erdos883SmallCertificate93Resource005
import Erdos883SmallCertificate93Resource006
import Erdos883SmallCertificate93Resource007
import Erdos883SmallCertificate93Resource008
import Erdos883SmallCertificate93Resource009
import Erdos883SmallCertificate93Resource010
import Erdos883SmallCertificate93Resource011
import Erdos883SmallCertificate93Resource012
import Erdos883SmallCertificate93Resource013
import Erdos883SmallCertificate93Resource014
import Erdos883SmallCertificate93Resource015
import Erdos883SmallCertificate93Resource016
import Erdos883SmallCertificate93Resource017Chunk000
import Erdos883SmallCertificate93Resource017Chunk001
import Erdos883SmallCertificate93Resource017Chunk002
import Erdos883SmallCertificate93Resource017
import Erdos883SmallCertificate93Resource018
import Erdos883SmallCertificate93Resource019
import Erdos883SmallCertificate93Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder93 : List ℕ := coreData93.map (·.value)
theorem smallOrder93_nodup : smallOrder93.Nodup := (coreOrderPermutationCheck_sound coreOrderCheck93).1
theorem smallOrder93_set : smallOrder93.toFinset = oddUniverse 93 := (coreOrderPermutationCheck_sound coreOrderCheck93).2
private def resources93 (i : Fin 20) : PrefixResourceData := resourceOfCore (coreResources93 i)
private theorem dataValid93 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData93.map oddDataOfCore) := by
  apply oddCertificateDataValid_of_coreChunks coreMetadataChunks93 coreMetadataFlatten93
  intro c
  fin_cases c
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck93_0
#print axioms dataValid93

private theorem validResource93_0 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 0) 0 46
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 93 smallOrder93 [3, 5, 7, 11] 0 46 true) coreChunks93_0 coreFlatten93_0 coreCheck93_0

private theorem validResource93_1 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 1) 11 46
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_0 coreChunks93_1 coreFlatten93_1 coreCheck93_1

private theorem validResource93_2 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 2) 12 45
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_1 coreChunks93_2 coreFlatten93_2 coreCheck93_2

private theorem validResource93_3 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 3) 16 44
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_2 coreChunks93_3 coreFlatten93_3 coreCheck93_3

private theorem validResource93_4 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 4) 17 43
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_3 coreChunks93_4 coreFlatten93_4 coreCheck93_4

private theorem validResource93_5 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 5) 19 42
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_4 coreChunks93_5 coreFlatten93_5 coreCheck93_5

private theorem validResource93_6 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 6) 20 41
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_5 coreChunks93_6 coreFlatten93_6 coreCheck93_6

private theorem validResource93_7 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 7) 21 39
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_6 coreChunks93_7 coreFlatten93_7 coreCheck93_7

private theorem validResource93_8 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 8) 23 36
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_7 coreChunks93_8 coreFlatten93_8 coreCheck93_8

private theorem validResource93_9 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 9) 25 32
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_8 coreChunks93_9 coreFlatten93_9 coreCheck93_9

private theorem validResource93_10 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 10) 26 29
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_9 coreChunks93_10 coreFlatten93_10 coreCheck93_10

private theorem validResource93_11 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 11) 27 28
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_10 coreChunks93_11 coreFlatten93_11 coreCheck93_11

private theorem validResource93_12 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 12) 28 26
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_11 coreChunks93_12 coreFlatten93_12 coreCheck93_12

private theorem validResource93_13 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 13) 31 25
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_12 coreChunks93_13 coreFlatten93_13 coreCheck93_13

private theorem validResource93_14 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 14) 35 22
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_13 coreChunks93_14 coreFlatten93_14 coreCheck93_14

private theorem validResource93_15 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 15) 37 21
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_14 coreChunks93_15 coreFlatten93_15 coreCheck93_15

private theorem validResource93_16 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 16) 41 20
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_15 coreChunks93_16 coreFlatten93_16 coreCheck93_16

private theorem validResource93_17 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 17) 0 25
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 93 smallOrder93 [3, 5, 7, 11] 1 25 true) coreChunks93_17 coreFlatten93_17 coreCheck93_17

private theorem validResource93_18 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 18) 0 30
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 93 smallOrder93 [3, 5, 7, 11] 2 30 true) coreChunks93_18 coreFlatten93_18 coreCheck93_18

private theorem validResource93_19 :
    PrefixResourceValid 93 smallOrder93 [3, 5, 7, 11] (resources93 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) (r := coreResources93 19) 30 30
    dataValid93 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource93_18 coreChunks93_19 coreFlatten93_19 coreCheck93_19

theorem finiteCheck93_93 : finiteIntervalCheck 93 93 smallOrder93 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 93) (U := 93) (O := smallOrder93)
    (ps := [3, 5, 7, 11]) resources93 coreSelector93
  · intro i
    fin_cases i
    · exact validResource93_0
    · exact validResource93_1
    · exact validResource93_2
    · exact validResource93_3
    · exact validResource93_4
    · exact validResource93_5
    · exact validResource93_6
    · exact validResource93_7
    · exact validResource93_8
    · exact validResource93_9
    · exact validResource93_10
    · exact validResource93_11
    · exact validResource93_12
    · exact validResource93_13
    · exact validResource93_14
    · exact validResource93_15
    · exact validResource93_16
    · exact validResource93_17
    · exact validResource93_18
    · exact validResource93_19
  · intro b j
    exact resourceRequirements_of_core (coreRequirements93_0 b j)


theorem exactCertificate93_93 : ExactIntervalCertificate 93 93 smallOrder93 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck93_93
#print axioms smallOrder93_nodup
#print axioms smallOrder93_set
#print axioms finiteCheck93_93
#print axioms exactCertificate93_93
end Erdos883Verified
