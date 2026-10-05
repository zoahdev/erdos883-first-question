import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate92OrderCheck
import Erdos883SmallCertificate92Metadata000
import Erdos883SmallCertificate92Resource000
import Erdos883SmallCertificate92Resource001
import Erdos883SmallCertificate92Resource002
import Erdos883SmallCertificate92Resource003
import Erdos883SmallCertificate92Resource004
import Erdos883SmallCertificate92Resource005
import Erdos883SmallCertificate92Resource006
import Erdos883SmallCertificate92Resource007
import Erdos883SmallCertificate92Resource008
import Erdos883SmallCertificate92Resource009
import Erdos883SmallCertificate92Resource010
import Erdos883SmallCertificate92Resource011
import Erdos883SmallCertificate92Resource012
import Erdos883SmallCertificate92Resource013
import Erdos883SmallCertificate92Resource014
import Erdos883SmallCertificate92Resource015
import Erdos883SmallCertificate92Resource016Chunk000
import Erdos883SmallCertificate92Resource016Chunk001
import Erdos883SmallCertificate92Resource016Chunk002
import Erdos883SmallCertificate92Resource016
import Erdos883SmallCertificate92Resource017
import Erdos883SmallCertificate92Resource018
import Erdos883SmallCertificate92Resource019
import Erdos883SmallCertificate92Resource020
import Erdos883SmallCertificate92Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder92 : List ℕ := coreData92.map (·.value)
theorem smallOrder92_nodup : smallOrder92.Nodup := (coreOrderPermutationCheck_sound coreOrderCheck92).1
theorem smallOrder92_set : smallOrder92.toFinset = oddUniverse 92 := (coreOrderPermutationCheck_sound coreOrderCheck92).2
private def resources92 (i : Fin 21) : PrefixResourceData := resourceOfCore (coreResources92 i)
private theorem dataValid92 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData92.map oddDataOfCore) := by
  apply oddCertificateDataValid_of_coreChunks coreMetadataChunks92 coreMetadataFlatten92
  intro c
  fin_cases c
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck92_0
#print axioms dataValid92

private theorem validResource92_0 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 0) 0 82
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 84 smallOrder92 [3, 5, 7, 11] 0 82 false) coreChunks92_0 coreFlatten92_0 coreCheck92_0

private theorem validResource92_1 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 1) 0 42
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 84 smallOrder92 [3, 5, 7, 11] 0 42 true) coreChunks92_1 coreFlatten92_1 coreCheck92_1

private theorem validResource92_2 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 2) 12 42
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_1 coreChunks92_2 coreFlatten92_2 coreCheck92_2

private theorem validResource92_3 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 3) 13 41
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_2 coreChunks92_3 coreFlatten92_3 coreCheck92_3

private theorem validResource92_4 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 4) 17 40
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_3 coreChunks92_4 coreFlatten92_4 coreCheck92_4

private theorem validResource92_5 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 5) 18 39
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_4 coreChunks92_5 coreFlatten92_5 coreCheck92_5

private theorem validResource92_6 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 6) 19 38
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_5 coreChunks92_6 coreFlatten92_6 coreCheck92_6

private theorem validResource92_7 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 7) 20 37
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_6 coreChunks92_7 coreFlatten92_7 coreCheck92_7

private theorem validResource92_8 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 8) 21 36
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_7 coreChunks92_8 coreFlatten92_8 coreCheck92_8

private theorem validResource92_9 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 9) 23 33
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_8 coreChunks92_9 coreFlatten92_9 coreCheck92_9

private theorem validResource92_10 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 10) 25 29
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_9 coreChunks92_10 coreFlatten92_10 coreCheck92_10

private theorem validResource92_11 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 11) 27 26
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_10 coreChunks92_11 coreFlatten92_11 coreCheck92_11

private theorem validResource92_12 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 12) 28 24
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_11 coreChunks92_12 coreFlatten92_12 coreCheck92_12

private theorem validResource92_13 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 13) 31 23
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_12 coreChunks92_13 coreFlatten92_13 coreCheck92_13

private theorem validResource92_14 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 14) 35 19
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_13 coreChunks92_14 coreFlatten92_14 coreCheck92_14

private theorem validResource92_15 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 15) 37 18
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_14 coreChunks92_15 coreFlatten92_15 coreCheck92_15

private theorem validResource92_16 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 16) 0 23
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 84 smallOrder92 [3, 5, 7, 11] 1 23 true) coreChunks92_16 coreFlatten92_16 coreCheck92_16

private theorem validResource92_17 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 17) 0 30
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 84 smallOrder92 [3, 5, 7, 11] 2 30 true) coreChunks92_17 coreFlatten92_17 coreCheck92_17

private theorem validResource92_18 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 18) 28 30
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_17 coreChunks92_18 coreFlatten92_18 coreCheck92_18

private theorem validResource92_19 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 19) 29 29
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_18 coreChunks92_19 coreFlatten92_19 coreCheck92_19

private theorem validResource92_20 :
    PrefixResourceValid 84 smallOrder92 [3, 5, 7, 11] (resources92 20) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 84) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) (r := coreResources92 20) 30 28
    dataValid92 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource92_19 coreChunks92_20 coreFlatten92_20 coreCheck92_20

theorem finiteCheck84_92 : finiteIntervalCheck 84 92 smallOrder92 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 84) (U := 92) (O := smallOrder92)
    (ps := [3, 5, 7, 11]) resources92 coreSelector92
  · intro i
    fin_cases i
    · exact validResource92_0
    · exact validResource92_1
    · exact validResource92_2
    · exact validResource92_3
    · exact validResource92_4
    · exact validResource92_5
    · exact validResource92_6
    · exact validResource92_7
    · exact validResource92_8
    · exact validResource92_9
    · exact validResource92_10
    · exact validResource92_11
    · exact validResource92_12
    · exact validResource92_13
    · exact validResource92_14
    · exact validResource92_15
    · exact validResource92_16
    · exact validResource92_17
    · exact validResource92_18
    · exact validResource92_19
    · exact validResource92_20
  · intro b j
    exact resourceRequirements_of_core (coreRequirements92_0 b j)


theorem exactCertificate84_92 : ExactIntervalCertificate 84 92 smallOrder92 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck84_92
#print axioms smallOrder92_nodup
#print axioms smallOrder92_set
#print axioms finiteCheck84_92
#print axioms exactCertificate84_92
end Erdos883Verified
