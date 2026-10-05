import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate129OrderCheck
import Erdos883SmallCertificate129Metadata000
import Erdos883SmallCertificate129Metadata001
import Erdos883SmallCertificate129Resource000
import Erdos883SmallCertificate129Resource001
import Erdos883SmallCertificate129Resource002
import Erdos883SmallCertificate129Resource003
import Erdos883SmallCertificate129Resource004
import Erdos883SmallCertificate129Resource005
import Erdos883SmallCertificate129Resource006
import Erdos883SmallCertificate129Resource007
import Erdos883SmallCertificate129Resource008
import Erdos883SmallCertificate129Resource009
import Erdos883SmallCertificate129Resource010
import Erdos883SmallCertificate129Resource011
import Erdos883SmallCertificate129Resource012
import Erdos883SmallCertificate129Resource013
import Erdos883SmallCertificate129Resource014
import Erdos883SmallCertificate129Resource015
import Erdos883SmallCertificate129Resource016
import Erdos883SmallCertificate129Resource017
import Erdos883SmallCertificate129Resource018
import Erdos883SmallCertificate129Resource019
import Erdos883SmallCertificate129Resource020
import Erdos883SmallCertificate129Resource021
import Erdos883SmallCertificate129Resource022
import Erdos883SmallCertificate129Resource023
import Erdos883SmallCertificate129Resource024
import Erdos883SmallCertificate129Resource025Chunk000
import Erdos883SmallCertificate129Resource025Chunk001
import Erdos883SmallCertificate129Resource025Chunk002
import Erdos883SmallCertificate129Resource025Chunk003
import Erdos883SmallCertificate129Resource025
import Erdos883SmallCertificate129Resource026Chunk000
import Erdos883SmallCertificate129Resource026Chunk001
import Erdos883SmallCertificate129Resource026Chunk002
import Erdos883SmallCertificate129Resource026
import Erdos883SmallCertificate129Resource027Chunk000
import Erdos883SmallCertificate129Resource027Chunk001
import Erdos883SmallCertificate129Resource027Chunk002
import Erdos883SmallCertificate129Resource027
import Erdos883SmallCertificate129Resource028
import Erdos883SmallCertificate129Resource029
import Erdos883SmallCertificate129Resource030
import Erdos883SmallCertificate129Resource031
import Erdos883SmallCertificate129Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder129 : List ℕ := coreData129.map (·.value)
theorem smallOrder129_nodup : smallOrder129.Nodup := (coreOrderPermutationCheck_sound coreOrderCheck129).1
theorem smallOrder129_set : smallOrder129.toFinset = oddUniverse 129 := (coreOrderPermutationCheck_sound coreOrderCheck129).2
private def resources129 (i : Fin 32) : PrefixResourceData := resourceOfCore (coreResources129 i)
private theorem dataValid129 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData129.map oddDataOfCore) := by
  apply oddCertificateDataValid_of_coreChunks coreMetadataChunks129 coreMetadataFlatten129
  intro c
  fin_cases c
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck129_0
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck129_1
#print axioms dataValid129

private theorem validResource129_0 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 0) 0 116
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 118 smallOrder129 [3, 5, 7, 11] 0 116 false) coreChunks129_0 coreFlatten129_0 coreCheck129_0

private theorem validResource129_1 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 1) 15 116
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_0 coreChunks129_1 coreFlatten129_1 coreCheck129_1

private theorem validResource129_2 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 2) 16 115
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_1 coreChunks129_2 coreFlatten129_2 coreCheck129_2

private theorem validResource129_3 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 3) 18 114
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_2 coreChunks129_3 coreFlatten129_3 coreCheck129_3

private theorem validResource129_4 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 4) 32 87
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_3 coreChunks129_4 coreFlatten129_4 coreCheck129_4

private theorem validResource129_5 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 5) 0 59
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 118 smallOrder129 [3, 5, 7, 11] 0 59 true) coreChunks129_5 coreFlatten129_5 coreCheck129_5

private theorem validResource129_6 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 6) 15 59
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_5 coreChunks129_6 coreFlatten129_6 coreCheck129_6

private theorem validResource129_7 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 7) 16 58
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_6 coreChunks129_7 coreFlatten129_7 coreCheck129_7

private theorem validResource129_8 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 8) 22 57
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_7 coreChunks129_8 coreFlatten129_8 coreCheck129_8

private theorem validResource129_9 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 9) 23 56
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_8 coreChunks129_9 coreFlatten129_9 coreCheck129_9

private theorem validResource129_10 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 10) 24 55
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_9 coreChunks129_10 coreFlatten129_10 coreCheck129_10

private theorem validResource129_11 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 11) 25 54
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_10 coreChunks129_11 coreFlatten129_11 coreCheck129_11

private theorem validResource129_12 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 12) 26 53
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_11 coreChunks129_12 coreFlatten129_12 coreCheck129_12

private theorem validResource129_13 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 13) 27 52
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_12 coreChunks129_13 coreFlatten129_13 coreCheck129_13

private theorem validResource129_14 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 14) 29 50
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_13 coreChunks129_14 coreFlatten129_14 coreCheck129_14

private theorem validResource129_15 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 15) 31 46
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_14 coreChunks129_15 coreFlatten129_15 coreCheck129_15

private theorem validResource129_16 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 16) 32 43
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_15 coreChunks129_16 coreFlatten129_16 coreCheck129_16

private theorem validResource129_17 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 17) 35 38
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_16 coreChunks129_17 coreFlatten129_17 coreCheck129_17

private theorem validResource129_18 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 18) 37 37
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_17 coreChunks129_18 coreFlatten129_18 coreCheck129_18

private theorem validResource129_19 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 19) 38 35
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_18 coreChunks129_19 coreFlatten129_19 coreCheck129_19

private theorem validResource129_20 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 20) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 20) 40 34
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_19 coreChunks129_20 coreFlatten129_20 coreCheck129_20

private theorem validResource129_21 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 21) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 21) 43 33
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_20 coreChunks129_21 coreFlatten129_21 coreCheck129_21

private theorem validResource129_22 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 22) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 22) 47 27
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_21 coreChunks129_22 coreFlatten129_22 coreCheck129_22

private theorem validResource129_23 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 23) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 23) 51 26
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_22 coreChunks129_23 coreFlatten129_23 coreCheck129_23

private theorem validResource129_24 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 24) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 24) 55 25
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_23 coreChunks129_24 coreFlatten129_24 coreCheck129_24

private theorem validResource129_25 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 25) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 25) 0 33
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 118 smallOrder129 [3, 5, 7, 11] 1 33 true) coreChunks129_25 coreFlatten129_25 coreCheck129_25

private theorem validResource129_26 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 26) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 26) 0 85
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 118 smallOrder129 [3, 5, 7, 11] 2 85 false) coreChunks129_26 coreFlatten129_26 coreCheck129_26

private theorem validResource129_27 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 27) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 27) 0 43
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 118 smallOrder129 [3, 5, 7, 11] 2 43 true) coreChunks129_27 coreFlatten129_27 coreCheck129_27

private theorem validResource129_28 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 28) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 28) 35 43
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_27 coreChunks129_28 coreFlatten129_28 coreCheck129_28

private theorem validResource129_29 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 29) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 29) 40 42
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_28 coreChunks129_29 coreFlatten129_29 coreCheck129_29

private theorem validResource129_30 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 30) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 30) 41 41
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_29 coreChunks129_30 coreFlatten129_30 coreCheck129_30

private theorem validResource129_31 :
    PrefixResourceValid 118 smallOrder129 [3, 5, 7, 11] (resources129 31) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 118) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) (r := coreResources129 31) 42 40
    dataValid129 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource129_30 coreChunks129_31 coreFlatten129_31 coreCheck129_31

theorem finiteCheck118_129 : finiteIntervalCheck 118 129 smallOrder129 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 118) (U := 129) (O := smallOrder129)
    (ps := [3, 5, 7, 11]) resources129 coreSelector129
  · intro i
    fin_cases i
    · exact validResource129_0
    · exact validResource129_1
    · exact validResource129_2
    · exact validResource129_3
    · exact validResource129_4
    · exact validResource129_5
    · exact validResource129_6
    · exact validResource129_7
    · exact validResource129_8
    · exact validResource129_9
    · exact validResource129_10
    · exact validResource129_11
    · exact validResource129_12
    · exact validResource129_13
    · exact validResource129_14
    · exact validResource129_15
    · exact validResource129_16
    · exact validResource129_17
    · exact validResource129_18
    · exact validResource129_19
    · exact validResource129_20
    · exact validResource129_21
    · exact validResource129_22
    · exact validResource129_23
    · exact validResource129_24
    · exact validResource129_25
    · exact validResource129_26
    · exact validResource129_27
    · exact validResource129_28
    · exact validResource129_29
    · exact validResource129_30
    · exact validResource129_31
  · intro b j
    exact resourceRequirements_of_core (coreRequirements129_0 b j)


theorem exactCertificate118_129 : ExactIntervalCertificate 118 129 smallOrder129 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck118_129
#print axioms smallOrder129_nodup
#print axioms smallOrder129_set
#print axioms finiteCheck118_129
#print axioms exactCertificate118_129
end Erdos883Verified
