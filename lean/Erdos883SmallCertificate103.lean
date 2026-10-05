import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate103OrderCheck
import Erdos883SmallCertificate103Metadata000
import Erdos883SmallCertificate103Resource000
import Erdos883SmallCertificate103Resource001
import Erdos883SmallCertificate103Resource002
import Erdos883SmallCertificate103Resource003
import Erdos883SmallCertificate103Resource004
import Erdos883SmallCertificate103Resource005
import Erdos883SmallCertificate103Resource006
import Erdos883SmallCertificate103Resource007
import Erdos883SmallCertificate103Resource008
import Erdos883SmallCertificate103Resource009
import Erdos883SmallCertificate103Resource010
import Erdos883SmallCertificate103Resource011
import Erdos883SmallCertificate103Resource012
import Erdos883SmallCertificate103Resource013
import Erdos883SmallCertificate103Resource014
import Erdos883SmallCertificate103Resource015
import Erdos883SmallCertificate103Resource016
import Erdos883SmallCertificate103Resource017
import Erdos883SmallCertificate103Resource018
import Erdos883SmallCertificate103Resource019
import Erdos883SmallCertificate103Resource020Chunk000
import Erdos883SmallCertificate103Resource020Chunk001
import Erdos883SmallCertificate103Resource020Chunk002
import Erdos883SmallCertificate103Resource020
import Erdos883SmallCertificate103Resource021
import Erdos883SmallCertificate103Resource022
import Erdos883SmallCertificate103Resource023
import Erdos883SmallCertificate103Resource024
import Erdos883SmallCertificate103Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder103 : List ℕ := coreData103.map (·.value)
theorem smallOrder103_nodup : smallOrder103.Nodup := (coreOrderPermutationCheck_sound coreOrderCheck103).1
theorem smallOrder103_set : smallOrder103.toFinset = oddUniverse 103 := (coreOrderPermutationCheck_sound coreOrderCheck103).2
private def resources103 (i : Fin 25) : PrefixResourceData := resourceOfCore (coreResources103 i)
private theorem dataValid103 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData103.map oddDataOfCore) := by
  apply oddCertificateDataValid_of_coreChunks coreMetadataChunks103 coreMetadataFlatten103
  intro c
  fin_cases c
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck103_0
#print axioms dataValid103

private theorem validResource103_0 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 0) 0 92
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 94 smallOrder103 [3, 5, 7, 11] 0 92 false) coreChunks103_0 coreFlatten103_0 coreCheck103_0

private theorem validResource103_1 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 1) 13 92
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_0 coreChunks103_1 coreFlatten103_1 coreCheck103_1

private theorem validResource103_2 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 2) 14 91
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_1 coreChunks103_2 coreFlatten103_2 coreCheck103_2

private theorem validResource103_3 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 3) 0 47
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 94 smallOrder103 [3, 5, 7, 11] 0 47 true) coreChunks103_3 coreFlatten103_3 coreCheck103_3

private theorem validResource103_4 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 4) 13 47
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_3 coreChunks103_4 coreFlatten103_4 coreCheck103_4

private theorem validResource103_5 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 5) 14 46
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_4 coreChunks103_5 coreFlatten103_5 coreCheck103_5

private theorem validResource103_6 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 6) 19 45
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_5 coreChunks103_6 coreFlatten103_6 coreCheck103_6

private theorem validResource103_7 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 7) 20 44
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_6 coreChunks103_7 coreFlatten103_7 coreCheck103_7

private theorem validResource103_8 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 8) 22 43
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_7 coreChunks103_8 coreFlatten103_8 coreCheck103_8

private theorem validResource103_9 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 9) 23 42
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_8 coreChunks103_9 coreFlatten103_9 coreCheck103_9

private theorem validResource103_10 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 10) 24 40
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_9 coreChunks103_10 coreFlatten103_10 coreCheck103_10

private theorem validResource103_11 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 11) 26 37
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_10 coreChunks103_11 coreFlatten103_11 coreCheck103_11

private theorem validResource103_12 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 12) 28 33
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_11 coreChunks103_12 coreFlatten103_12 coreCheck103_12

private theorem validResource103_13 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 13) 29 30
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_12 coreChunks103_13 coreFlatten103_13 coreCheck103_13

private theorem validResource103_14 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 14) 30 29
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_13 coreChunks103_14 coreFlatten103_14 coreCheck103_14

private theorem validResource103_15 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 15) 32 27
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_14 coreChunks103_15 coreFlatten103_15 coreCheck103_15

private theorem validResource103_16 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 16) 35 26
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_15 coreChunks103_16 coreFlatten103_16 coreCheck103_16

private theorem validResource103_17 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 17) 39 23
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_16 coreChunks103_17 coreFlatten103_17 coreCheck103_17

private theorem validResource103_18 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 18) 41 22
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_17 coreChunks103_18 coreFlatten103_18 coreCheck103_18

private theorem validResource103_19 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 19) 45 21
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_18 coreChunks103_19 coreFlatten103_19 coreCheck103_19

private theorem validResource103_20 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 20) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 20) 0 26
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 94 smallOrder103 [3, 5, 7, 11] 1 26 true) coreChunks103_20 coreFlatten103_20 coreCheck103_20

private theorem validResource103_21 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 21) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 21) 0 34
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 94 smallOrder103 [3, 5, 7, 11] 2 34 true) coreChunks103_21 coreFlatten103_21 coreCheck103_21

private theorem validResource103_22 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 22) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 22) 32 34
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_21 coreChunks103_22 coreFlatten103_22 coreCheck103_22

private theorem validResource103_23 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 23) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 23) 33 33
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_22 coreChunks103_23 coreFlatten103_23 coreCheck103_23

private theorem validResource103_24 :
    PrefixResourceValid 94 smallOrder103 [3, 5, 7, 11] (resources103 24) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 94) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) (r := coreResources103 24) 34 31
    dataValid103 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource103_23 coreChunks103_24 coreFlatten103_24 coreCheck103_24

theorem finiteCheck94_103 : finiteIntervalCheck 94 103 smallOrder103 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 94) (U := 103) (O := smallOrder103)
    (ps := [3, 5, 7, 11]) resources103 coreSelector103
  · intro i
    fin_cases i
    · exact validResource103_0
    · exact validResource103_1
    · exact validResource103_2
    · exact validResource103_3
    · exact validResource103_4
    · exact validResource103_5
    · exact validResource103_6
    · exact validResource103_7
    · exact validResource103_8
    · exact validResource103_9
    · exact validResource103_10
    · exact validResource103_11
    · exact validResource103_12
    · exact validResource103_13
    · exact validResource103_14
    · exact validResource103_15
    · exact validResource103_16
    · exact validResource103_17
    · exact validResource103_18
    · exact validResource103_19
    · exact validResource103_20
    · exact validResource103_21
    · exact validResource103_22
    · exact validResource103_23
    · exact validResource103_24
  · intro b j
    exact resourceRequirements_of_core (coreRequirements103_0 b j)


theorem exactCertificate94_103 : ExactIntervalCertificate 94 103 smallOrder103 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck94_103
#print axioms smallOrder103_nodup
#print axioms smallOrder103_set
#print axioms finiteCheck94_103
#print axioms exactCertificate94_103
end Erdos883Verified
