import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate212OrderCheck
import Erdos883SmallCertificate212Metadata000
import Erdos883SmallCertificate212Metadata001
import Erdos883SmallCertificate212Resource000
import Erdos883SmallCertificate212Resource001
import Erdos883SmallCertificate212Resource002
import Erdos883SmallCertificate212Resource003
import Erdos883SmallCertificate212Resource004
import Erdos883SmallCertificate212Resource005
import Erdos883SmallCertificate212Resource006
import Erdos883SmallCertificate212Resource007
import Erdos883SmallCertificate212Resource008
import Erdos883SmallCertificate212Resource009
import Erdos883SmallCertificate212Resource010
import Erdos883SmallCertificate212Resource011
import Erdos883SmallCertificate212Resource012
import Erdos883SmallCertificate212Resource013
import Erdos883SmallCertificate212Resource014
import Erdos883SmallCertificate212Resource015
import Erdos883SmallCertificate212Resource016
import Erdos883SmallCertificate212Resource017
import Erdos883SmallCertificate212Resource018
import Erdos883SmallCertificate212Resource019
import Erdos883SmallCertificate212Resource020
import Erdos883SmallCertificate212Resource021
import Erdos883SmallCertificate212Resource022
import Erdos883SmallCertificate212Resource023
import Erdos883SmallCertificate212Resource024
import Erdos883SmallCertificate212Resource025
import Erdos883SmallCertificate212Resource026
import Erdos883SmallCertificate212Resource027
import Erdos883SmallCertificate212Resource028
import Erdos883SmallCertificate212Resource029
import Erdos883SmallCertificate212Resource030
import Erdos883SmallCertificate212Resource031
import Erdos883SmallCertificate212Resource032
import Erdos883SmallCertificate212Resource033
import Erdos883SmallCertificate212Resource034
import Erdos883SmallCertificate212Resource035
import Erdos883SmallCertificate212Resource036
import Erdos883SmallCertificate212Resource037
import Erdos883SmallCertificate212Resource038
import Erdos883SmallCertificate212Resource039Chunk000
import Erdos883SmallCertificate212Resource039Chunk001
import Erdos883SmallCertificate212Resource039Chunk002
import Erdos883SmallCertificate212Resource039Chunk003
import Erdos883SmallCertificate212Resource039Chunk004
import Erdos883SmallCertificate212Resource039Chunk005
import Erdos883SmallCertificate212Resource039
import Erdos883SmallCertificate212Resource040Chunk000
import Erdos883SmallCertificate212Resource040Chunk001
import Erdos883SmallCertificate212Resource040Chunk002
import Erdos883SmallCertificate212Resource040Chunk003
import Erdos883SmallCertificate212Resource040Chunk004
import Erdos883SmallCertificate212Resource040
import Erdos883SmallCertificate212Resource041
import Erdos883SmallCertificate212Resource042
import Erdos883SmallCertificate212Resource043Chunk000
import Erdos883SmallCertificate212Resource043Chunk001
import Erdos883SmallCertificate212Resource043Chunk002
import Erdos883SmallCertificate212Resource043Chunk003
import Erdos883SmallCertificate212Resource043
import Erdos883SmallCertificate212Resource044
import Erdos883SmallCertificate212Resource045
import Erdos883SmallCertificate212Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder212 : List ℕ := coreData212.map (·.value)
theorem smallOrder212_nodup : smallOrder212.Nodup := (coreOrderPermutationCheck_sound coreOrderCheck212).1
theorem smallOrder212_set : smallOrder212.toFinset = oddUniverse 212 := (coreOrderPermutationCheck_sound coreOrderCheck212).2
private def resources212 (i : Fin 46) : PrefixResourceData := resourceOfCore (coreResources212 i)
private theorem dataValid212 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData212.map oddDataOfCore) := by
  apply oddCertificateDataValid_of_coreChunks coreMetadataChunks212 coreMetadataFlatten212
  intro c
  fin_cases c
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck212_0
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck212_1
#print axioms dataValid212

private theorem validResource212_0 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 0) 0 191
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 193 smallOrder212 [3, 5, 7, 11] 0 191 false) coreChunks212_0 coreFlatten212_0 coreCheck212_0

private theorem validResource212_1 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 1) 24 191
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_0 coreChunks212_1 coreFlatten212_1 coreCheck212_1

private theorem validResource212_2 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 2) 25 190
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_1 coreChunks212_2 coreFlatten212_2 coreCheck212_2

private theorem validResource212_3 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 3) 29 189
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_2 coreChunks212_3 coreFlatten212_3 coreCheck212_3

private theorem validResource212_4 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 4) 47 153
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_3 coreChunks212_4 coreFlatten212_4 coreCheck212_4

private theorem validResource212_5 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 5) 50 142
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_4 coreChunks212_5 coreFlatten212_5 coreCheck212_5

private theorem validResource212_6 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 6) 51 140
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_5 coreChunks212_6 coreFlatten212_6 coreCheck212_6

private theorem validResource212_7 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 7) 52 134
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_6 coreChunks212_7 coreFlatten212_7 coreCheck212_7

private theorem validResource212_8 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 8) 0 96
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 193 smallOrder212 [3, 5, 7, 11] 0 96 true) coreChunks212_8 coreFlatten212_8 coreCheck212_8

private theorem validResource212_9 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 9) 24 96
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_8 coreChunks212_9 coreFlatten212_9 coreCheck212_9

private theorem validResource212_10 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 10) 25 95
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_9 coreChunks212_10 coreFlatten212_10 coreCheck212_10

private theorem validResource212_11 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 11) 33 94
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_10 coreChunks212_11 coreFlatten212_11 coreCheck212_11

private theorem validResource212_12 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 12) 34 93
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_11 coreChunks212_12 coreFlatten212_12 coreCheck212_12

private theorem validResource212_13 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 13) 37 92
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_12 coreChunks212_13 coreFlatten212_13 coreCheck212_13

private theorem validResource212_14 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 14) 38 91
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_13 coreChunks212_14 coreFlatten212_14 coreCheck212_14

private theorem validResource212_15 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 15) 39 90
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_14 coreChunks212_15 coreFlatten212_15 coreCheck212_15

private theorem validResource212_16 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 16) 40 89
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_15 coreChunks212_16 coreFlatten212_16 coreCheck212_16

private theorem validResource212_17 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 17) 41 87
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_16 coreChunks212_17 coreFlatten212_17 coreCheck212_17

private theorem validResource212_18 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 18) 42 86
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_17 coreChunks212_18 coreFlatten212_18 coreCheck212_18

private theorem validResource212_19 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 19) 44 84
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_18 coreChunks212_19 coreFlatten212_19 coreCheck212_19

private theorem validResource212_20 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 20) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 20) 46 81
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_19 coreChunks212_20 coreFlatten212_20 coreCheck212_20

private theorem validResource212_21 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 21) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 21) 47 76
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_20 coreChunks212_21 coreFlatten212_21 coreCheck212_21

private theorem validResource212_22 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 22) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 22) 50 71
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_21 coreChunks212_22 coreFlatten212_22 coreCheck212_22

private theorem validResource212_23 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 23) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 23) 51 70
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_22 coreChunks212_23 coreFlatten212_23 coreCheck212_23

private theorem validResource212_24 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 24) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 24) 52 67
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_23 coreChunks212_24 coreFlatten212_24 coreCheck212_24

private theorem validResource212_25 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 25) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 25) 53 66
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_24 coreChunks212_25 coreFlatten212_25 coreCheck212_25

private theorem validResource212_26 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 26) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 26) 55 65
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_25 coreChunks212_26 coreFlatten212_26 coreCheck212_26

private theorem validResource212_27 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 27) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 27) 58 62
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_26 coreChunks212_27 coreFlatten212_27 coreCheck212_27

private theorem validResource212_28 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 28) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 28) 59 61
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_27 coreChunks212_28 coreFlatten212_28 coreCheck212_28

private theorem validResource212_29 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 29) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 29) 60 59
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_28 coreChunks212_29 coreFlatten212_29 coreCheck212_29

private theorem validResource212_30 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 30) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 30) 62 58
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_29 coreChunks212_30 coreFlatten212_30 coreCheck212_30

private theorem validResource212_31 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 31) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 31) 64 57
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_30 coreChunks212_31 coreFlatten212_31 coreCheck212_31

private theorem validResource212_32 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 32) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 32) 67 56
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_31 coreChunks212_32 coreFlatten212_32 coreCheck212_32

private theorem validResource212_33 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 33) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 33) 71 55
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_32 coreChunks212_33 coreFlatten212_33 coreCheck212_33

private theorem validResource212_34 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 34) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 34) 75 44
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_33 coreChunks212_34 coreFlatten212_34 coreCheck212_34

private theorem validResource212_35 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 35) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 35) 79 43
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_34 coreChunks212_35 coreFlatten212_35 coreCheck212_35

private theorem validResource212_36 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 36) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 36) 85 42
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_35 coreChunks212_36 coreFlatten212_36 coreCheck212_36

private theorem validResource212_37 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 37) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 37) 93 41
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_36 coreChunks212_37 coreFlatten212_37 coreCheck212_37

private theorem validResource212_38 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 38) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 38) 103 40
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_37 coreChunks212_38 coreFlatten212_38 coreCheck212_38

private theorem validResource212_39 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 39) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 39) 0 55
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 193 smallOrder212 [3, 5, 7, 11] 1 55 true) coreChunks212_39 coreFlatten212_39 coreCheck212_39

private theorem validResource212_40 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 40) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 40) 0 65
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 193 smallOrder212 [3, 5, 7, 11] 2 65 true) coreChunks212_40 coreFlatten212_40 coreCheck212_40

private theorem validResource212_41 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 41) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 41) 68 65
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_40 coreChunks212_41 coreFlatten212_41 coreCheck212_41

private theorem validResource212_42 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 42) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 42) 69 64
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_41 coreChunks212_42 coreFlatten212_42 coreCheck212_42

private theorem validResource212_43 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 43) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 43) 0 73
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 193 smallOrder212 [3, 5, 7, 11] 3 73 true) coreChunks212_43 coreFlatten212_43 coreCheck212_43

private theorem validResource212_44 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 44) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 44) 58 73
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_43 coreChunks212_44 coreFlatten212_44 coreCheck212_44

private theorem validResource212_45 :
    PrefixResourceValid 193 smallOrder212 [3, 5, 7, 11] (resources212 45) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 193) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) (r := coreResources212 45) 60 72
    dataValid212 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource212_44 coreChunks212_45 coreFlatten212_45 coreCheck212_45

theorem finiteCheck193_212 : finiteIntervalCheck 193 212 smallOrder212 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 193) (U := 212) (O := smallOrder212)
    (ps := [3, 5, 7, 11]) resources212 coreSelector212
  · intro i
    fin_cases i
    · exact validResource212_0
    · exact validResource212_1
    · exact validResource212_2
    · exact validResource212_3
    · exact validResource212_4
    · exact validResource212_5
    · exact validResource212_6
    · exact validResource212_7
    · exact validResource212_8
    · exact validResource212_9
    · exact validResource212_10
    · exact validResource212_11
    · exact validResource212_12
    · exact validResource212_13
    · exact validResource212_14
    · exact validResource212_15
    · exact validResource212_16
    · exact validResource212_17
    · exact validResource212_18
    · exact validResource212_19
    · exact validResource212_20
    · exact validResource212_21
    · exact validResource212_22
    · exact validResource212_23
    · exact validResource212_24
    · exact validResource212_25
    · exact validResource212_26
    · exact validResource212_27
    · exact validResource212_28
    · exact validResource212_29
    · exact validResource212_30
    · exact validResource212_31
    · exact validResource212_32
    · exact validResource212_33
    · exact validResource212_34
    · exact validResource212_35
    · exact validResource212_36
    · exact validResource212_37
    · exact validResource212_38
    · exact validResource212_39
    · exact validResource212_40
    · exact validResource212_41
    · exact validResource212_42
    · exact validResource212_43
    · exact validResource212_44
    · exact validResource212_45
  · intro b j
    exact resourceRequirements_of_core (coreRequirements212_0 b j)


theorem exactCertificate193_212 : ExactIntervalCertificate 193 212 smallOrder212 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck193_212
#print axioms smallOrder212_nodup
#print axioms smallOrder212_set
#print axioms finiteCheck193_212
#print axioms exactCertificate193_212
end Erdos883Verified
