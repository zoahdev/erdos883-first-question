import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate192OrderCheck
import Erdos883SmallCertificate192Metadata000
import Erdos883SmallCertificate192Metadata001
import Erdos883SmallCertificate192Resource000
import Erdos883SmallCertificate192Resource001
import Erdos883SmallCertificate192Resource002
import Erdos883SmallCertificate192Resource003
import Erdos883SmallCertificate192Resource004
import Erdos883SmallCertificate192Resource005
import Erdos883SmallCertificate192Resource006
import Erdos883SmallCertificate192Resource007
import Erdos883SmallCertificate192Resource008
import Erdos883SmallCertificate192Resource009
import Erdos883SmallCertificate192Resource010
import Erdos883SmallCertificate192Resource011
import Erdos883SmallCertificate192Resource012
import Erdos883SmallCertificate192Resource013
import Erdos883SmallCertificate192Resource014
import Erdos883SmallCertificate192Resource015
import Erdos883SmallCertificate192Resource016
import Erdos883SmallCertificate192Resource017
import Erdos883SmallCertificate192Resource018
import Erdos883SmallCertificate192Resource019
import Erdos883SmallCertificate192Resource020
import Erdos883SmallCertificate192Resource021
import Erdos883SmallCertificate192Resource022
import Erdos883SmallCertificate192Resource023
import Erdos883SmallCertificate192Resource024
import Erdos883SmallCertificate192Resource025
import Erdos883SmallCertificate192Resource026
import Erdos883SmallCertificate192Resource027
import Erdos883SmallCertificate192Resource028
import Erdos883SmallCertificate192Resource029
import Erdos883SmallCertificate192Resource030
import Erdos883SmallCertificate192Resource031
import Erdos883SmallCertificate192Resource032
import Erdos883SmallCertificate192Resource033
import Erdos883SmallCertificate192Resource034
import Erdos883SmallCertificate192Resource035Chunk000
import Erdos883SmallCertificate192Resource035Chunk001
import Erdos883SmallCertificate192Resource035Chunk002
import Erdos883SmallCertificate192Resource035Chunk003
import Erdos883SmallCertificate192Resource035Chunk004
import Erdos883SmallCertificate192Resource035
import Erdos883SmallCertificate192Resource036Chunk000
import Erdos883SmallCertificate192Resource036Chunk001
import Erdos883SmallCertificate192Resource036Chunk002
import Erdos883SmallCertificate192Resource036Chunk003
import Erdos883SmallCertificate192Resource036
import Erdos883SmallCertificate192Resource037
import Erdos883SmallCertificate192Resource038Chunk000
import Erdos883SmallCertificate192Resource038Chunk001
import Erdos883SmallCertificate192Resource038Chunk002
import Erdos883SmallCertificate192Resource038Chunk003
import Erdos883SmallCertificate192Resource038
import Erdos883SmallCertificate192Resource039Chunk000
import Erdos883SmallCertificate192Resource039Chunk001
import Erdos883SmallCertificate192Resource039Chunk002
import Erdos883SmallCertificate192Resource039Chunk003
import Erdos883SmallCertificate192Resource039
import Erdos883SmallCertificate192Resource040
import Erdos883SmallCertificate192Resource041
import Erdos883SmallCertificate192Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder192 : List ℕ := coreData192.map (·.value)
theorem smallOrder192_nodup : smallOrder192.Nodup := (coreOrderPermutationCheck_sound coreOrderCheck192).1
theorem smallOrder192_set : smallOrder192.toFinset = oddUniverse 192 := (coreOrderPermutationCheck_sound coreOrderCheck192).2
private def resources192 (i : Fin 42) : PrefixResourceData := resourceOfCore (coreResources192 i)
private theorem dataValid192 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData192.map oddDataOfCore) := by
  apply oddCertificateDataValid_of_coreChunks coreMetadataChunks192 coreMetadataFlatten192
  intro c
  fin_cases c
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck192_0
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck192_1
#print axioms dataValid192

private theorem validResource192_0 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 0) 0 173
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 175 smallOrder192 [3, 5, 7, 11] 0 173 false) coreChunks192_0 coreFlatten192_0 coreCheck192_0

private theorem validResource192_1 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 1) 21 173
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_0 coreChunks192_1 coreFlatten192_1 coreCheck192_1

private theorem validResource192_2 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 2) 22 172
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_1 coreChunks192_2 coreFlatten192_2 coreCheck192_2

private theorem validResource192_3 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 3) 27 171
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_2 coreChunks192_3 coreFlatten192_3 coreCheck192_3

private theorem validResource192_4 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 4) 43 137
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_3 coreChunks192_4 coreFlatten192_4 coreCheck192_4

private theorem validResource192_5 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 5) 45 128
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_4 coreChunks192_5 coreFlatten192_5 coreCheck192_5

private theorem validResource192_6 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 6) 46 126
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_5 coreChunks192_6 coreFlatten192_6 coreCheck192_6

private theorem validResource192_7 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 7) 47 120
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_6 coreChunks192_7 coreFlatten192_7 coreCheck192_7

private theorem validResource192_8 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 8) 0 86
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 175 smallOrder192 [3, 5, 7, 11] 0 86 true) coreChunks192_8 coreFlatten192_8 coreCheck192_8

private theorem validResource192_9 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 9) 22 86
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_8 coreChunks192_9 coreFlatten192_9 coreCheck192_9

private theorem validResource192_10 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 10) 30 85
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_9 coreChunks192_10 coreFlatten192_10 coreCheck192_10

private theorem validResource192_11 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 11) 31 84
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_10 coreChunks192_11 coreFlatten192_11 coreCheck192_11

private theorem validResource192_12 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 12) 34 83
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_11 coreChunks192_12 coreFlatten192_12 coreCheck192_12

private theorem validResource192_13 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 13) 35 82
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_12 coreChunks192_13 coreFlatten192_13 coreCheck192_13

private theorem validResource192_14 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 14) 36 81
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_13 coreChunks192_14 coreFlatten192_14 coreCheck192_14

private theorem validResource192_15 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 15) 37 80
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_14 coreChunks192_15 coreFlatten192_15 coreCheck192_15

private theorem validResource192_16 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 16) 38 78
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_15 coreChunks192_16 coreFlatten192_16 coreCheck192_16

private theorem validResource192_17 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 17) 40 76
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_16 coreChunks192_17 coreFlatten192_17 coreCheck192_17

private theorem validResource192_18 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 18) 42 74
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_17 coreChunks192_18 coreFlatten192_18 coreCheck192_18

private theorem validResource192_19 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 19) 44 69
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_18 coreChunks192_19 coreFlatten192_19 coreCheck192_19

private theorem validResource192_20 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 20) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 20) 45 64
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_19 coreChunks192_20 coreFlatten192_20 coreCheck192_20

private theorem validResource192_21 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 21) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 21) 46 63
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_20 coreChunks192_21 coreFlatten192_21 coreCheck192_21

private theorem validResource192_22 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 22) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 22) 47 60
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_21 coreChunks192_22 coreFlatten192_22 coreCheck192_22

private theorem validResource192_23 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 23) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 23) 48 59
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_22 coreChunks192_23 coreFlatten192_23 coreCheck192_23

private theorem validResource192_24 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 24) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 24) 49 58
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_23 coreChunks192_24 coreFlatten192_24 coreCheck192_24

private theorem validResource192_25 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 25) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 25) 52 56
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_24 coreChunks192_25 coreFlatten192_25 coreCheck192_25

private theorem validResource192_26 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 26) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 26) 54 55
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_25 coreChunks192_26 coreFlatten192_26 coreCheck192_26

private theorem validResource192_27 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 27) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 27) 56 53
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_26 coreChunks192_27 coreFlatten192_27 coreCheck192_27

private theorem validResource192_28 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 28) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 28) 58 52
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_27 coreChunks192_28 coreFlatten192_28 coreCheck192_28

private theorem validResource192_29 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 29) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 29) 60 51
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_28 coreChunks192_29 coreFlatten192_29 coreCheck192_29

private theorem validResource192_30 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 30) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 30) 64 50
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_29 coreChunks192_30 coreFlatten192_30 coreCheck192_30

private theorem validResource192_31 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 31) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 31) 68 40
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_30 coreChunks192_31 coreFlatten192_31 coreCheck192_31

private theorem validResource192_32 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 32) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 32) 72 39
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_31 coreChunks192_32 coreFlatten192_32 coreCheck192_32

private theorem validResource192_33 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 33) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 33) 78 38
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_32 coreChunks192_33 coreFlatten192_33 coreCheck192_33

private theorem validResource192_34 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 34) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 34) 94 37
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_33 coreChunks192_34 coreFlatten192_34 coreCheck192_34

private theorem validResource192_35 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 35) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 35) 0 50
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 175 smallOrder192 [3, 5, 7, 11] 1 50 true) coreChunks192_35 coreFlatten192_35 coreCheck192_35

private theorem validResource192_36 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 36) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 36) 0 58
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 175 smallOrder192 [3, 5, 7, 11] 2 58 true) coreChunks192_36 coreFlatten192_36 coreCheck192_36

private theorem validResource192_37 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 37) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 37) 62 58
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_36 coreChunks192_37 coreFlatten192_37 coreCheck192_37

private theorem validResource192_38 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 38) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 38) 0 133
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 175 smallOrder192 [3, 5, 7, 11] 3 133 false) coreChunks192_38 coreFlatten192_38 coreCheck192_38

private theorem validResource192_39 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 39) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 39) 0 66
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 175 smallOrder192 [3, 5, 7, 11] 3 66 true) coreChunks192_39 coreFlatten192_39 coreCheck192_39

private theorem validResource192_40 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 40) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 40) 52 66
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_39 coreChunks192_40 coreFlatten192_40 coreCheck192_40

private theorem validResource192_41 :
    PrefixResourceValid 175 smallOrder192 [3, 5, 7, 11] (resources192 41) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 175) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) (r := coreResources192 41) 53 64
    dataValid192 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource192_40 coreChunks192_41 coreFlatten192_41 coreCheck192_41

theorem finiteCheck175_192 : finiteIntervalCheck 175 192 smallOrder192 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 175) (U := 192) (O := smallOrder192)
    (ps := [3, 5, 7, 11]) resources192 coreSelector192
  · intro i
    fin_cases i
    · exact validResource192_0
    · exact validResource192_1
    · exact validResource192_2
    · exact validResource192_3
    · exact validResource192_4
    · exact validResource192_5
    · exact validResource192_6
    · exact validResource192_7
    · exact validResource192_8
    · exact validResource192_9
    · exact validResource192_10
    · exact validResource192_11
    · exact validResource192_12
    · exact validResource192_13
    · exact validResource192_14
    · exact validResource192_15
    · exact validResource192_16
    · exact validResource192_17
    · exact validResource192_18
    · exact validResource192_19
    · exact validResource192_20
    · exact validResource192_21
    · exact validResource192_22
    · exact validResource192_23
    · exact validResource192_24
    · exact validResource192_25
    · exact validResource192_26
    · exact validResource192_27
    · exact validResource192_28
    · exact validResource192_29
    · exact validResource192_30
    · exact validResource192_31
    · exact validResource192_32
    · exact validResource192_33
    · exact validResource192_34
    · exact validResource192_35
    · exact validResource192_36
    · exact validResource192_37
    · exact validResource192_38
    · exact validResource192_39
    · exact validResource192_40
    · exact validResource192_41
  · intro b j
    exact resourceRequirements_of_core (coreRequirements192_0 b j)


theorem exactCertificate175_192 : ExactIntervalCertificate 175 192 smallOrder192 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck175_192
#print axioms smallOrder192_nodup
#print axioms smallOrder192_set
#print axioms finiteCheck175_192
#print axioms exactCertificate175_192
end Erdos883Verified
