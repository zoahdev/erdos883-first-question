import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate158OrderCheck
import Erdos883SmallCertificate158Metadata000
import Erdos883SmallCertificate158Metadata001
import Erdos883SmallCertificate158Resource000
import Erdos883SmallCertificate158Resource001
import Erdos883SmallCertificate158Resource002
import Erdos883SmallCertificate158Resource003
import Erdos883SmallCertificate158Resource004
import Erdos883SmallCertificate158Resource005
import Erdos883SmallCertificate158Resource006
import Erdos883SmallCertificate158Resource007
import Erdos883SmallCertificate158Resource008
import Erdos883SmallCertificate158Resource009
import Erdos883SmallCertificate158Resource010
import Erdos883SmallCertificate158Resource011
import Erdos883SmallCertificate158Resource012
import Erdos883SmallCertificate158Resource013
import Erdos883SmallCertificate158Resource014
import Erdos883SmallCertificate158Resource015
import Erdos883SmallCertificate158Resource016
import Erdos883SmallCertificate158Resource017
import Erdos883SmallCertificate158Resource018
import Erdos883SmallCertificate158Resource019
import Erdos883SmallCertificate158Resource020
import Erdos883SmallCertificate158Resource021
import Erdos883SmallCertificate158Resource022
import Erdos883SmallCertificate158Resource023
import Erdos883SmallCertificate158Resource024
import Erdos883SmallCertificate158Resource025
import Erdos883SmallCertificate158Resource026
import Erdos883SmallCertificate158Resource027
import Erdos883SmallCertificate158Resource028
import Erdos883SmallCertificate158Resource029
import Erdos883SmallCertificate158Resource030
import Erdos883SmallCertificate158Resource031Chunk000
import Erdos883SmallCertificate158Resource031Chunk001
import Erdos883SmallCertificate158Resource031Chunk002
import Erdos883SmallCertificate158Resource031Chunk003
import Erdos883SmallCertificate158Resource031
import Erdos883SmallCertificate158Resource032Chunk000
import Erdos883SmallCertificate158Resource032Chunk001
import Erdos883SmallCertificate158Resource032Chunk002
import Erdos883SmallCertificate158Resource032Chunk003
import Erdos883SmallCertificate158Resource032
import Erdos883SmallCertificate158Resource033
import Erdos883SmallCertificate158Resource034Chunk000
import Erdos883SmallCertificate158Resource034Chunk001
import Erdos883SmallCertificate158Resource034Chunk002
import Erdos883SmallCertificate158Resource034
import Erdos883SmallCertificate158Resource035
import Erdos883SmallCertificate158Resource036
import Erdos883SmallCertificate158Resource037Chunk000
import Erdos883SmallCertificate158Resource037Chunk001
import Erdos883SmallCertificate158Resource037Chunk002
import Erdos883SmallCertificate158Resource037Chunk003
import Erdos883SmallCertificate158Resource037
import Erdos883SmallCertificate158Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder158 : List ℕ := coreData158.map (·.value)
theorem smallOrder158_nodup : smallOrder158.Nodup := (coreOrderPermutationCheck_sound coreOrderCheck158).1
theorem smallOrder158_set : smallOrder158.toFinset = oddUniverse 158 := (coreOrderPermutationCheck_sound coreOrderCheck158).2
private def resources158 (i : Fin 38) : PrefixResourceData := resourceOfCore (coreResources158 i)
private theorem dataValid158 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData158.map oddDataOfCore) := by
  apply oddCertificateDataValid_of_coreChunks coreMetadataChunks158 coreMetadataFlatten158
  intro c
  fin_cases c
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck158_0
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck158_1
#print axioms dataValid158

private theorem validResource158_0 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 0) 0 142
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 144 smallOrder158 [3, 5, 7, 11] 0 142 false) coreChunks158_0 coreFlatten158_0 coreCheck158_0

private theorem validResource158_1 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 1) 18 142
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_0 coreChunks158_1 coreFlatten158_1 coreCheck158_1

private theorem validResource158_2 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 2) 19 141
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_1 coreChunks158_2 coreFlatten158_2 coreCheck158_2

private theorem validResource158_3 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 3) 22 140
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_2 coreChunks158_3 coreFlatten158_3 coreCheck158_3

private theorem validResource158_4 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 4) 36 112
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_3 coreChunks158_4 coreFlatten158_4 coreCheck158_4

private theorem validResource158_5 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 5) 38 103
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_4 coreChunks158_5 coreFlatten158_5 coreCheck158_5

private theorem validResource158_6 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 6) 39 97
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_5 coreChunks158_6 coreFlatten158_6 coreCheck158_6

private theorem validResource158_7 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 7) 0 72
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 144 smallOrder158 [3, 5, 7, 11] 0 72 true) coreChunks158_7 coreFlatten158_7 coreCheck158_7

private theorem validResource158_8 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 8) 18 72
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_7 coreChunks158_8 coreFlatten158_8 coreCheck158_8

private theorem validResource158_9 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 9) 19 71
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_8 coreChunks158_9 coreFlatten158_9 coreCheck158_9

private theorem validResource158_10 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 10) 27 70
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_9 coreChunks158_10 coreFlatten158_10 coreCheck158_10

private theorem validResource158_11 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 11) 28 69
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_10 coreChunks158_11 coreFlatten158_11 coreCheck158_11

private theorem validResource158_12 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 12) 29 68
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_11 coreChunks158_12 coreFlatten158_12 coreCheck158_12

private theorem validResource158_13 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 13) 30 67
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_12 coreChunks158_13 coreFlatten158_13 coreCheck158_13

private theorem validResource158_14 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 14) 31 66
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_13 coreChunks158_14 coreFlatten158_14 coreCheck158_14

private theorem validResource158_15 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 15) 32 65
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_14 coreChunks158_15 coreFlatten158_15 coreCheck158_15

private theorem validResource158_16 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 16) 33 63
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_15 coreChunks158_16 coreFlatten158_16 coreCheck158_16

private theorem validResource158_17 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 17) 35 61
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_16 coreChunks158_17 coreFlatten158_17 coreCheck158_17

private theorem validResource158_18 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 18) 37 56
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_17 coreChunks158_18 coreFlatten158_18 coreCheck158_18

private theorem validResource158_19 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 19) 38 51
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_18 coreChunks158_19 coreFlatten158_19 coreCheck158_19

private theorem validResource158_20 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 20) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 20) 39 48
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_19 coreChunks158_20 coreFlatten158_20 coreCheck158_20

private theorem validResource158_21 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 21) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 21) 40 47
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_20 coreChunks158_21 coreFlatten158_21 coreCheck158_21

private theorem validResource158_22 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 22) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 22) 44 46
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_21 coreChunks158_22 coreFlatten158_22 coreCheck158_22

private theorem validResource158_23 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 23) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 23) 45 45
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_22 coreChunks158_23 coreFlatten158_23 coreCheck158_23

private theorem validResource158_24 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 24) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 24) 47 43
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_23 coreChunks158_24 coreFlatten158_24 coreCheck158_24

private theorem validResource158_25 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 25) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 25) 49 42
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_24 coreChunks158_25 coreFlatten158_25 coreCheck158_25

private theorem validResource158_26 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 26) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 26) 53 41
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_25 coreChunks158_26 coreFlatten158_26 coreCheck158_26

private theorem validResource158_27 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 27) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 27) 57 33
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_26 coreChunks158_27 coreFlatten158_27 coreCheck158_27

private theorem validResource158_28 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 28) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 28) 61 32
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_27 coreChunks158_28 coreFlatten158_28 coreCheck158_28

private theorem validResource158_29 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 29) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 29) 65 31
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_28 coreChunks158_29 coreFlatten158_29 coreCheck158_29

private theorem validResource158_30 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 30) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 30) 78 30
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_29 coreChunks158_30 coreFlatten158_30 coreCheck158_30

private theorem validResource158_31 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 31) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 31) 0 41
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 144 smallOrder158 [3, 5, 7, 11] 1 41 true) coreChunks158_31 coreFlatten158_31 coreCheck158_31

private theorem validResource158_32 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 32) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 32) 0 47
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 144 smallOrder158 [3, 5, 7, 11] 2 47 true) coreChunks158_32 coreFlatten158_32 coreCheck158_32

private theorem validResource158_33 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 33) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 33) 52 47
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_32 coreChunks158_33 coreFlatten158_33 coreCheck158_33

private theorem validResource158_34 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 34) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 34) 0 55
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 144 smallOrder158 [3, 5, 7, 11] 3 55 true) coreChunks158_34 coreFlatten158_34 coreCheck158_34

private theorem validResource158_35 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 35) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 35) 43 55
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_34 coreChunks158_35 coreFlatten158_35 coreCheck158_35

private theorem validResource158_36 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 36) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 36) 44 53
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource158_35 coreChunks158_36 coreFlatten158_36 coreCheck158_36

private theorem validResource158_37 :
    PrefixResourceValid 144 smallOrder158 [3, 5, 7, 11] (resources158 37) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 144) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) (r := coreResources158 37) 0 52
    dataValid158 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 144 smallOrder158 [3, 5, 7, 11] 4 52 true) coreChunks158_37 coreFlatten158_37 coreCheck158_37

theorem finiteCheck144_158 : finiteIntervalCheck 144 158 smallOrder158 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 144) (U := 158) (O := smallOrder158)
    (ps := [3, 5, 7, 11]) resources158 coreSelector158
  · intro i
    fin_cases i
    · exact validResource158_0
    · exact validResource158_1
    · exact validResource158_2
    · exact validResource158_3
    · exact validResource158_4
    · exact validResource158_5
    · exact validResource158_6
    · exact validResource158_7
    · exact validResource158_8
    · exact validResource158_9
    · exact validResource158_10
    · exact validResource158_11
    · exact validResource158_12
    · exact validResource158_13
    · exact validResource158_14
    · exact validResource158_15
    · exact validResource158_16
    · exact validResource158_17
    · exact validResource158_18
    · exact validResource158_19
    · exact validResource158_20
    · exact validResource158_21
    · exact validResource158_22
    · exact validResource158_23
    · exact validResource158_24
    · exact validResource158_25
    · exact validResource158_26
    · exact validResource158_27
    · exact validResource158_28
    · exact validResource158_29
    · exact validResource158_30
    · exact validResource158_31
    · exact validResource158_32
    · exact validResource158_33
    · exact validResource158_34
    · exact validResource158_35
    · exact validResource158_36
    · exact validResource158_37
  · intro b j
    exact resourceRequirements_of_core (coreRequirements158_0 b j)


theorem exactCertificate144_158 : ExactIntervalCertificate 144 158 smallOrder158 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck144_158
#print axioms smallOrder158_nodup
#print axioms smallOrder158_set
#print axioms finiteCheck144_158
#print axioms exactCertificate144_158
end Erdos883Verified
