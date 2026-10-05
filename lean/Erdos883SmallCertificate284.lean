import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate284Resource000
import Erdos883SmallCertificate284Resource001
import Erdos883SmallCertificate284Resource002
import Erdos883SmallCertificate284Resource003
import Erdos883SmallCertificate284Resource004
import Erdos883SmallCertificate284Resource005
import Erdos883SmallCertificate284Resource006
import Erdos883SmallCertificate284Resource007
import Erdos883SmallCertificate284Resource008
import Erdos883SmallCertificate284Resource009
import Erdos883SmallCertificate284Resource010
import Erdos883SmallCertificate284Resource011
import Erdos883SmallCertificate284Resource012
import Erdos883SmallCertificate284Resource013
import Erdos883SmallCertificate284Resource014
import Erdos883SmallCertificate284Resource015
import Erdos883SmallCertificate284Resource016
import Erdos883SmallCertificate284Resource017
import Erdos883SmallCertificate284Resource018
import Erdos883SmallCertificate284Resource019
import Erdos883SmallCertificate284Resource020
import Erdos883SmallCertificate284Resource021
import Erdos883SmallCertificate284Resource022
import Erdos883SmallCertificate284Resource023
import Erdos883SmallCertificate284Resource024
import Erdos883SmallCertificate284Resource025
import Erdos883SmallCertificate284Resource026
import Erdos883SmallCertificate284Resource027
import Erdos883SmallCertificate284Resource028
import Erdos883SmallCertificate284Resource029
import Erdos883SmallCertificate284Resource030
import Erdos883SmallCertificate284Resource031
import Erdos883SmallCertificate284Resource032
import Erdos883SmallCertificate284Resource033
import Erdos883SmallCertificate284Resource034
import Erdos883SmallCertificate284Resource035
import Erdos883SmallCertificate284Resource036
import Erdos883SmallCertificate284Resource037
import Erdos883SmallCertificate284Resource038
import Erdos883SmallCertificate284Resource039
import Erdos883SmallCertificate284Resource040
import Erdos883SmallCertificate284Resource041
import Erdos883SmallCertificate284Resource042
import Erdos883SmallCertificate284Resource043
import Erdos883SmallCertificate284Resource044
import Erdos883SmallCertificate284Resource045
import Erdos883SmallCertificate284Resource046
import Erdos883SmallCertificate284Resource047
import Erdos883SmallCertificate284Resource048
import Erdos883SmallCertificate284Resource049
import Erdos883SmallCertificate284Resource050
import Erdos883SmallCertificate284Resource051
import Erdos883SmallCertificate284Resource052
import Erdos883SmallCertificate284Resource053
import Erdos883SmallCertificate284Resource054
import Erdos883SmallCertificate284Resource055
import Erdos883SmallCertificate284Resource056
import Erdos883SmallCertificate284Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder284 : List ℕ := coreData284.map (·.value)
theorem smallOrder284_nodup : smallOrder284.Nodup := by decide +kernel
theorem smallOrder284_set : smallOrder284.toFinset = oddUniverse 284 := by decide +kernel
private def resources284 (i : Fin 57) : PrefixResourceData := resourceOfCore (coreResources284 i)
private theorem dataValid284 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData284.map oddDataOfCore) := by
  unfold OddCertificateDataValid
  decide +kernel
#print axioms dataValid284

private theorem validResource284_0 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 0) 0 257
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 259 smallOrder284 [3, 5, 7, 11] 0 257 false) coreChunks284_0 coreFlatten284_0 coreCheck284_0

private theorem validResource284_1 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 1) 31 257
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_0 coreChunks284_1 coreFlatten284_1 coreCheck284_1

private theorem validResource284_2 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 2) 32 256
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_1 coreChunks284_2 coreFlatten284_2 coreCheck284_2

private theorem validResource284_3 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 3) 38 255
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_2 coreChunks284_3 coreFlatten284_3 coreCheck284_3

private theorem validResource284_4 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 4) 61 207
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_3 coreChunks284_4 coreFlatten284_4 coreCheck284_4

private theorem validResource284_5 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 5) 62 197
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_4 coreChunks284_5 coreFlatten284_5 coreCheck284_5

private theorem validResource284_6 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 6) 63 195
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_5 coreChunks284_6 coreFlatten284_6 coreCheck284_6

private theorem validResource284_7 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 7) 64 194
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_6 coreChunks284_7 coreFlatten284_7 coreCheck284_7

private theorem validResource284_8 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 8) 66 191
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_7 coreChunks284_8 coreFlatten284_8 coreCheck284_8

private theorem validResource284_9 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 9) 67 190
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_8 coreChunks284_9 coreFlatten284_9 coreCheck284_9

private theorem validResource284_10 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 10) 68 186
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_9 coreChunks284_10 coreFlatten284_10 coreCheck284_10

private theorem validResource284_11 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 11) 69 180
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_10 coreChunks284_11 coreFlatten284_11 coreCheck284_11

private theorem validResource284_12 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 12) 0 129
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 259 smallOrder284 [3, 5, 7, 11] 0 129 true) coreChunks284_12 coreFlatten284_12 coreCheck284_12

private theorem validResource284_13 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 13) 31 129
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_12 coreChunks284_13 coreFlatten284_13 coreCheck284_13

private theorem validResource284_14 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 14) 32 128
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_13 coreChunks284_14 coreFlatten284_14 coreCheck284_14

private theorem validResource284_15 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 15) 44 127
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_14 coreChunks284_15 coreFlatten284_15 coreCheck284_15

private theorem validResource284_16 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 16) 45 126
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_15 coreChunks284_16 coreFlatten284_16 coreCheck284_16

private theorem validResource284_17 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 17) 48 125
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_16 coreChunks284_17 coreFlatten284_17 coreCheck284_17

private theorem validResource284_18 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 18) 49 124
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_17 coreChunks284_18 coreFlatten284_18 coreCheck284_18

private theorem validResource284_19 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 19) 51 123
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_18 coreChunks284_19 coreFlatten284_19 coreCheck284_19

private theorem validResource284_20 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 20) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 20) 52 122
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_19 coreChunks284_20 coreFlatten284_20 coreCheck284_20

private theorem validResource284_21 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 21) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 21) 53 121
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_20 coreChunks284_21 coreFlatten284_21 coreCheck284_21

private theorem validResource284_22 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 22) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 22) 54 120
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_21 coreChunks284_22 coreFlatten284_22 coreCheck284_22

private theorem validResource284_23 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 23) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 23) 55 118
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_22 coreChunks284_23 coreFlatten284_23 coreCheck284_23

private theorem validResource284_24 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 24) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 24) 56 116
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_23 coreChunks284_24 coreFlatten284_24 coreCheck284_24

private theorem validResource284_25 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 25) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 25) 58 113
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_24 coreChunks284_25 coreFlatten284_25 coreCheck284_25

private theorem validResource284_26 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 26) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 26) 60 109
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_25 coreChunks284_26 coreFlatten284_26 coreCheck284_26

private theorem validResource284_27 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 27) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 27) 61 103
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_26 coreChunks284_27 coreFlatten284_27 coreCheck284_27

private theorem validResource284_28 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 28) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 28) 62 98
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_27 coreChunks284_28 coreFlatten284_28 coreCheck284_28

private theorem validResource284_29 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 29) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 29) 63 97
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_28 coreChunks284_29 coreFlatten284_29 coreCheck284_29

private theorem validResource284_30 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 30) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 30) 64 96
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_29 coreChunks284_30 coreFlatten284_30 coreCheck284_30

private theorem validResource284_31 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 31) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 31) 67 95
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_30 coreChunks284_31 coreFlatten284_31 coreCheck284_31

private theorem validResource284_32 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 32) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 32) 68 93
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_31 coreChunks284_32 coreFlatten284_32 coreCheck284_32

private theorem validResource284_33 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 33) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 33) 69 90
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_32 coreChunks284_33 coreFlatten284_33 coreCheck284_33

private theorem validResource284_34 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 34) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 34) 71 89
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_33 coreChunks284_34 coreFlatten284_34 coreCheck284_34

private theorem validResource284_35 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 35) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 35) 72 88
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_34 coreChunks284_35 coreFlatten284_35 coreCheck284_35

private theorem validResource284_36 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 36) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 36) 74 87
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_35 coreChunks284_36 coreFlatten284_36 coreCheck284_36

private theorem validResource284_37 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 37) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 37) 77 84
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_36 coreChunks284_37 coreFlatten284_37 coreCheck284_37

private theorem validResource284_38 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 38) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 38) 78 82
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_37 coreChunks284_38 coreFlatten284_38 coreCheck284_38

private theorem validResource284_39 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 39) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 39) 80 80
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_38 coreChunks284_39 coreFlatten284_39 coreCheck284_39

private theorem validResource284_40 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 40) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 40) 82 79
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_39 coreChunks284_40 coreFlatten284_40 coreCheck284_40

private theorem validResource284_41 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 41) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 41) 84 78
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_40 coreChunks284_41 coreFlatten284_41 coreCheck284_41

private theorem validResource284_42 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 42) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 42) 87 77
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_41 coreChunks284_42 coreFlatten284_42 coreCheck284_42

private theorem validResource284_43 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 43) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 43) 89 76
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_42 coreChunks284_43 coreFlatten284_43 coreCheck284_43

private theorem validResource284_44 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 44) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 44) 95 74
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_43 coreChunks284_44 coreFlatten284_44 coreCheck284_44

private theorem validResource284_45 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 45) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 45) 100 59
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_44 coreChunks284_45 coreFlatten284_45 coreCheck284_45

private theorem validResource284_46 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 46) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 46) 106 58
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_45 coreChunks284_46 coreFlatten284_46 coreCheck284_46

private theorem validResource284_47 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 47) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 47) 113 57
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_46 coreChunks284_47 coreFlatten284_47 coreCheck284_47

private theorem validResource284_48 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 48) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 48) 123 56
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_47 coreChunks284_48 coreFlatten284_48 coreCheck284_48

private theorem validResource284_49 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 49) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 49) 125 55
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_48 coreChunks284_49 coreFlatten284_49 coreCheck284_49

private theorem validResource284_50 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 50) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 50) 136 54
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_49 coreChunks284_50 coreFlatten284_50 coreCheck284_50

private theorem validResource284_51 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 51) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 51) 0 74
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 259 smallOrder284 [3, 5, 7, 11] 1 74 true) coreChunks284_51 coreFlatten284_51 coreCheck284_51

private theorem validResource284_52 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 52) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 52) 0 87
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 259 smallOrder284 [3, 5, 7, 11] 2 87 true) coreChunks284_52 coreFlatten284_52 coreCheck284_52

private theorem validResource284_53 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 53) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 53) 92 87
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_52 coreChunks284_53 coreFlatten284_53 coreCheck284_53

private theorem validResource284_54 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 54) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 54) 0 194
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 259 smallOrder284 [3, 5, 7, 11] 3 194 false) coreChunks284_54 coreFlatten284_54 coreCheck284_54

private theorem validResource284_55 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 55) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 55) 0 96
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 259 smallOrder284 [3, 5, 7, 11] 3 96 true) coreChunks284_55 coreFlatten284_55 coreCheck284_55

private theorem validResource284_56 :
    PrefixResourceValid 259 smallOrder284 [3, 5, 7, 11] (resources284 56) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 259) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) (r := coreResources284 56) 82 96
    dataValid284 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource284_55 coreChunks284_56 coreFlatten284_56 coreCheck284_56

theorem finiteCheck259_284 : finiteIntervalCheck 259 284 smallOrder284 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 259) (U := 284) (O := smallOrder284)
    (ps := [3, 5, 7, 11]) resources284 coreSelector284
  · intro i
    fin_cases i
    · exact validResource284_0
    · exact validResource284_1
    · exact validResource284_2
    · exact validResource284_3
    · exact validResource284_4
    · exact validResource284_5
    · exact validResource284_6
    · exact validResource284_7
    · exact validResource284_8
    · exact validResource284_9
    · exact validResource284_10
    · exact validResource284_11
    · exact validResource284_12
    · exact validResource284_13
    · exact validResource284_14
    · exact validResource284_15
    · exact validResource284_16
    · exact validResource284_17
    · exact validResource284_18
    · exact validResource284_19
    · exact validResource284_20
    · exact validResource284_21
    · exact validResource284_22
    · exact validResource284_23
    · exact validResource284_24
    · exact validResource284_25
    · exact validResource284_26
    · exact validResource284_27
    · exact validResource284_28
    · exact validResource284_29
    · exact validResource284_30
    · exact validResource284_31
    · exact validResource284_32
    · exact validResource284_33
    · exact validResource284_34
    · exact validResource284_35
    · exact validResource284_36
    · exact validResource284_37
    · exact validResource284_38
    · exact validResource284_39
    · exact validResource284_40
    · exact validResource284_41
    · exact validResource284_42
    · exact validResource284_43
    · exact validResource284_44
    · exact validResource284_45
    · exact validResource284_46
    · exact validResource284_47
    · exact validResource284_48
    · exact validResource284_49
    · exact validResource284_50
    · exact validResource284_51
    · exact validResource284_52
    · exact validResource284_53
    · exact validResource284_54
    · exact validResource284_55
    · exact validResource284_56
  · intro b j
    exact resourceRequirements_of_core (coreRequirements284 b j)

theorem exactCertificate259_284 : ExactIntervalCertificate 259 284 smallOrder284 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck259_284
#print axioms smallOrder284_nodup
#print axioms smallOrder284_set
#print axioms finiteCheck259_284
#print axioms exactCertificate259_284
end Erdos883Verified
