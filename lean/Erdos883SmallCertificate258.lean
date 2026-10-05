import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate258Resource000
import Erdos883SmallCertificate258Resource001
import Erdos883SmallCertificate258Resource002
import Erdos883SmallCertificate258Resource003
import Erdos883SmallCertificate258Resource004
import Erdos883SmallCertificate258Resource005
import Erdos883SmallCertificate258Resource006
import Erdos883SmallCertificate258Resource007
import Erdos883SmallCertificate258Resource008
import Erdos883SmallCertificate258Resource009
import Erdos883SmallCertificate258Resource010
import Erdos883SmallCertificate258Resource011
import Erdos883SmallCertificate258Resource012
import Erdos883SmallCertificate258Resource013
import Erdos883SmallCertificate258Resource014
import Erdos883SmallCertificate258Resource015
import Erdos883SmallCertificate258Resource016
import Erdos883SmallCertificate258Resource017
import Erdos883SmallCertificate258Resource018
import Erdos883SmallCertificate258Resource019
import Erdos883SmallCertificate258Resource020
import Erdos883SmallCertificate258Resource021
import Erdos883SmallCertificate258Resource022
import Erdos883SmallCertificate258Resource023
import Erdos883SmallCertificate258Resource024
import Erdos883SmallCertificate258Resource025
import Erdos883SmallCertificate258Resource026
import Erdos883SmallCertificate258Resource027
import Erdos883SmallCertificate258Resource028
import Erdos883SmallCertificate258Resource029
import Erdos883SmallCertificate258Resource030
import Erdos883SmallCertificate258Resource031
import Erdos883SmallCertificate258Resource032
import Erdos883SmallCertificate258Resource033
import Erdos883SmallCertificate258Resource034
import Erdos883SmallCertificate258Resource035
import Erdos883SmallCertificate258Resource036
import Erdos883SmallCertificate258Resource037
import Erdos883SmallCertificate258Resource038
import Erdos883SmallCertificate258Resource039
import Erdos883SmallCertificate258Resource040
import Erdos883SmallCertificate258Resource041
import Erdos883SmallCertificate258Resource042
import Erdos883SmallCertificate258Resource043
import Erdos883SmallCertificate258Resource044
import Erdos883SmallCertificate258Resource045
import Erdos883SmallCertificate258Resource046
import Erdos883SmallCertificate258Resource047
import Erdos883SmallCertificate258Resource048
import Erdos883SmallCertificate258Resource049
import Erdos883SmallCertificate258Resource050
import Erdos883SmallCertificate258Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder258 : List ℕ := coreData258.map (·.value)
theorem smallOrder258_nodup : smallOrder258.Nodup := by decide +kernel
theorem smallOrder258_set : smallOrder258.toFinset = oddUniverse 258 := by decide +kernel
private def resources258 (i : Fin 51) : PrefixResourceData := resourceOfCore (coreResources258 i)
private theorem dataValid258 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData258.map oddDataOfCore) := by
  unfold OddCertificateDataValid
  decide +kernel
#print axioms dataValid258

private theorem validResource258_0 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 0) 0 233
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 235 smallOrder258 [3, 5, 7, 11] 0 233 false) coreChunks258_0 coreFlatten258_0 coreCheck258_0

private theorem validResource258_1 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 1) 26 233
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_0 coreChunks258_1 coreFlatten258_1 coreCheck258_1

private theorem validResource258_2 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 2) 27 232
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_1 coreChunks258_2 coreFlatten258_2 coreCheck258_2

private theorem validResource258_3 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 3) 35 231
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_2 coreChunks258_3 coreFlatten258_3 coreCheck258_3

private theorem validResource258_4 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 4) 55 186
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_3 coreChunks258_4 coreFlatten258_4 coreCheck258_4

private theorem validResource258_5 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 5) 57 176
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_4 coreChunks258_5 coreFlatten258_5 coreCheck258_5

private theorem validResource258_6 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 6) 58 175
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_5 coreChunks258_6 coreFlatten258_6 coreCheck258_6

private theorem validResource258_7 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 7) 60 174
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_6 coreChunks258_7 coreFlatten258_7 coreCheck258_7

private theorem validResource258_8 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 8) 61 173
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_7 coreChunks258_8 coreFlatten258_8 coreCheck258_8

private theorem validResource258_9 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 9) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 9) 62 169
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_8 coreChunks258_9 coreFlatten258_9 coreCheck258_9

private theorem validResource258_10 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 10) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 10) 63 163
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_9 coreChunks258_10 coreFlatten258_10 coreCheck258_10

private theorem validResource258_11 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 11) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 11) 64 162
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_10 coreChunks258_11 coreFlatten258_11 coreCheck258_11

private theorem validResource258_12 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 12) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 12) 65 160
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_11 coreChunks258_12 coreFlatten258_12 coreCheck258_12

private theorem validResource258_13 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 13) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 13) 0 115
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 235 smallOrder258 [3, 5, 7, 11] 0 115 true) coreChunks258_13 coreFlatten258_13 coreCheck258_13

private theorem validResource258_14 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 14) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 14) 40 115
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_13 coreChunks258_14 coreFlatten258_14 coreCheck258_14

private theorem validResource258_15 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 15) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 15) 41 114
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_14 coreChunks258_15 coreFlatten258_15 coreCheck258_15

private theorem validResource258_16 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 16) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 16) 44 113
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_15 coreChunks258_16 coreFlatten258_16 coreCheck258_16

private theorem validResource258_17 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 17) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 17) 45 112
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_16 coreChunks258_17 coreFlatten258_17 coreCheck258_17

private theorem validResource258_18 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 18) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 18) 46 111
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_17 coreChunks258_18 coreFlatten258_18 coreCheck258_18

private theorem validResource258_19 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 19) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 19) 47 110
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_18 coreChunks258_19 coreFlatten258_19 coreCheck258_19

private theorem validResource258_20 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 20) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 20) 48 108
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_19 coreChunks258_20 coreFlatten258_20 coreCheck258_20

private theorem validResource258_21 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 21) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 21) 49 106
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_20 coreChunks258_21 coreFlatten258_21 coreCheck258_21

private theorem validResource258_22 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 22) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 22) 50 105
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_21 coreChunks258_22 coreFlatten258_22 coreCheck258_22

private theorem validResource258_23 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 23) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 23) 52 102
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_22 coreChunks258_23 coreFlatten258_23 coreCheck258_23

private theorem validResource258_24 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 24) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 24) 54 98
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_23 coreChunks258_24 coreFlatten258_24 coreCheck258_24

private theorem validResource258_25 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 25) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 25) 55 92
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_24 coreChunks258_25 coreFlatten258_25 coreCheck258_25

private theorem validResource258_26 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 26) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 26) 57 87
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_25 coreChunks258_26 coreFlatten258_26 coreCheck258_26

private theorem validResource258_27 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 27) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 27) 61 86
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_26 coreChunks258_27 coreFlatten258_27 coreCheck258_27

private theorem validResource258_28 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 28) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 28) 62 84
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_27 coreChunks258_28 coreFlatten258_28 coreCheck258_28

private theorem validResource258_29 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 29) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 29) 63 81
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_28 coreChunks258_29 coreFlatten258_29 coreCheck258_29

private theorem validResource258_30 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 30) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 30) 64 80
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_29 coreChunks258_30 coreFlatten258_30 coreCheck258_30

private theorem validResource258_31 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 31) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 31) 65 79
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_30 coreChunks258_31 coreFlatten258_31 coreCheck258_31

private theorem validResource258_32 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 32) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 32) 67 78
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_31 coreChunks258_32 coreFlatten258_32 coreCheck258_32

private theorem validResource258_33 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 33) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 33) 70 76
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_32 coreChunks258_33 coreFlatten258_33 coreCheck258_33

private theorem validResource258_34 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 34) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 34) 71 74
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_33 coreChunks258_34 coreFlatten258_34 coreCheck258_34

private theorem validResource258_35 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 35) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 35) 75 72
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_34 coreChunks258_35 coreFlatten258_35 coreCheck258_35

private theorem validResource258_36 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 36) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 36) 77 71
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_35 coreChunks258_36 coreFlatten258_36 coreCheck258_36

private theorem validResource258_37 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 37) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 37) 79 70
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_36 coreChunks258_37 coreFlatten258_37 coreCheck258_37

private theorem validResource258_38 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 38) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 38) 81 69
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_37 coreChunks258_38 coreFlatten258_38 coreCheck258_38

private theorem validResource258_39 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 39) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 39) 86 67
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_38 coreChunks258_39 coreFlatten258_39 coreCheck258_39

private theorem validResource258_40 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 40) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 40) 91 53
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_39 coreChunks258_40 coreFlatten258_40 coreCheck258_40

private theorem validResource258_41 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 41) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 41) 98 52
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_40 coreChunks258_41 coreFlatten258_41 coreCheck258_41

private theorem validResource258_42 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 42) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 42) 104 51
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_41 coreChunks258_42 coreFlatten258_42 coreCheck258_42

private theorem validResource258_43 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 43) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 43) 111 50
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_42 coreChunks258_43 coreFlatten258_43 coreCheck258_43

private theorem validResource258_44 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 44) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 44) 124 49
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_43 coreChunks258_44 coreFlatten258_44 coreCheck258_44

private theorem validResource258_45 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 45) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 45) 0 67
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 235 smallOrder258 [3, 5, 7, 11] 1 67 true) coreChunks258_45 coreFlatten258_45 coreCheck258_45

private theorem validResource258_46 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 46) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 46) 0 78
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 235 smallOrder258 [3, 5, 7, 11] 2 78 true) coreChunks258_46 coreFlatten258_46 coreCheck258_46

private theorem validResource258_47 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 47) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 47) 83 78
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_46 coreChunks258_47 coreFlatten258_47 coreCheck258_47

private theorem validResource258_48 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 48) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 48) 0 175
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 235 smallOrder258 [3, 5, 7, 11] 3 175 false) coreChunks258_48 coreFlatten258_48 coreCheck258_48

private theorem validResource258_49 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 49) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 49) 0 86
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 235 smallOrder258 [3, 5, 7, 11] 3 86 true) coreChunks258_49 coreFlatten258_49 coreCheck258_49

private theorem validResource258_50 :
    PrefixResourceValid 235 smallOrder258 [3, 5, 7, 11] (resources258 50) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 235) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) (r := coreResources258 50) 74 86
    dataValid258 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource258_49 coreChunks258_50 coreFlatten258_50 coreCheck258_50

theorem finiteCheck235_258 : finiteIntervalCheck 235 258 smallOrder258 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 235) (U := 258) (O := smallOrder258)
    (ps := [3, 5, 7, 11]) resources258 coreSelector258
  · intro i
    fin_cases i
    · exact validResource258_0
    · exact validResource258_1
    · exact validResource258_2
    · exact validResource258_3
    · exact validResource258_4
    · exact validResource258_5
    · exact validResource258_6
    · exact validResource258_7
    · exact validResource258_8
    · exact validResource258_9
    · exact validResource258_10
    · exact validResource258_11
    · exact validResource258_12
    · exact validResource258_13
    · exact validResource258_14
    · exact validResource258_15
    · exact validResource258_16
    · exact validResource258_17
    · exact validResource258_18
    · exact validResource258_19
    · exact validResource258_20
    · exact validResource258_21
    · exact validResource258_22
    · exact validResource258_23
    · exact validResource258_24
    · exact validResource258_25
    · exact validResource258_26
    · exact validResource258_27
    · exact validResource258_28
    · exact validResource258_29
    · exact validResource258_30
    · exact validResource258_31
    · exact validResource258_32
    · exact validResource258_33
    · exact validResource258_34
    · exact validResource258_35
    · exact validResource258_36
    · exact validResource258_37
    · exact validResource258_38
    · exact validResource258_39
    · exact validResource258_40
    · exact validResource258_41
    · exact validResource258_42
    · exact validResource258_43
    · exact validResource258_44
    · exact validResource258_45
    · exact validResource258_46
    · exact validResource258_47
    · exact validResource258_48
    · exact validResource258_49
    · exact validResource258_50
  · intro b j
    exact resourceRequirements_of_core (coreRequirements258 b j)

theorem exactCertificate235_258 : ExactIntervalCertificate 235 258 smallOrder258 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck235_258
#print axioms smallOrder258_nodup
#print axioms smallOrder258_set
#print axioms finiteCheck235_258
#print axioms exactCertificate235_258
end Erdos883Verified
