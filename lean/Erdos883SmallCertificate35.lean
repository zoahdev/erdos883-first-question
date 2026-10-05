import Erdos883SmallCertificateCoreBridge
import Erdos883SmallCertificate35OrderCheck
import Erdos883SmallCertificate35Metadata000
import Erdos883SmallCertificate35Resource000
import Erdos883SmallCertificate35Resource001
import Erdos883SmallCertificate35Resource002
import Erdos883SmallCertificate35Resource003
import Erdos883SmallCertificate35Resource004
import Erdos883SmallCertificate35Resource005
import Erdos883SmallCertificate35Resource006
import Erdos883SmallCertificate35Resource007
import Erdos883SmallCertificate35Resource008
import Erdos883SmallCertificate35Requirements
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

def smallOrder35 : List ℕ := coreData35.map (·.value)
theorem smallOrder35_nodup : smallOrder35.Nodup := (coreOrderPermutationCheck_sound coreOrderCheck35).1
theorem smallOrder35_set : smallOrder35.toFinset = oddUniverse 35 := (coreOrderPermutationCheck_sound coreOrderCheck35).2
private def resources35 (i : Fin 9) : PrefixResourceData := resourceOfCore (coreResources35 i)
private theorem dataValid35 :
    OddCertificateDataValid [3, 5, 7, 11] (coreData35.map oddDataOfCore) := by
  apply oddCertificateDataValid_of_coreChunks coreMetadataChunks35 coreMetadataFlatten35
  intro c
  fin_cases c
  · exact oddCertificateDataValid_of_coreCheck coreMetadataCheck35_0
#print axioms dataValid35

private theorem validResource35_0 :
    PrefixResourceValid 32 smallOrder35 [3, 5, 7, 11] (resources35 0) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 32) (O := smallOrder35)
    (ps := [3, 5, 7, 11]) (r := coreResources35 0) 0 16
    dataValid35 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 32 smallOrder35 [3, 5, 7, 11] 0 16 true) coreChunks35_0 coreFlatten35_0 coreCheck35_0

private theorem validResource35_1 :
    PrefixResourceValid 32 smallOrder35 [3, 5, 7, 11] (resources35 1) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 32) (O := smallOrder35)
    (ps := [3, 5, 7, 11]) (r := coreResources35 1) 6 16
    dataValid35 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource35_0 coreChunks35_1 coreFlatten35_1 coreCheck35_1

private theorem validResource35_2 :
    PrefixResourceValid 32 smallOrder35 [3, 5, 7, 11] (resources35 2) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 32) (O := smallOrder35)
    (ps := [3, 5, 7, 11]) (r := coreResources35 2) 7 15
    dataValid35 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource35_1 coreChunks35_2 coreFlatten35_2 coreCheck35_2

private theorem validResource35_3 :
    PrefixResourceValid 32 smallOrder35 [3, 5, 7, 11] (resources35 3) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 32) (O := smallOrder35)
    (ps := [3, 5, 7, 11]) (r := coreResources35 3) 8 14
    dataValid35 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource35_2 coreChunks35_3 coreFlatten35_3 coreCheck35_3

private theorem validResource35_4 :
    PrefixResourceValid 32 smallOrder35 [3, 5, 7, 11] (resources35 4) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 32) (O := smallOrder35)
    (ps := [3, 5, 7, 11]) (r := coreResources35 4) 9 13
    dataValid35 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource35_3 coreChunks35_4 coreFlatten35_4 coreCheck35_4

private theorem validResource35_5 :
    PrefixResourceValid 32 smallOrder35 [3, 5, 7, 11] (resources35 5) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 32) (O := smallOrder35)
    (ps := [3, 5, 7, 11]) (r := coreResources35 5) 11 11
    dataValid35 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource35_4 coreChunks35_5 coreFlatten35_5 coreCheck35_5

private theorem validResource35_6 :
    PrefixResourceValid 32 smallOrder35 [3, 5, 7, 11] (resources35 6) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 32) (O := smallOrder35)
    (ps := [3, 5, 7, 11]) (r := coreResources35 6) 12 10
    dataValid35 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource35_5 coreChunks35_6 coreFlatten35_6 coreCheck35_6

private theorem validResource35_7 :
    PrefixResourceValid 32 smallOrder35 [3, 5, 7, 11] (resources35 7) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 32) (O := smallOrder35)
    (ps := [3, 5, 7, 11]) (r := coreResources35 7) 15 7
    dataValid35 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    validResource35_6 coreChunks35_7 coreFlatten35_7 coreCheck35_7

private theorem validResource35_8 :
    PrefixResourceValid 32 smallOrder35 [3, 5, 7, 11] (resources35 8) := by
  exact prefixResourceValid_extend_of_coreChunks (L := 32) (O := smallOrder35)
    (ps := [3, 5, 7, 11]) (r := coreResources35 8) 0 10
    dataValid35 rfl (by decide +kernel) (by decide +kernel) (by decide +kernel)
    (prefixResourceValid_empty 32 smallOrder35 [3, 5, 7, 11] 1 10 true) coreChunks35_8 coreFlatten35_8 coreCheck35_8

theorem finiteCheck32_35 : finiteIntervalCheck 32 35 smallOrder35 [3, 5, 7, 11] := by
  apply finiteIntervalCheck_of_resources (L := 32) (U := 35) (O := smallOrder35)
    (ps := [3, 5, 7, 11]) resources35 coreSelector35
  · intro i
    fin_cases i
    · exact validResource35_0
    · exact validResource35_1
    · exact validResource35_2
    · exact validResource35_3
    · exact validResource35_4
    · exact validResource35_5
    · exact validResource35_6
    · exact validResource35_7
    · exact validResource35_8
  · intro b j
    exact resourceRequirements_of_core (coreRequirements35_0 b j)


theorem exactCertificate32_35 : ExactIntervalCertificate 32 35 smallOrder35 [3, 5, 7, 11] :=
  exactCertificate_of_finiteCheck finiteCheck32_35
#print axioms smallOrder35_nodup
#print axioms smallOrder35_set
#print axioms finiteCheck32_35
#print axioms exactCertificate32_35
end Erdos883Verified
