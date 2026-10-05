import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck825 : coreOrderPermutationCheck 825 (coreData825.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten825 : (List.ofFn coreMetadataChunks825).flatten = coreData825 := by
  decide +kernel
#print axioms coreOrderCheck825
#print axioms coreMetadataFlatten825
end Erdos883Verified
