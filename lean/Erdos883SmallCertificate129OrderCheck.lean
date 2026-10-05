import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck129 : coreOrderPermutationCheck 129 (coreData129.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten129 : (List.ofFn coreMetadataChunks129).flatten = coreData129 := by
  decide +kernel
#print axioms coreOrderCheck129
#print axioms coreMetadataFlatten129
end Erdos883Verified
