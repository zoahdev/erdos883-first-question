import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck83 : coreOrderPermutationCheck 83 (coreData83.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten83 : (List.ofFn coreMetadataChunks83).flatten = coreData83 := by
  decide +kernel
#print axioms coreOrderCheck83
#print axioms coreMetadataFlatten83
end Erdos883Verified
