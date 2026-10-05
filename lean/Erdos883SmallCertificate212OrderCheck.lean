import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck212 : coreOrderPermutationCheck 212 (coreData212.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten212 : (List.ofFn coreMetadataChunks212).flatten = coreData212 := by
  decide +kernel
#print axioms coreOrderCheck212
#print axioms coreMetadataFlatten212
end Erdos883Verified
