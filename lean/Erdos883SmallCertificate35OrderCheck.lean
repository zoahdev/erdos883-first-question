import Erdos883SmallCertificate35Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck35 : coreOrderPermutationCheck 35 (coreData35.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten35 : (List.ofFn coreMetadataChunks35).flatten = coreData35 := by
  decide +kernel
#print axioms coreOrderCheck35
#print axioms coreMetadataFlatten35
end Erdos883Verified
