import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck103 : coreOrderPermutationCheck 103 (coreData103.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten103 : (List.ofFn coreMetadataChunks103).flatten = coreData103 := by
  decide +kernel
#print axioms coreOrderCheck103
#print axioms coreMetadataFlatten103
end Erdos883Verified
