import Erdos883SmallCertificate158Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck158 : coreOrderPermutationCheck 158 (coreData158.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten158 : (List.ofFn coreMetadataChunks158).flatten = coreData158 := by
  decide +kernel
#print axioms coreOrderCheck158
#print axioms coreMetadataFlatten158
end Erdos883Verified
