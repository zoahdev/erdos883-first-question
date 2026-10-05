import Erdos883SmallCertificate1211Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck1211 : coreOrderPermutationCheck 1211 (coreData1211.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten1211 : (List.ofFn coreMetadataChunks1211).flatten = coreData1211 := by
  decide +kernel
#print axioms coreOrderCheck1211
#print axioms coreMetadataFlatten1211
end Erdos883Verified
