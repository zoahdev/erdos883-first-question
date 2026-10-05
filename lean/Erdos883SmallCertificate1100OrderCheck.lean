import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck1100 : coreOrderPermutationCheck 1100 (coreData1100.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten1100 : (List.ofFn coreMetadataChunks1100).flatten = coreData1100 := by
  decide +kernel
#print axioms coreOrderCheck1100
#print axioms coreMetadataFlatten1100
end Erdos883Verified
