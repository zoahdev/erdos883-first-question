import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck93 : coreOrderPermutationCheck 93 (coreData93.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten93 : (List.ofFn coreMetadataChunks93).flatten = coreData93 := by
  decide +kernel
#print axioms coreOrderCheck93
#print axioms coreMetadataFlatten93
end Erdos883Verified
