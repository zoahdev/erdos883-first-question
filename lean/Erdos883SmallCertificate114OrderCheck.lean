import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck114 : coreOrderPermutationCheck 114 (coreData114.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten114 : (List.ofFn coreMetadataChunks114).flatten = coreData114 := by
  decide +kernel
#print axioms coreOrderCheck114
#print axioms coreMetadataFlatten114
end Erdos883Verified
