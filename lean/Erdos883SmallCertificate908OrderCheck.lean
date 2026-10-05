import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck908 : coreOrderPermutationCheck 908 (coreData908.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten908 : (List.ofFn coreMetadataChunks908).flatten = coreData908 := by
  decide +kernel
#print axioms coreOrderCheck908
#print axioms coreMetadataFlatten908
end Erdos883Verified
