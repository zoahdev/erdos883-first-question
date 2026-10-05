import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck749 : coreOrderPermutationCheck 749 (coreData749.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten749 : (List.ofFn coreMetadataChunks749).flatten = coreData749 := by
  decide +kernel
#print axioms coreOrderCheck749
#print axioms coreMetadataFlatten749
end Erdos883Verified
