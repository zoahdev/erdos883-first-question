import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck999 : coreOrderPermutationCheck 999 (coreData999.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten999 : (List.ofFn coreMetadataChunks999).flatten = coreData999 := by
  decide +kernel
#print axioms coreOrderCheck999
#print axioms coreMetadataFlatten999
end Erdos883Verified
