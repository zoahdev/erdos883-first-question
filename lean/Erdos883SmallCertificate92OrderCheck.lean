import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck92 : coreOrderPermutationCheck 92 (coreData92.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten92 : (List.ofFn coreMetadataChunks92).flatten = coreData92 := by
  decide +kernel
#print axioms coreOrderCheck92
#print axioms coreMetadataFlatten92
end Erdos883Verified
