import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck192 : coreOrderPermutationCheck 192 (coreData192.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten192 : (List.ofFn coreMetadataChunks192).flatten = coreData192 := by
  decide +kernel
#print axioms coreOrderCheck192
#print axioms coreMetadataFlatten192
end Erdos883Verified
