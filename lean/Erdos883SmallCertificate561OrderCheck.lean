import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck561 : coreOrderCheck 561 (coreData561.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten561 : (List.ofFn coreMetadataChunks561).flatten = coreData561 := by
  decide +kernel
#print axioms coreOrderCheck561
#print axioms coreMetadataFlatten561
end Erdos883Verified
