import Erdos883SmallCertificate31Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck31 : coreOrderPermutationCheck 31 (coreData31.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten31 : (List.ofFn coreMetadataChunks31).flatten = coreData31 := by
  decide +kernel
#print axioms coreOrderCheck31
#print axioms coreMetadataFlatten31
end Erdos883Verified
