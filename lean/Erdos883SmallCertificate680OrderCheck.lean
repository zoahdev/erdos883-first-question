import Erdos883SmallCertificate680Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck680 : coreOrderPermutationCheck 680 (coreData680.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten680 : (List.ofFn coreMetadataChunks680).flatten = coreData680 := by
  decide +kernel
#print axioms coreOrderCheck680
#print axioms coreMetadataFlatten680
end Erdos883Verified
