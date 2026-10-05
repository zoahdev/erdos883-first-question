import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck174 : coreOrderPermutationCheck 174 (coreData174.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten174 : (List.ofFn coreMetadataChunks174).flatten = coreData174 := by
  decide +kernel
#print axioms coreOrderCheck174
#print axioms coreMetadataFlatten174
end Erdos883Verified
