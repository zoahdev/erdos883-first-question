import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreOrderCheck509 : coreOrderCheck 509 (coreData509.map (·.value)) = true := by
  decide +kernel

theorem coreMetadataFlatten509 : (List.ofFn coreMetadataChunks509).flatten = coreData509 := by
  decide +kernel
#print axioms coreOrderCheck509
#print axioms coreMetadataFlatten509
end Erdos883Verified
