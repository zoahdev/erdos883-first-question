import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck825_0 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks825 0) = true := by
  decide +kernel
#print axioms coreMetadataCheck825_0
end Erdos883Verified
