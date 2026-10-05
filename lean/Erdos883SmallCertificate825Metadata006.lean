import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck825_6 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks825 6) = true := by
  decide +kernel
#print axioms coreMetadataCheck825_6
end Erdos883Verified
