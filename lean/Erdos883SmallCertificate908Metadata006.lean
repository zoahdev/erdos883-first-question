import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck908_6 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks908 6) = true := by
  decide +kernel
#print axioms coreMetadataCheck908_6
end Erdos883Verified
