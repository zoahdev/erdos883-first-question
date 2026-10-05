import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck908_3 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks908 3) = true := by
  decide +kernel
#print axioms coreMetadataCheck908_3
end Erdos883Verified
