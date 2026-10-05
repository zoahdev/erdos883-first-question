import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck908_7 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks908 7) = true := by
  decide +kernel
#print axioms coreMetadataCheck908_7
end Erdos883Verified
