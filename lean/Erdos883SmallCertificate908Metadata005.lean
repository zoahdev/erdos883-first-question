import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck908_5 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks908 5) = true := by
  decide +kernel
#print axioms coreMetadataCheck908_5
end Erdos883Verified
