import Erdos883SmallCertificate114Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck114_0 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks114 0) = true := by
  decide +kernel
#print axioms coreMetadataCheck114_0
end Erdos883Verified
