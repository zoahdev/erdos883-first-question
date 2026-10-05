import Erdos883SmallCertificate31Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck31_0 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks31 0) = true := by
  decide +kernel
#print axioms coreMetadataCheck31_0
end Erdos883Verified
