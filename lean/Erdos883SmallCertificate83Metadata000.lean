import Erdos883SmallCertificate83Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck83_0 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks83 0) = true := by
  decide +kernel
#print axioms coreMetadataCheck83_0
end Erdos883Verified
