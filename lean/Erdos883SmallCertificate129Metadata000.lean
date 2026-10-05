import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck129_0 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks129 0) = true := by
  decide +kernel
#print axioms coreMetadataCheck129_0
end Erdos883Verified
