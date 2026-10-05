import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck212_1 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks212 1) = true := by
  decide +kernel
#print axioms coreMetadataCheck212_1
end Erdos883Verified
