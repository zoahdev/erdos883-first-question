import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck999_1 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks999 1) = true := by
  decide +kernel
#print axioms coreMetadataCheck999_1
end Erdos883Verified
