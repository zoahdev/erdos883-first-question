import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck93_0 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks93 0) = true := by
  decide +kernel
#print axioms coreMetadataCheck93_0
end Erdos883Verified
