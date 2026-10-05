import Erdos883SmallCertificate35Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck35_0 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks35 0) = true := by
  decide +kernel
#print axioms coreMetadataCheck35_0
end Erdos883Verified
