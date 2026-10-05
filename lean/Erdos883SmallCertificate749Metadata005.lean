import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck749_5 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks749 5) = true := by
  decide +kernel
#print axioms coreMetadataCheck749_5
end Erdos883Verified
