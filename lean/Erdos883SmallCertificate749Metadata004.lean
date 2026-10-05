import Erdos883SmallCertificate749Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck749_4 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks749 4) = true := by
  decide +kernel
#print axioms coreMetadataCheck749_4
end Erdos883Verified
