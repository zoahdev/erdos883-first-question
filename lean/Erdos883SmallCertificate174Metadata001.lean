import Erdos883SmallCertificate174Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreMetadataCheck174_1 :
    coreMetadataCheck [3, 5, 7, 11] (coreMetadataChunks174 1) = true := by
  decide +kernel
#print axioms coreMetadataCheck174_1
end Erdos883Verified
