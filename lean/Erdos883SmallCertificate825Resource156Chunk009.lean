import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk825_156_9 :
    (coreChunks825_156 9).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 156)) = true := by
  decide +kernel
#print axioms coreCheckChunk825_156_9
end Erdos883Verified
