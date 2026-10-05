import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk825_155_8 :
    (coreChunks825_155 8).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 155)) = true := by
  decide +kernel
#print axioms coreCheckChunk825_155_8
end Erdos883Verified
