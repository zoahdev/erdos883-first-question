import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk825_56_3 :
    (coreChunks825_56 3).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 56)) = true := by
  decide +kernel
#print axioms coreCheckChunk825_56_3
end Erdos883Verified
