import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk825_149_0 :
    (coreChunks825_149 0).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 149)) = true := by
  decide +kernel
#print axioms coreCheckChunk825_149_0
end Erdos883Verified
