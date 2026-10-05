import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk825_150_16 :
    (coreChunks825_150 16).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 150)) = true := by
  decide +kernel
#print axioms coreCheckChunk825_150_16
end Erdos883Verified
