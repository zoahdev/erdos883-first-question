import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk825_150_11 :
    (coreChunks825_150 11).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 150)) = true := by
  decide +kernel
#print axioms coreCheckChunk825_150_11
end Erdos883Verified
