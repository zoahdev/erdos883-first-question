import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk129_25_2 :
    (coreChunks129_25 2).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 25)) = true := by
  decide +kernel
#print axioms coreCheckChunk129_25_2
end Erdos883Verified
