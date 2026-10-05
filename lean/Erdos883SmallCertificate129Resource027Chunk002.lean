import Erdos883SmallCertificate129Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk129_27_2 :
    (coreChunks129_27 2).all
      (coreResourceRowCheck 118 coreData129 (coreResources129 27)) = true := by
  decide +kernel
#print axioms coreCheckChunk129_27_2
end Erdos883Verified
