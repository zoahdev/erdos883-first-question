import Erdos883SmallCertificate561Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk561_106_6 :
    (coreChunks561_106 6).all
      (coreResourceRowCheck 510 coreData561 (coreResources561 106)) = true := by
  decide +kernel
#print axioms coreCheckChunk561_106_6
end Erdos883Verified
