import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk462_85_4 :
    (coreChunks462_85 4).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 85)) = true := by
  decide +kernel
#print axioms coreCheckChunk462_85_4
end Erdos883Verified
