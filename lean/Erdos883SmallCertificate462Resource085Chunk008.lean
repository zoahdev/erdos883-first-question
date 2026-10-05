import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk462_85_8 :
    (coreChunks462_85 8).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 85)) = true := by
  decide +kernel
#print axioms coreCheckChunk462_85_8
end Erdos883Verified
