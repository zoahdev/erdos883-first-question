import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk462_85_7 :
    (coreChunks462_85 7).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 85)) = true := by
  decide +kernel
#print axioms coreCheckChunk462_85_7
end Erdos883Verified
