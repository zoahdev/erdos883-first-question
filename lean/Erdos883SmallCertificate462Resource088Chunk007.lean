import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk462_88_7 :
    (coreChunks462_88 7).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 88)) = true := by
  decide +kernel
#print axioms coreCheckChunk462_88_7
end Erdos883Verified
