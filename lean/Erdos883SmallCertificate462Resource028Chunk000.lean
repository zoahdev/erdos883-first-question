import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk462_28_0 :
    (coreChunks462_28 0).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 28)) = true := by
  decide +kernel
#print axioms coreCheckChunk462_28_0
end Erdos883Verified
