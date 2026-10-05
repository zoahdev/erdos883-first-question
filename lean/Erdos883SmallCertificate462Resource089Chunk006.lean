import Erdos883SmallCertificate462Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk462_89_6 :
    (coreChunks462_89 6).all
      (coreResourceRowCheck 420 coreData462 (coreResources462 89)) = true := by
  decide +kernel
#print axioms coreCheckChunk462_89_6
end Erdos883Verified
