import Erdos883SmallCertificate92Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk92_16_0 :
    (coreChunks92_16 0).all
      (coreResourceRowCheck 84 coreData92 (coreResources92 16)) = true := by
  decide +kernel
#print axioms coreCheckChunk92_16_0
end Erdos883Verified
