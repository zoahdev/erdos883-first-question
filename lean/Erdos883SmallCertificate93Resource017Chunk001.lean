import Erdos883SmallCertificate93Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk93_17_1 :
    (coreChunks93_17 1).all
      (coreResourceRowCheck 93 coreData93 (coreResources93 17)) = true := by
  decide +kernel
#print axioms coreCheckChunk93_17_1
end Erdos883Verified
