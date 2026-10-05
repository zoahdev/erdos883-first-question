import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk103_20_1 :
    (coreChunks103_20 1).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 20)) = true := by
  decide +kernel
#print axioms coreCheckChunk103_20_1
end Erdos883Verified
