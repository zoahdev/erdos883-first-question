import Erdos883SmallCertificate103Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk103_20_2 :
    (coreChunks103_20 2).all
      (coreResourceRowCheck 94 coreData103 (coreResources103 20)) = true := by
  decide +kernel
#print axioms coreCheckChunk103_20_2
end Erdos883Verified
