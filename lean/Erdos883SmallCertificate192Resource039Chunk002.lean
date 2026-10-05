import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk192_39_2 :
    (coreChunks192_39 2).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 39)) = true := by
  decide +kernel
#print axioms coreCheckChunk192_39_2
end Erdos883Verified
