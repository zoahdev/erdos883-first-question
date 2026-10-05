import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk192_36_0 :
    (coreChunks192_36 0).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 36)) = true := by
  decide +kernel
#print axioms coreCheckChunk192_36_0
end Erdos883Verified
