import Erdos883SmallCertificate192Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk192_35_4 :
    (coreChunks192_35 4).all
      (coreResourceRowCheck 175 coreData192 (coreResources192 35)) = true := by
  decide +kernel
#print axioms coreCheckChunk192_35_4
end Erdos883Verified
