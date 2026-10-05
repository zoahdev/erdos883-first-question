import Erdos883SmallCertificate825Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk825_151_15 :
    (coreChunks825_151 15).all
      (coreResourceRowCheck 750 coreData825 (coreResources825 151)) = true := by
  decide +kernel
#print axioms coreCheckChunk825_151_15
end Erdos883Verified
