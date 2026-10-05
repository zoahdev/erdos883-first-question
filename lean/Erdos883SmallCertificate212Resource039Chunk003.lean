import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk212_39_3 :
    (coreChunks212_39 3).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 39)) = true := by
  decide +kernel
#print axioms coreCheckChunk212_39_3
end Erdos883Verified
