import Erdos883SmallCertificate212Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk212_43_3 :
    (coreChunks212_43 3).all
      (coreResourceRowCheck 193 coreData212 (coreResources212 43)) = true := by
  decide +kernel
#print axioms coreCheckChunk212_43_3
end Erdos883Verified
