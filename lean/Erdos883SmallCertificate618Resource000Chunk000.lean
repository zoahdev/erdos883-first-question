import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk618_0_0 :
    (coreChunks618_0 0).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 0)) = true := by
  decide +kernel
#print axioms coreCheckChunk618_0_0
end Erdos883Verified
