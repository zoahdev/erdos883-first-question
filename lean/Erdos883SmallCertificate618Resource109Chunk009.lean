import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk618_109_9 :
    (coreChunks618_109 9).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 109)) = true := by
  decide +kernel
#print axioms coreCheckChunk618_109_9
end Erdos883Verified
