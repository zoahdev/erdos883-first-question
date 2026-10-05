import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk618_110_10 :
    (coreChunks618_110 10).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 110)) = true := by
  decide +kernel
#print axioms coreCheckChunk618_110_10
end Erdos883Verified
