import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk618_107_8 :
    (coreChunks618_107 8).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 107)) = true := by
  decide +kernel
#print axioms coreCheckChunk618_107_8
end Erdos883Verified
