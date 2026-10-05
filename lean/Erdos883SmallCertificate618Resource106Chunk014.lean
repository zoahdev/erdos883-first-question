import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk618_106_14 :
    (coreChunks618_106 14).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 106)) = true := by
  decide +kernel
#print axioms coreCheckChunk618_106_14
end Erdos883Verified
