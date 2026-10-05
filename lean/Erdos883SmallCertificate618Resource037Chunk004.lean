import Erdos883SmallCertificate618Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk618_37_4 :
    (coreChunks618_37 4).all
      (coreResourceRowCheck 562 coreData618 (coreResources618 37)) = true := by
  decide +kernel
#print axioms coreCheckChunk618_37_4
end Erdos883Verified
