import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk1100_204_7 :
    (coreChunks1100_204 7).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 204)) = true := by
  decide +kernel
#print axioms coreCheckChunk1100_204_7
end Erdos883Verified
