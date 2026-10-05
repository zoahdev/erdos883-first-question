import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk1100_195_3 :
    (coreChunks1100_195 3).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 195)) = true := by
  decide +kernel
#print axioms coreCheckChunk1100_195_3
end Erdos883Verified
