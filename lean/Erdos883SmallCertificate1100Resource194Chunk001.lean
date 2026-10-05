import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk1100_194_1 :
    (coreChunks1100_194 1).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 194)) = true := by
  decide +kernel
#print axioms coreCheckChunk1100_194_1
end Erdos883Verified
