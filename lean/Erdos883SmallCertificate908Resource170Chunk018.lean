import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk908_170_18 :
    (coreChunks908_170 18).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 170)) = true := by
  decide +kernel
#print axioms coreCheckChunk908_170_18
end Erdos883Verified
