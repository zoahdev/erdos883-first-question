import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk908_176_4 :
    (coreChunks908_176 4).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 176)) = true := by
  decide +kernel
#print axioms coreCheckChunk908_176_4
end Erdos883Verified
