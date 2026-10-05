import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk908_171_6 :
    (coreChunks908_171 6).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 171)) = true := by
  decide +kernel
#print axioms coreCheckChunk908_171_6
end Erdos883Verified
