import Erdos883SmallCertificate908Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk908_175_6 :
    (coreChunks908_175 6).all
      (coreResourceRowCheck 826 coreData908 (coreResources908 175)) = true := by
  decide +kernel
#print axioms coreCheckChunk908_175_6
end Erdos883Verified
