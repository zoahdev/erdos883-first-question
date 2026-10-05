import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk509_93_8 :
    (coreChunks509_93 8).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 93)) = true := by
  decide +kernel
#print axioms coreCheckChunk509_93_8
end Erdos883Verified
