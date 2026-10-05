import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk509_91_2 :
    (coreChunks509_91 2).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 91)) = true := by
  decide +kernel
#print axioms coreCheckChunk509_91_2
end Erdos883Verified
