import Erdos883SmallCertificate509Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreCheckChunk509_96_0 :
    (coreChunks509_96 0).all
      (coreResourceRowCheck 463 coreData509 (coreResources509 96)) = true := by
  decide +kernel
#print axioms coreCheckChunk509_96_0
end Erdos883Verified
