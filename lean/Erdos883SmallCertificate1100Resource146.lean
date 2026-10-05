import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_146 :
    (List.ofFn coreChunks1100_146).flatten =
      (coreData1100.take (coreResources1100 146).q).drop 277 := by
  decide +kernel

theorem coreCheck1100_146 :
    ∀ c : Fin 1, (coreChunks1100_146 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 146)) = true := by
  decide +kernel
#print axioms coreFlatten1100_146
#print axioms coreCheck1100_146
end Erdos883Verified
