import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_166 :
    (List.ofFn coreChunks1100_166).flatten =
      (coreData1100.take (coreResources1100 166).q).drop 338 := by
  decide +kernel

theorem coreCheck1100_166 :
    ∀ c : Fin 1, (coreChunks1100_166 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 166)) = true := by
  decide +kernel
#print axioms coreFlatten1100_166
#print axioms coreCheck1100_166
end Erdos883Verified
