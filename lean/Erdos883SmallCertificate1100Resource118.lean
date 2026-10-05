import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_118 :
    (List.ofFn coreChunks1100_118).flatten =
      (coreData1100.take (coreResources1100 118).q).drop 222 := by
  decide +kernel

theorem coreCheck1100_118 :
    ∀ c : Fin 1, (coreChunks1100_118 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 118)) = true := by
  decide +kernel
#print axioms coreFlatten1100_118
#print axioms coreCheck1100_118
end Erdos883Verified
