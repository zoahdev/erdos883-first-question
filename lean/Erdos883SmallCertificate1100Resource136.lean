import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_136 :
    (List.ofFn coreChunks1100_136).flatten =
      (coreData1100.take (coreResources1100 136).q).drop 249 := by
  decide +kernel

theorem coreCheck1100_136 :
    ∀ c : Fin 1, (coreChunks1100_136 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 136)) = true := by
  decide +kernel
#print axioms coreFlatten1100_136
#print axioms coreCheck1100_136
end Erdos883Verified
