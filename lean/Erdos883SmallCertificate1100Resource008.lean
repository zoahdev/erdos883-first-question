import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_8 :
    (List.ofFn coreChunks1100_8).flatten =
      (coreData1100.take (coreResources1100 8).q).drop 179 := by
  decide +kernel

theorem coreCheck1100_8 :
    ∀ c : Fin 1, (coreChunks1100_8 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 8)) = true := by
  decide +kernel
#print axioms coreFlatten1100_8
#print axioms coreCheck1100_8
end Erdos883Verified
