import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_64 :
    (List.ofFn coreChunks1100_64).flatten =
      (coreData1100.take (coreResources1100 64).q).drop 268 := by
  decide +kernel

theorem coreCheck1100_64 :
    ∀ c : Fin 1, (coreChunks1100_64 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 64)) = true := by
  decide +kernel
#print axioms coreFlatten1100_64
#print axioms coreCheck1100_64
end Erdos883Verified
