import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_48 :
    (List.ofFn coreChunks1100_48).flatten =
      (coreData1100.take (coreResources1100 48).q).drop 240 := by
  decide +kernel

theorem coreCheck1100_48 :
    ∀ c : Fin 1, (coreChunks1100_48 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 48)) = true := by
  decide +kernel
#print axioms coreFlatten1100_48
#print axioms coreCheck1100_48
end Erdos883Verified
