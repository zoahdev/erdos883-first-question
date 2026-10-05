import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_55 :
    (List.ofFn coreChunks1100_55).flatten =
      (coreData1100.take (coreResources1100 55).q).drop 247 := by
  decide +kernel

theorem coreCheck1100_55 :
    ∀ c : Fin 1, (coreChunks1100_55 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 55)) = true := by
  decide +kernel
#print axioms coreFlatten1100_55
#print axioms coreCheck1100_55
end Erdos883Verified
