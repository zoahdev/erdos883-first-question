import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_46 :
    (List.ofFn coreChunks1100_46).flatten =
      (coreData1100.take (coreResources1100 46).q).drop 238 := by
  decide +kernel

theorem coreCheck1100_46 :
    ∀ c : Fin 1, (coreChunks1100_46 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 46)) = true := by
  decide +kernel
#print axioms coreFlatten1100_46
#print axioms coreCheck1100_46
end Erdos883Verified
