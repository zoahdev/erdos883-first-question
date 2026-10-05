import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_130 :
    (List.ofFn coreChunks1100_130).flatten =
      (coreData1100.take (coreResources1100 130).q).drop 243 := by
  decide +kernel

theorem coreCheck1100_130 :
    ∀ c : Fin 1, (coreChunks1100_130 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 130)) = true := by
  decide +kernel
#print axioms coreFlatten1100_130
#print axioms coreCheck1100_130
end Erdos883Verified
