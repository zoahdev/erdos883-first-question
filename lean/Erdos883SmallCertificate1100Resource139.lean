import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_139 :
    (List.ofFn coreChunks1100_139).flatten =
      (coreData1100.take (coreResources1100 139).q).drop 254 := by
  decide +kernel

theorem coreCheck1100_139 :
    ∀ c : Fin 1, (coreChunks1100_139 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 139)) = true := by
  decide +kernel
#print axioms coreFlatten1100_139
#print axioms coreCheck1100_139
end Erdos883Verified
