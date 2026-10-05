import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_119 :
    (List.ofFn coreChunks1100_119).flatten =
      (coreData1100.take (coreResources1100 119).q).drop 223 := by
  decide +kernel

theorem coreCheck1100_119 :
    ∀ c : Fin 1, (coreChunks1100_119 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 119)) = true := by
  decide +kernel
#print axioms coreFlatten1100_119
#print axioms coreCheck1100_119
end Erdos883Verified
