import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_96 :
    (List.ofFn coreChunks1100_96).flatten =
      (coreData1100.take (coreResources1100 96).q).drop 187 := by
  decide +kernel

theorem coreCheck1100_96 :
    ∀ c : Fin 1, (coreChunks1100_96 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 96)) = true := by
  decide +kernel
#print axioms coreFlatten1100_96
#print axioms coreCheck1100_96
end Erdos883Verified
