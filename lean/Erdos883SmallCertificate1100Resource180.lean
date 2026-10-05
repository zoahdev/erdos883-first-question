import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_180 :
    (List.ofFn coreChunks1100_180).flatten =
      (coreData1100.take (coreResources1100 180).q).drop 443 := by
  decide +kernel

theorem coreCheck1100_180 :
    ∀ c : Fin 1, (coreChunks1100_180 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 180)) = true := by
  decide +kernel
#print axioms coreFlatten1100_180
#print axioms coreCheck1100_180
end Erdos883Verified
