import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_173 :
    (List.ofFn coreChunks1100_173).flatten =
      (coreData1100.take (coreResources1100 173).q).drop 366 := by
  decide +kernel

theorem coreCheck1100_173 :
    ∀ c : Fin 2, (coreChunks1100_173 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 173)) = true := by
  decide +kernel
#print axioms coreFlatten1100_173
#print axioms coreCheck1100_173
end Erdos883Verified
