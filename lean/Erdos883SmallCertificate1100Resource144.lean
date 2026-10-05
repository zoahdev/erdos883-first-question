import Erdos883SmallCertificate1100Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten1100_144 :
    (List.ofFn coreChunks1100_144).flatten =
      (coreData1100.take (coreResources1100 144).q).drop 275 := by
  decide +kernel

theorem coreCheck1100_144 :
    ∀ c : Fin 1, (coreChunks1100_144 c).all
      (coreResourceRowCheck 1000 coreData1100 (coreResources1100 144)) = true := by
  decide +kernel
#print axioms coreFlatten1100_144
#print axioms coreCheck1100_144
end Erdos883Verified
