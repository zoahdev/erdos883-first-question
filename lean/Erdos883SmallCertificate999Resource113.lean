import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_113 :
    (List.ofFn coreChunks999_113).flatten =
      (coreData999.take (coreResources999 113).q).drop 196 := by
  decide +kernel

theorem coreCheck999_113 :
    ∀ c : Fin 1, (coreChunks999_113 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 113)) = true := by
  decide +kernel
#print axioms coreFlatten999_113
#print axioms coreCheck999_113
end Erdos883Verified
