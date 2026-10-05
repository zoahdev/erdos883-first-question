import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_84 :
    (List.ofFn coreChunks999_84).flatten =
      (coreData999.take (coreResources999 84).q).drop 153 := by
  decide +kernel

theorem coreCheck999_84 :
    ∀ c : Fin 1, (coreChunks999_84 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 84)) = true := by
  decide +kernel
#print axioms coreFlatten999_84
#print axioms coreCheck999_84
end Erdos883Verified
