import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_9 :
    (List.ofFn coreChunks999_9).flatten =
      (coreData999.take (coreResources999 9).q).drop 135 := by
  decide +kernel

theorem coreCheck999_9 :
    ∀ c : Fin 2, (coreChunks999_9 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 9)) = true := by
  decide +kernel
#print axioms coreFlatten999_9
#print axioms coreCheck999_9
end Erdos883Verified
