import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_1 :
    (List.ofFn coreChunks999_1).flatten =
      (coreData999.take (coreResources999 1).q).drop 107 := by
  decide +kernel

theorem coreCheck999_1 :
    ∀ c : Fin 1, (coreChunks999_1 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 1)) = true := by
  decide +kernel
#print axioms coreFlatten999_1
#print axioms coreCheck999_1
end Erdos883Verified
