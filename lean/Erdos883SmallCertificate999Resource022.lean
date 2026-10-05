import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_22 :
    (List.ofFn coreChunks999_22).flatten =
      (coreData999.take (coreResources999 22).q).drop 180 := by
  decide +kernel

theorem coreCheck999_22 :
    ∀ c : Fin 1, (coreChunks999_22 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 22)) = true := by
  decide +kernel
#print axioms coreFlatten999_22
#print axioms coreCheck999_22
end Erdos883Verified
