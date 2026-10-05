import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_12 :
    (List.ofFn coreChunks999_12).flatten =
      (coreData999.take (coreResources999 12).q).drop 168 := by
  decide +kernel

theorem coreCheck999_12 :
    ∀ c : Fin 1, (coreChunks999_12 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 12)) = true := by
  decide +kernel
#print axioms coreFlatten999_12
#print axioms coreCheck999_12
end Erdos883Verified
