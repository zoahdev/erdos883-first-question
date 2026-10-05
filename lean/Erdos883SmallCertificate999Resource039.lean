import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_39 :
    (List.ofFn coreChunks999_39).flatten =
      (coreData999.take (coreResources999 39).q).drop 201 := by
  decide +kernel

theorem coreCheck999_39 :
    ∀ c : Fin 1, (coreChunks999_39 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 39)) = true := by
  decide +kernel
#print axioms coreFlatten999_39
#print axioms coreCheck999_39
end Erdos883Verified
