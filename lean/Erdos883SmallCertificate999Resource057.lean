import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_57 :
    (List.ofFn coreChunks999_57).flatten =
      (coreData999.take (coreResources999 57).q).drop 225 := by
  decide +kernel

theorem coreCheck999_57 :
    ∀ c : Fin 1, (coreChunks999_57 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 57)) = true := by
  decide +kernel
#print axioms coreFlatten999_57
#print axioms coreCheck999_57
end Erdos883Verified
