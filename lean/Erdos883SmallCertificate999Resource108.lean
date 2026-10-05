import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_108 :
    (List.ofFn coreChunks999_108).flatten =
      (coreData999.take (coreResources999 108).q).drop 185 := by
  decide +kernel

theorem coreCheck999_108 :
    ∀ c : Fin 1, (coreChunks999_108 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 108)) = true := by
  decide +kernel
#print axioms coreFlatten999_108
#print axioms coreCheck999_108
end Erdos883Verified
