import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_165 :
    (List.ofFn coreChunks999_165).flatten =
      (coreData999.take (coreResources999 165).q).drop 314 := by
  decide +kernel

theorem coreCheck999_165 :
    ∀ c : Fin 1, (coreChunks999_165 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 165)) = true := by
  decide +kernel
#print axioms coreFlatten999_165
#print axioms coreCheck999_165
end Erdos883Verified
