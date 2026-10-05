import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_116 :
    (List.ofFn coreChunks999_116).flatten =
      (coreData999.take (coreResources999 116).q).drop 199 := by
  decide +kernel

theorem coreCheck999_116 :
    ∀ c : Fin 1, (coreChunks999_116 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 116)) = true := by
  decide +kernel
#print axioms coreFlatten999_116
#print axioms coreCheck999_116
end Erdos883Verified
