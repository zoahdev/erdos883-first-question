import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_17 :
    (List.ofFn coreChunks999_17).flatten =
      (coreData999.take (coreResources999 17).q).drop 173 := by
  decide +kernel

theorem coreCheck999_17 :
    ∀ c : Fin 1, (coreChunks999_17 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 17)) = true := by
  decide +kernel
#print axioms coreFlatten999_17
#print axioms coreCheck999_17
end Erdos883Verified
