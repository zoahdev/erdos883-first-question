import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_28 :
    (List.ofFn coreChunks999_28).flatten =
      (coreData999.take (coreResources999 28).q).drop 186 := by
  decide +kernel

theorem coreCheck999_28 :
    ∀ c : Fin 1, (coreChunks999_28 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 28)) = true := by
  decide +kernel
#print axioms coreFlatten999_28
#print axioms coreCheck999_28
end Erdos883Verified
