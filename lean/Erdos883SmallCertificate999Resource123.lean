import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_123 :
    (List.ofFn coreChunks999_123).flatten =
      (coreData999.take (coreResources999 123).q).drop 211 := by
  decide +kernel

theorem coreCheck999_123 :
    ∀ c : Fin 1, (coreChunks999_123 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 123)) = true := by
  decide +kernel
#print axioms coreFlatten999_123
#print axioms coreCheck999_123
end Erdos883Verified
