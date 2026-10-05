import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_188 :
    (List.ofFn coreChunks999_188).flatten =
      (coreData999.take (coreResources999 188).q).drop 319 := by
  decide +kernel

theorem coreCheck999_188 :
    ∀ c : Fin 1, (coreChunks999_188 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 188)) = true := by
  decide +kernel
#print axioms coreFlatten999_188
#print axioms coreCheck999_188
end Erdos883Verified
