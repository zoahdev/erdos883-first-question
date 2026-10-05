import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_181 :
    (List.ofFn coreChunks999_181).flatten =
      (coreData999.take (coreResources999 181).q).drop 429 := by
  decide +kernel

theorem coreCheck999_181 :
    ∀ c : Fin 1, (coreChunks999_181 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 181)) = true := by
  decide +kernel
#print axioms coreFlatten999_181
#print axioms coreCheck999_181
end Erdos883Verified
