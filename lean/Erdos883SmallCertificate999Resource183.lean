import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_183 :
    (List.ofFn coreChunks999_183).flatten =
      (coreData999.take (coreResources999 183).q).drop 439 := by
  decide +kernel

theorem coreCheck999_183 :
    ∀ c : Fin 1, (coreChunks999_183 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 183)) = true := by
  decide +kernel
#print axioms coreFlatten999_183
#print axioms coreCheck999_183
end Erdos883Verified
