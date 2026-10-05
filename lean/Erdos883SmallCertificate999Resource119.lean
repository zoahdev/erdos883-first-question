import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_119 :
    (List.ofFn coreChunks999_119).flatten =
      (coreData999.take (coreResources999 119).q).drop 202 := by
  decide +kernel

theorem coreCheck999_119 :
    ∀ c : Fin 1, (coreChunks999_119 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 119)) = true := by
  decide +kernel
#print axioms coreFlatten999_119
#print axioms coreCheck999_119
end Erdos883Verified
