import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_24 :
    (List.ofFn coreChunks999_24).flatten =
      (coreData999.take (coreResources999 24).q).drop 182 := by
  decide +kernel

theorem coreCheck999_24 :
    ∀ c : Fin 1, (coreChunks999_24 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 24)) = true := by
  decide +kernel
#print axioms coreFlatten999_24
#print axioms coreCheck999_24
end Erdos883Verified
