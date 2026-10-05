import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_43 :
    (List.ofFn coreChunks999_43).flatten =
      (coreData999.take (coreResources999 43).q).drop 209 := by
  decide +kernel

theorem coreCheck999_43 :
    ∀ c : Fin 1, (coreChunks999_43 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 43)) = true := by
  decide +kernel
#print axioms coreFlatten999_43
#print axioms coreCheck999_43
end Erdos883Verified
