import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_97 :
    (List.ofFn coreChunks999_97).flatten =
      (coreData999.take (coreResources999 97).q).drop 171 := by
  decide +kernel

theorem coreCheck999_97 :
    ∀ c : Fin 1, (coreChunks999_97 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 97)) = true := by
  decide +kernel
#print axioms coreFlatten999_97
#print axioms coreCheck999_97
end Erdos883Verified
