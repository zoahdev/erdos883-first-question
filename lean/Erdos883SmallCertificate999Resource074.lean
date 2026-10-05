import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_74 :
    (List.ofFn coreChunks999_74).flatten =
      (coreData999.take (coreResources999 74).q).drop 133 := by
  decide +kernel

theorem coreCheck999_74 :
    ∀ c : Fin 1, (coreChunks999_74 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 74)) = true := by
  decide +kernel
#print axioms coreFlatten999_74
#print axioms coreCheck999_74
end Erdos883Verified
