import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_124 :
    (List.ofFn coreChunks999_124).flatten =
      (coreData999.take (coreResources999 124).q).drop 212 := by
  decide +kernel

theorem coreCheck999_124 :
    ∀ c : Fin 1, (coreChunks999_124 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 124)) = true := by
  decide +kernel
#print axioms coreFlatten999_124
#print axioms coreCheck999_124
end Erdos883Verified
