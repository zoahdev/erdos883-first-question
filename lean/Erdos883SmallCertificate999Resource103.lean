import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_103 :
    (List.ofFn coreChunks999_103).flatten =
      (coreData999.take (coreResources999 103).q).drop 180 := by
  decide +kernel

theorem coreCheck999_103 :
    ∀ c : Fin 1, (coreChunks999_103 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 103)) = true := by
  decide +kernel
#print axioms coreFlatten999_103
#print axioms coreCheck999_103
end Erdos883Verified
