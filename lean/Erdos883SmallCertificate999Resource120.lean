import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_120 :
    (List.ofFn coreChunks999_120).flatten =
      (coreData999.take (coreResources999 120).q).drop 204 := by
  decide +kernel

theorem coreCheck999_120 :
    ∀ c : Fin 1, (coreChunks999_120 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 120)) = true := by
  decide +kernel
#print axioms coreFlatten999_120
#print axioms coreCheck999_120
end Erdos883Verified
