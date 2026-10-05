import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_156 :
    (List.ofFn coreChunks999_156).flatten =
      (coreData999.take (coreResources999 156).q).drop 292 := by
  decide +kernel

theorem coreCheck999_156 :
    ∀ c : Fin 1, (coreChunks999_156 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 156)) = true := by
  decide +kernel
#print axioms coreFlatten999_156
#print axioms coreCheck999_156
end Erdos883Verified
