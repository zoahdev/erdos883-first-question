import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_15 :
    (List.ofFn coreChunks999_15).flatten =
      (coreData999.take (coreResources999 15).q).drop 171 := by
  decide +kernel

theorem coreCheck999_15 :
    ∀ c : Fin 1, (coreChunks999_15 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 15)) = true := by
  decide +kernel
#print axioms coreFlatten999_15
#print axioms coreCheck999_15
end Erdos883Verified
