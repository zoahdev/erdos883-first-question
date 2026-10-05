import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_48 :
    (List.ofFn coreChunks999_48).flatten =
      (coreData999.take (coreResources999 48).q).drop 215 := by
  decide +kernel

theorem coreCheck999_48 :
    ∀ c : Fin 1, (coreChunks999_48 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 48)) = true := by
  decide +kernel
#print axioms coreFlatten999_48
#print axioms coreCheck999_48
end Erdos883Verified
