import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_90 :
    (List.ofFn coreChunks999_90).flatten =
      (coreData999.take (coreResources999 90).q).drop 160 := by
  decide +kernel

theorem coreCheck999_90 :
    ∀ c : Fin 1, (coreChunks999_90 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 90)) = true := by
  decide +kernel
#print axioms coreFlatten999_90
#print axioms coreCheck999_90
end Erdos883Verified
