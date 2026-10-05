import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_7 :
    (List.ofFn coreChunks999_7).flatten =
      (coreData999.take (coreResources999 7).q).drop 133 := by
  decide +kernel

theorem coreCheck999_7 :
    ∀ c : Fin 1, (coreChunks999_7 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 7)) = true := by
  decide +kernel
#print axioms coreFlatten999_7
#print axioms coreCheck999_7
end Erdos883Verified
