import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_102 :
    (List.ofFn coreChunks999_102).flatten =
      (coreData999.take (coreResources999 102).q).drop 176 := by
  decide +kernel

theorem coreCheck999_102 :
    ∀ c : Fin 1, (coreChunks999_102 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 102)) = true := by
  decide +kernel
#print axioms coreFlatten999_102
#print axioms coreCheck999_102
end Erdos883Verified
