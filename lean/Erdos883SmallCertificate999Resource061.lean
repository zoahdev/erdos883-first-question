import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_61 :
    (List.ofFn coreChunks999_61).flatten =
      (coreData999.take (coreResources999 61).q).drop 234 := by
  decide +kernel

theorem coreCheck999_61 :
    ∀ c : Fin 1, (coreChunks999_61 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 61)) = true := by
  decide +kernel
#print axioms coreFlatten999_61
#print axioms coreCheck999_61
end Erdos883Verified
