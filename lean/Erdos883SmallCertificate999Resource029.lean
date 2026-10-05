import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_29 :
    (List.ofFn coreChunks999_29).flatten =
      (coreData999.take (coreResources999 29).q).drop 187 := by
  decide +kernel

theorem coreCheck999_29 :
    ∀ c : Fin 1, (coreChunks999_29 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 29)) = true := by
  decide +kernel
#print axioms coreFlatten999_29
#print axioms coreCheck999_29
end Erdos883Verified
