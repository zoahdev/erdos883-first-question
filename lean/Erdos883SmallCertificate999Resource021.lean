import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_21 :
    (List.ofFn coreChunks999_21).flatten =
      (coreData999.take (coreResources999 21).q).drop 177 := by
  decide +kernel

theorem coreCheck999_21 :
    ∀ c : Fin 1, (coreChunks999_21 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 21)) = true := by
  decide +kernel
#print axioms coreFlatten999_21
#print axioms coreCheck999_21
end Erdos883Verified
