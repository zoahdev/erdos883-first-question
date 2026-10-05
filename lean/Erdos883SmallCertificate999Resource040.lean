import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_40 :
    (List.ofFn coreChunks999_40).flatten =
      (coreData999.take (coreResources999 40).q).drop 202 := by
  decide +kernel

theorem coreCheck999_40 :
    ∀ c : Fin 1, (coreChunks999_40 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 40)) = true := by
  decide +kernel
#print axioms coreFlatten999_40
#print axioms coreCheck999_40
end Erdos883Verified
