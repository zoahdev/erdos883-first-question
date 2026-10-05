import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_25 :
    (List.ofFn coreChunks999_25).flatten =
      (coreData999.take (coreResources999 25).q).drop 183 := by
  decide +kernel

theorem coreCheck999_25 :
    ∀ c : Fin 1, (coreChunks999_25 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 25)) = true := by
  decide +kernel
#print axioms coreFlatten999_25
#print axioms coreCheck999_25
end Erdos883Verified
