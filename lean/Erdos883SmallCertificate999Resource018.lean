import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_18 :
    (List.ofFn coreChunks999_18).flatten =
      (coreData999.take (coreResources999 18).q).drop 174 := by
  decide +kernel

theorem coreCheck999_18 :
    ∀ c : Fin 1, (coreChunks999_18 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 18)) = true := by
  decide +kernel
#print axioms coreFlatten999_18
#print axioms coreCheck999_18
end Erdos883Verified
