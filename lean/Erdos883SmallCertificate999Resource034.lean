import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_34 :
    (List.ofFn coreChunks999_34).flatten =
      (coreData999.take (coreResources999 34).q).drop 196 := by
  decide +kernel

theorem coreCheck999_34 :
    ∀ c : Fin 1, (coreChunks999_34 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 34)) = true := by
  decide +kernel
#print axioms coreFlatten999_34
#print axioms coreCheck999_34
end Erdos883Verified
