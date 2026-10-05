import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_66 :
    (List.ofFn coreChunks999_66).flatten =
      (coreData999.take (coreResources999 66).q).drop 247 := by
  decide +kernel

theorem coreCheck999_66 :
    ∀ c : Fin 1, (coreChunks999_66 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 66)) = true := by
  decide +kernel
#print axioms coreFlatten999_66
#print axioms coreCheck999_66
end Erdos883Verified
