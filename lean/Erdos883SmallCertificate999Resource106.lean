import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_106 :
    (List.ofFn coreChunks999_106).flatten =
      (coreData999.take (coreResources999 106).q).drop 183 := by
  decide +kernel

theorem coreCheck999_106 :
    ∀ c : Fin 1, (coreChunks999_106 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 106)) = true := by
  decide +kernel
#print axioms coreFlatten999_106
#print axioms coreCheck999_106
end Erdos883Verified
