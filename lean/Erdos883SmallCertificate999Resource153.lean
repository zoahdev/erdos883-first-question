import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_153 :
    (List.ofFn coreChunks999_153).flatten =
      (coreData999.take (coreResources999 153).q).drop 275 := by
  decide +kernel

theorem coreCheck999_153 :
    ∀ c : Fin 1, (coreChunks999_153 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 153)) = true := by
  decide +kernel
#print axioms coreFlatten999_153
#print axioms coreCheck999_153
end Erdos883Verified
