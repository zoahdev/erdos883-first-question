import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_133 :
    (List.ofFn coreChunks999_133).flatten =
      (coreData999.take (coreResources999 133).q).drop 223 := by
  decide +kernel

theorem coreCheck999_133 :
    ∀ c : Fin 1, (coreChunks999_133 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 133)) = true := by
  decide +kernel
#print axioms coreFlatten999_133
#print axioms coreCheck999_133
end Erdos883Verified
