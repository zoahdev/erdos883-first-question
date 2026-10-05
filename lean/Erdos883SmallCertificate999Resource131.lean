import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_131 :
    (List.ofFn coreChunks999_131).flatten =
      (coreData999.take (coreResources999 131).q).drop 221 := by
  decide +kernel

theorem coreCheck999_131 :
    ∀ c : Fin 1, (coreChunks999_131 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 131)) = true := by
  decide +kernel
#print axioms coreFlatten999_131
#print axioms coreCheck999_131
end Erdos883Verified
