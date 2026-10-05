import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_50 :
    (List.ofFn coreChunks999_50).flatten =
      (coreData999.take (coreResources999 50).q).drop 218 := by
  decide +kernel

theorem coreCheck999_50 :
    ∀ c : Fin 1, (coreChunks999_50 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 50)) = true := by
  decide +kernel
#print axioms coreFlatten999_50
#print axioms coreCheck999_50
end Erdos883Verified
