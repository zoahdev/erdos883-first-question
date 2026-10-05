import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_64 :
    (List.ofFn coreChunks999_64).flatten =
      (coreData999.take (coreResources999 64).q).drop 243 := by
  decide +kernel

theorem coreCheck999_64 :
    ∀ c : Fin 1, (coreChunks999_64 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 64)) = true := by
  decide +kernel
#print axioms coreFlatten999_64
#print axioms coreCheck999_64
end Erdos883Verified
