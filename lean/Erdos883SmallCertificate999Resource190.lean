import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_190 :
    (List.ofFn coreChunks999_190).flatten =
      (coreData999.take (coreResources999 190).q).drop 323 := by
  decide +kernel

theorem coreCheck999_190 :
    ∀ c : Fin 1, (coreChunks999_190 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 190)) = true := by
  decide +kernel
#print axioms coreFlatten999_190
#print axioms coreCheck999_190
end Erdos883Verified
