import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_99 :
    (List.ofFn coreChunks999_99).flatten =
      (coreData999.take (coreResources999 99).q).drop 173 := by
  decide +kernel

theorem coreCheck999_99 :
    ∀ c : Fin 1, (coreChunks999_99 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 99)) = true := by
  decide +kernel
#print axioms coreFlatten999_99
#print axioms coreCheck999_99
end Erdos883Verified
