import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_176 :
    (List.ofFn coreChunks999_176).flatten =
      (coreData999.take (coreResources999 176).q).drop 411 := by
  decide +kernel

theorem coreCheck999_176 :
    ∀ c : Fin 1, (coreChunks999_176 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 176)) = true := by
  decide +kernel
#print axioms coreFlatten999_176
#print axioms coreCheck999_176
end Erdos883Verified
