import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_170 :
    (List.ofFn coreChunks999_170).flatten =
      (coreData999.take (coreResources999 170).q).drop 352 := by
  decide +kernel

theorem coreCheck999_170 :
    ∀ c : Fin 2, (coreChunks999_170 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 170)) = true := by
  decide +kernel
#print axioms coreFlatten999_170
#print axioms coreCheck999_170
end Erdos883Verified
