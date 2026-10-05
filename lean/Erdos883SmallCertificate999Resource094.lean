import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_94 :
    (List.ofFn coreChunks999_94).flatten =
      (coreData999.take (coreResources999 94).q).drop 168 := by
  decide +kernel

theorem coreCheck999_94 :
    ∀ c : Fin 1, (coreChunks999_94 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 94)) = true := by
  decide +kernel
#print axioms coreFlatten999_94
#print axioms coreCheck999_94
end Erdos883Verified
