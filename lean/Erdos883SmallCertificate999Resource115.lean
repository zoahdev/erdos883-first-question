import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_115 :
    (List.ofFn coreChunks999_115).flatten =
      (coreData999.take (coreResources999 115).q).drop 198 := by
  decide +kernel

theorem coreCheck999_115 :
    ∀ c : Fin 1, (coreChunks999_115 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 115)) = true := by
  decide +kernel
#print axioms coreFlatten999_115
#print axioms coreCheck999_115
end Erdos883Verified
