import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_68 :
    (List.ofFn coreChunks999_68).flatten =
      (coreData999.take (coreResources999 68).q).drop 249 := by
  decide +kernel

theorem coreCheck999_68 :
    ∀ c : Fin 1, (coreChunks999_68 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 68)) = true := by
  decide +kernel
#print axioms coreFlatten999_68
#print axioms coreCheck999_68
end Erdos883Verified
