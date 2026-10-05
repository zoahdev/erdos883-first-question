import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_58 :
    (List.ofFn coreChunks999_58).flatten =
      (coreData999.take (coreResources999 58).q).drop 226 := by
  decide +kernel

theorem coreCheck999_58 :
    ∀ c : Fin 1, (coreChunks999_58 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 58)) = true := by
  decide +kernel
#print axioms coreFlatten999_58
#print axioms coreCheck999_58
end Erdos883Verified
