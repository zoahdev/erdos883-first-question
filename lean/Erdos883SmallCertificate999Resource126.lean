import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_126 :
    (List.ofFn coreChunks999_126).flatten =
      (coreData999.take (coreResources999 126).q).drop 215 := by
  decide +kernel

theorem coreCheck999_126 :
    ∀ c : Fin 1, (coreChunks999_126 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 126)) = true := by
  decide +kernel
#print axioms coreFlatten999_126
#print axioms coreCheck999_126
end Erdos883Verified
