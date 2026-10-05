import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_147 :
    (List.ofFn coreChunks999_147).flatten =
      (coreData999.take (coreResources999 147).q).drop 255 := by
  decide +kernel

theorem coreCheck999_147 :
    ∀ c : Fin 1, (coreChunks999_147 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 147)) = true := by
  decide +kernel
#print axioms coreFlatten999_147
#print axioms coreCheck999_147
end Erdos883Verified
