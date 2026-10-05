import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_152 :
    (List.ofFn coreChunks999_152).flatten =
      (coreData999.take (coreResources999 152).q).drop 265 := by
  decide +kernel

theorem coreCheck999_152 :
    ∀ c : Fin 1, (coreChunks999_152 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 152)) = true := by
  decide +kernel
#print axioms coreFlatten999_152
#print axioms coreCheck999_152
end Erdos883Verified
