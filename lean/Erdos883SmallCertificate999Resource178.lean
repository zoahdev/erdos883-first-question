import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_178 :
    (List.ofFn coreChunks999_178).flatten =
      (coreData999.take (coreResources999 178).q).drop 418 := by
  decide +kernel

theorem coreCheck999_178 :
    ∀ c : Fin 1, (coreChunks999_178 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 178)) = true := by
  decide +kernel
#print axioms coreFlatten999_178
#print axioms coreCheck999_178
end Erdos883Verified
