import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_157 :
    (List.ofFn coreChunks999_157).flatten =
      (coreData999.take (coreResources999 157).q).drop 297 := by
  decide +kernel

theorem coreCheck999_157 :
    ∀ c : Fin 1, (coreChunks999_157 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 157)) = true := by
  decide +kernel
#print axioms coreFlatten999_157
#print axioms coreCheck999_157
end Erdos883Verified
