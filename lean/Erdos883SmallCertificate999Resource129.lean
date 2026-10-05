import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_129 :
    (List.ofFn coreChunks999_129).flatten =
      (coreData999.take (coreResources999 129).q).drop 219 := by
  decide +kernel

theorem coreCheck999_129 :
    ∀ c : Fin 1, (coreChunks999_129 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 129)) = true := by
  decide +kernel
#print axioms coreFlatten999_129
#print axioms coreCheck999_129
end Erdos883Verified
