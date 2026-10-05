import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_189 :
    (List.ofFn coreChunks999_189).flatten =
      (coreData999.take (coreResources999 189).q).drop 322 := by
  decide +kernel

theorem coreCheck999_189 :
    ∀ c : Fin 1, (coreChunks999_189 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 189)) = true := by
  decide +kernel
#print axioms coreFlatten999_189
#print axioms coreCheck999_189
end Erdos883Verified
