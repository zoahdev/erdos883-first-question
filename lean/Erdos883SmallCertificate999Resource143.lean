import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_143 :
    (List.ofFn coreChunks999_143).flatten =
      (coreData999.take (coreResources999 143).q).drop 249 := by
  decide +kernel

theorem coreCheck999_143 :
    ∀ c : Fin 1, (coreChunks999_143 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 143)) = true := by
  decide +kernel
#print axioms coreFlatten999_143
#print axioms coreCheck999_143
end Erdos883Verified
