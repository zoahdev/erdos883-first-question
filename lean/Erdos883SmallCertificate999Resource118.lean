import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_118 :
    (List.ofFn coreChunks999_118).flatten =
      (coreData999.take (coreResources999 118).q).drop 201 := by
  decide +kernel

theorem coreCheck999_118 :
    ∀ c : Fin 1, (coreChunks999_118 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 118)) = true := by
  decide +kernel
#print axioms coreFlatten999_118
#print axioms coreCheck999_118
end Erdos883Verified
