import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_171 :
    (List.ofFn coreChunks999_171).flatten =
      (coreData999.take (coreResources999 171).q).drop 371 := by
  decide +kernel

theorem coreCheck999_171 :
    ∀ c : Fin 2, (coreChunks999_171 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 171)) = true := by
  decide +kernel
#print axioms coreFlatten999_171
#print axioms coreCheck999_171
end Erdos883Verified
