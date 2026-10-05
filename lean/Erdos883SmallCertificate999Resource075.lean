import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_75 :
    (List.ofFn coreChunks999_75).flatten =
      (coreData999.take (coreResources999 75).q).drop 134 := by
  decide +kernel

theorem coreCheck999_75 :
    ∀ c : Fin 1, (coreChunks999_75 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 75)) = true := by
  decide +kernel
#print axioms coreFlatten999_75
#print axioms coreCheck999_75
end Erdos883Verified
