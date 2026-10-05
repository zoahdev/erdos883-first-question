import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_87 :
    (List.ofFn coreChunks999_87).flatten =
      (coreData999.take (coreResources999 87).q).drop 156 := by
  decide +kernel

theorem coreCheck999_87 :
    ∀ c : Fin 1, (coreChunks999_87 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 87)) = true := by
  decide +kernel
#print axioms coreFlatten999_87
#print axioms coreCheck999_87
end Erdos883Verified
