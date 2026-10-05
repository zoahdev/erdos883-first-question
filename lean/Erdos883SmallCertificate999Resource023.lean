import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_23 :
    (List.ofFn coreChunks999_23).flatten =
      (coreData999.take (coreResources999 23).q).drop 181 := by
  decide +kernel

theorem coreCheck999_23 :
    ∀ c : Fin 1, (coreChunks999_23 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 23)) = true := by
  decide +kernel
#print axioms coreFlatten999_23
#print axioms coreCheck999_23
end Erdos883Verified
