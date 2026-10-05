import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_8 :
    (List.ofFn coreChunks999_8).flatten =
      (coreData999.take (coreResources999 8).q).drop 134 := by
  decide +kernel

theorem coreCheck999_8 :
    ∀ c : Fin 1, (coreChunks999_8 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 8)) = true := by
  decide +kernel
#print axioms coreFlatten999_8
#print axioms coreCheck999_8
end Erdos883Verified
