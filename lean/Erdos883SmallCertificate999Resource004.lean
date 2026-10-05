import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_4 :
    (List.ofFn coreChunks999_4).flatten =
      (coreData999.take (coreResources999 4).q).drop 121 := by
  decide +kernel

theorem coreCheck999_4 :
    ∀ c : Fin 1, (coreChunks999_4 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 4)) = true := by
  decide +kernel
#print axioms coreFlatten999_4
#print axioms coreCheck999_4
end Erdos883Verified
