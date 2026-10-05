import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_52 :
    (List.ofFn coreChunks999_52).flatten =
      (coreData999.take (coreResources999 52).q).drop 220 := by
  decide +kernel

theorem coreCheck999_52 :
    ∀ c : Fin 1, (coreChunks999_52 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 52)) = true := by
  decide +kernel
#print axioms coreFlatten999_52
#print axioms coreCheck999_52
end Erdos883Verified
