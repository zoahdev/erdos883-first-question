import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_10 :
    (List.ofFn coreChunks999_10).flatten =
      (coreData999.take (coreResources999 10).q).drop 163 := by
  decide +kernel

theorem coreCheck999_10 :
    ∀ c : Fin 1, (coreChunks999_10 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 10)) = true := by
  decide +kernel
#print axioms coreFlatten999_10
#print axioms coreCheck999_10
end Erdos883Verified
