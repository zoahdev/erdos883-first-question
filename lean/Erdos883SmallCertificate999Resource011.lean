import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_11 :
    (List.ofFn coreChunks999_11).flatten =
      (coreData999.take (coreResources999 11).q).drop 166 := by
  decide +kernel

theorem coreCheck999_11 :
    ∀ c : Fin 1, (coreChunks999_11 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 11)) = true := by
  decide +kernel
#print axioms coreFlatten999_11
#print axioms coreCheck999_11
end Erdos883Verified
