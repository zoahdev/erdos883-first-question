import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_81 :
    (List.ofFn coreChunks999_81).flatten =
      (coreData999.take (coreResources999 81).q).drop 149 := by
  decide +kernel

theorem coreCheck999_81 :
    ∀ c : Fin 1, (coreChunks999_81 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 81)) = true := by
  decide +kernel
#print axioms coreFlatten999_81
#print axioms coreCheck999_81
end Erdos883Verified
