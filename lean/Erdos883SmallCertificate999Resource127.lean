import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_127 :
    (List.ofFn coreChunks999_127).flatten =
      (coreData999.take (coreResources999 127).q).drop 216 := by
  decide +kernel

theorem coreCheck999_127 :
    ∀ c : Fin 1, (coreChunks999_127 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 127)) = true := by
  decide +kernel
#print axioms coreFlatten999_127
#print axioms coreCheck999_127
end Erdos883Verified
