import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_109 :
    (List.ofFn coreChunks999_109).flatten =
      (coreData999.take (coreResources999 109).q).drop 186 := by
  decide +kernel

theorem coreCheck999_109 :
    ∀ c : Fin 1, (coreChunks999_109 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 109)) = true := by
  decide +kernel
#print axioms coreFlatten999_109
#print axioms coreCheck999_109
end Erdos883Verified
