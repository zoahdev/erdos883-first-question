import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_38 :
    (List.ofFn coreChunks999_38).flatten =
      (coreData999.take (coreResources999 38).q).drop 200 := by
  decide +kernel

theorem coreCheck999_38 :
    ∀ c : Fin 1, (coreChunks999_38 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 38)) = true := by
  decide +kernel
#print axioms coreFlatten999_38
#print axioms coreCheck999_38
end Erdos883Verified
