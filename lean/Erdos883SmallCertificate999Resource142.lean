import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_142 :
    (List.ofFn coreChunks999_142).flatten =
      (coreData999.take (coreResources999 142).q).drop 248 := by
  decide +kernel

theorem coreCheck999_142 :
    ∀ c : Fin 1, (coreChunks999_142 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 142)) = true := by
  decide +kernel
#print axioms coreFlatten999_142
#print axioms coreCheck999_142
end Erdos883Verified
