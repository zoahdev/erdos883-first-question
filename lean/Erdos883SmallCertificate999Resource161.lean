import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_161 :
    (List.ofFn coreChunks999_161).flatten =
      (coreData999.take (coreResources999 161).q).drop 304 := by
  decide +kernel

theorem coreCheck999_161 :
    ∀ c : Fin 1, (coreChunks999_161 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 161)) = true := by
  decide +kernel
#print axioms coreFlatten999_161
#print axioms coreCheck999_161
end Erdos883Verified
