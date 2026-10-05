import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_180 :
    (List.ofFn coreChunks999_180).flatten =
      (coreData999.take (coreResources999 180).q).drop 422 := by
  decide +kernel

theorem coreCheck999_180 :
    ∀ c : Fin 1, (coreChunks999_180 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 180)) = true := by
  decide +kernel
#print axioms coreFlatten999_180
#print axioms coreCheck999_180
end Erdos883Verified
