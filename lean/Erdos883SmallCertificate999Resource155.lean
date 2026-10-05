import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_155 :
    (List.ofFn coreChunks999_155).flatten =
      (coreData999.take (coreResources999 155).q).drop 287 := by
  decide +kernel

theorem coreCheck999_155 :
    ∀ c : Fin 1, (coreChunks999_155 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 155)) = true := by
  decide +kernel
#print axioms coreFlatten999_155
#print axioms coreCheck999_155
end Erdos883Verified
