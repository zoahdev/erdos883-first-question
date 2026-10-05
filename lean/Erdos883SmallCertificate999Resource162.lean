import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_162 :
    (List.ofFn coreChunks999_162).flatten =
      (coreData999.take (coreResources999 162).q).drop 306 := by
  decide +kernel

theorem coreCheck999_162 :
    ∀ c : Fin 1, (coreChunks999_162 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 162)) = true := by
  decide +kernel
#print axioms coreFlatten999_162
#print axioms coreCheck999_162
end Erdos883Verified
