import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_177 :
    (List.ofFn coreChunks999_177).flatten =
      (coreData999.take (coreResources999 177).q).drop 412 := by
  decide +kernel

theorem coreCheck999_177 :
    ∀ c : Fin 1, (coreChunks999_177 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 177)) = true := by
  decide +kernel
#print axioms coreFlatten999_177
#print axioms coreCheck999_177
end Erdos883Verified
