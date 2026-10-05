import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_31 :
    (List.ofFn coreChunks999_31).flatten =
      (coreData999.take (coreResources999 31).q).drop 191 := by
  decide +kernel

theorem coreCheck999_31 :
    ∀ c : Fin 1, (coreChunks999_31 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 31)) = true := by
  decide +kernel
#print axioms coreFlatten999_31
#print axioms coreCheck999_31
end Erdos883Verified
