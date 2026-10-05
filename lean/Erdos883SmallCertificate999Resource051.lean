import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_51 :
    (List.ofFn coreChunks999_51).flatten =
      (coreData999.take (coreResources999 51).q).drop 219 := by
  decide +kernel

theorem coreCheck999_51 :
    ∀ c : Fin 1, (coreChunks999_51 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 51)) = true := by
  decide +kernel
#print axioms coreFlatten999_51
#print axioms coreCheck999_51
end Erdos883Verified
