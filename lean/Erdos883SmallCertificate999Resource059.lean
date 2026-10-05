import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_59 :
    (List.ofFn coreChunks999_59).flatten =
      (coreData999.take (coreResources999 59).q).drop 229 := by
  decide +kernel

theorem coreCheck999_59 :
    ∀ c : Fin 1, (coreChunks999_59 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 59)) = true := by
  decide +kernel
#print axioms coreFlatten999_59
#print axioms coreCheck999_59
end Erdos883Verified
