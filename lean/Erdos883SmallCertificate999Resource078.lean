import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_78 :
    (List.ofFn coreChunks999_78).flatten =
      (coreData999.take (coreResources999 78).q).drop 145 := by
  decide +kernel

theorem coreCheck999_78 :
    ∀ c : Fin 1, (coreChunks999_78 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 78)) = true := by
  decide +kernel
#print axioms coreFlatten999_78
#print axioms coreCheck999_78
end Erdos883Verified
