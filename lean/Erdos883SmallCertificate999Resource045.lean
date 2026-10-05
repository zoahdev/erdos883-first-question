import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_45 :
    (List.ofFn coreChunks999_45).flatten =
      (coreData999.take (coreResources999 45).q).drop 211 := by
  decide +kernel

theorem coreCheck999_45 :
    ∀ c : Fin 1, (coreChunks999_45 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 45)) = true := by
  decide +kernel
#print axioms coreFlatten999_45
#print axioms coreCheck999_45
end Erdos883Verified
