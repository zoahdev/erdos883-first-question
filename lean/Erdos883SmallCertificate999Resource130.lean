import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_130 :
    (List.ofFn coreChunks999_130).flatten =
      (coreData999.take (coreResources999 130).q).drop 220 := by
  decide +kernel

theorem coreCheck999_130 :
    ∀ c : Fin 1, (coreChunks999_130 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 130)) = true := by
  decide +kernel
#print axioms coreFlatten999_130
#print axioms coreCheck999_130
end Erdos883Verified
