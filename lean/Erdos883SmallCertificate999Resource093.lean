import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_93 :
    (List.ofFn coreChunks999_93).flatten =
      (coreData999.take (coreResources999 93).q).drop 166 := by
  decide +kernel

theorem coreCheck999_93 :
    ∀ c : Fin 1, (coreChunks999_93 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 93)) = true := by
  decide +kernel
#print axioms coreFlatten999_93
#print axioms coreCheck999_93
end Erdos883Verified
