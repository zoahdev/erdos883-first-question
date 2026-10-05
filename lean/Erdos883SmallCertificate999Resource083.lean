import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_83 :
    (List.ofFn coreChunks999_83).flatten =
      (coreData999.take (coreResources999 83).q).drop 152 := by
  decide +kernel

theorem coreCheck999_83 :
    ∀ c : Fin 1, (coreChunks999_83 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 83)) = true := by
  decide +kernel
#print axioms coreFlatten999_83
#print axioms coreCheck999_83
end Erdos883Verified
