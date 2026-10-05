import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_125 :
    (List.ofFn coreChunks999_125).flatten =
      (coreData999.take (coreResources999 125).q).drop 213 := by
  decide +kernel

theorem coreCheck999_125 :
    ∀ c : Fin 1, (coreChunks999_125 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 125)) = true := by
  decide +kernel
#print axioms coreFlatten999_125
#print axioms coreCheck999_125
end Erdos883Verified
