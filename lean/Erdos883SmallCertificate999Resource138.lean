import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_138 :
    (List.ofFn coreChunks999_138).flatten =
      (coreData999.take (coreResources999 138).q).drop 230 := by
  decide +kernel

theorem coreCheck999_138 :
    ∀ c : Fin 1, (coreChunks999_138 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 138)) = true := by
  decide +kernel
#print axioms coreFlatten999_138
#print axioms coreCheck999_138
end Erdos883Verified
