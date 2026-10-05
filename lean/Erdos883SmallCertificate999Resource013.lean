import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_13 :
    (List.ofFn coreChunks999_13).flatten =
      (coreData999.take (coreResources999 13).q).drop 169 := by
  decide +kernel

theorem coreCheck999_13 :
    ∀ c : Fin 1, (coreChunks999_13 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 13)) = true := by
  decide +kernel
#print axioms coreFlatten999_13
#print axioms coreCheck999_13
end Erdos883Verified
