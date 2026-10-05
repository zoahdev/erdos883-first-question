import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_16 :
    (List.ofFn coreChunks999_16).flatten =
      (coreData999.take (coreResources999 16).q).drop 172 := by
  decide +kernel

theorem coreCheck999_16 :
    ∀ c : Fin 1, (coreChunks999_16 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 16)) = true := by
  decide +kernel
#print axioms coreFlatten999_16
#print axioms coreCheck999_16
end Erdos883Verified
