import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_32 :
    (List.ofFn coreChunks999_32).flatten =
      (coreData999.take (coreResources999 32).q).drop 193 := by
  decide +kernel

theorem coreCheck999_32 :
    ∀ c : Fin 1, (coreChunks999_32 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 32)) = true := by
  decide +kernel
#print axioms coreFlatten999_32
#print axioms coreCheck999_32
end Erdos883Verified
