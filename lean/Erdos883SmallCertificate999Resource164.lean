import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_164 :
    (List.ofFn coreChunks999_164).flatten =
      (coreData999.take (coreResources999 164).q).drop 312 := by
  decide +kernel

theorem coreCheck999_164 :
    ∀ c : Fin 1, (coreChunks999_164 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 164)) = true := by
  decide +kernel
#print axioms coreFlatten999_164
#print axioms coreCheck999_164
end Erdos883Verified
