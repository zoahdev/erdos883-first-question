import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_184 :
    (List.ofFn coreChunks999_184).flatten =
      (coreData999.take (coreResources999 184).q).drop 440 := by
  decide +kernel

theorem coreCheck999_184 :
    ∀ c : Fin 1, (coreChunks999_184 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 184)) = true := by
  decide +kernel
#print axioms coreFlatten999_184
#print axioms coreCheck999_184
end Erdos883Verified
