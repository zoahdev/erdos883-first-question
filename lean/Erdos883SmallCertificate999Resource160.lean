import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_160 :
    (List.ofFn coreChunks999_160).flatten =
      (coreData999.take (coreResources999 160).q).drop 301 := by
  decide +kernel

theorem coreCheck999_160 :
    ∀ c : Fin 1, (coreChunks999_160 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 160)) = true := by
  decide +kernel
#print axioms coreFlatten999_160
#print axioms coreCheck999_160
end Erdos883Verified
