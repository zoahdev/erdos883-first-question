import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_163 :
    (List.ofFn coreChunks999_163).flatten =
      (coreData999.take (coreResources999 163).q).drop 310 := by
  decide +kernel

theorem coreCheck999_163 :
    ∀ c : Fin 1, (coreChunks999_163 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 163)) = true := by
  decide +kernel
#print axioms coreFlatten999_163
#print axioms coreCheck999_163
end Erdos883Verified
