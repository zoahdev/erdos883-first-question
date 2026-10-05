import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_60 :
    (List.ofFn coreChunks999_60).flatten =
      (coreData999.take (coreResources999 60).q).drop 230 := by
  decide +kernel

theorem coreCheck999_60 :
    ∀ c : Fin 1, (coreChunks999_60 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 60)) = true := by
  decide +kernel
#print axioms coreFlatten999_60
#print axioms coreCheck999_60
end Erdos883Verified
