import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_92 :
    (List.ofFn coreChunks999_92).flatten =
      (coreData999.take (coreResources999 92).q).drop 164 := by
  decide +kernel

theorem coreCheck999_92 :
    ∀ c : Fin 1, (coreChunks999_92 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 92)) = true := by
  decide +kernel
#print axioms coreFlatten999_92
#print axioms coreCheck999_92
end Erdos883Verified
