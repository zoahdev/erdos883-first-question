import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_27 :
    (List.ofFn coreChunks999_27).flatten =
      (coreData999.take (coreResources999 27).q).drop 185 := by
  decide +kernel

theorem coreCheck999_27 :
    ∀ c : Fin 1, (coreChunks999_27 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 27)) = true := by
  decide +kernel
#print axioms coreFlatten999_27
#print axioms coreCheck999_27
end Erdos883Verified
