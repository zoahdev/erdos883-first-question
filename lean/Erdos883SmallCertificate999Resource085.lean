import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_85 :
    (List.ofFn coreChunks999_85).flatten =
      (coreData999.take (coreResources999 85).q).drop 154 := by
  decide +kernel

theorem coreCheck999_85 :
    ∀ c : Fin 1, (coreChunks999_85 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 85)) = true := by
  decide +kernel
#print axioms coreFlatten999_85
#print axioms coreCheck999_85
end Erdos883Verified
