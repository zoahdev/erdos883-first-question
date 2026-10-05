import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_62 :
    (List.ofFn coreChunks999_62).flatten =
      (coreData999.take (coreResources999 62).q).drop 238 := by
  decide +kernel

theorem coreCheck999_62 :
    ∀ c : Fin 1, (coreChunks999_62 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 62)) = true := by
  decide +kernel
#print axioms coreFlatten999_62
#print axioms coreCheck999_62
end Erdos883Verified
