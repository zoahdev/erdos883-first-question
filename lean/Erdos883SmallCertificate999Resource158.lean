import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_158 :
    (List.ofFn coreChunks999_158).flatten =
      (coreData999.take (coreResources999 158).q).drop 298 := by
  decide +kernel

theorem coreCheck999_158 :
    ∀ c : Fin 1, (coreChunks999_158 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 158)) = true := by
  decide +kernel
#print axioms coreFlatten999_158
#print axioms coreCheck999_158
end Erdos883Verified
