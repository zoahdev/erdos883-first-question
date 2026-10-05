import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_30 :
    (List.ofFn coreChunks999_30).flatten =
      (coreData999.take (coreResources999 30).q).drop 188 := by
  decide +kernel

theorem coreCheck999_30 :
    ∀ c : Fin 1, (coreChunks999_30 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 30)) = true := by
  decide +kernel
#print axioms coreFlatten999_30
#print axioms coreCheck999_30
end Erdos883Verified
