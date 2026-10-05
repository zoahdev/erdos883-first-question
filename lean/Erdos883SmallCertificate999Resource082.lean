import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_82 :
    (List.ofFn coreChunks999_82).flatten =
      (coreData999.take (coreResources999 82).q).drop 151 := by
  decide +kernel

theorem coreCheck999_82 :
    ∀ c : Fin 1, (coreChunks999_82 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 82)) = true := by
  decide +kernel
#print axioms coreFlatten999_82
#print axioms coreCheck999_82
end Erdos883Verified
