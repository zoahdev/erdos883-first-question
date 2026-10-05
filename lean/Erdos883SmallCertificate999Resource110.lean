import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_110 :
    (List.ofFn coreChunks999_110).flatten =
      (coreData999.take (coreResources999 110).q).drop 187 := by
  decide +kernel

theorem coreCheck999_110 :
    ∀ c : Fin 1, (coreChunks999_110 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 110)) = true := by
  decide +kernel
#print axioms coreFlatten999_110
#print axioms coreCheck999_110
end Erdos883Verified
