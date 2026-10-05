import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_136 :
    (List.ofFn coreChunks999_136).flatten =
      (coreData999.take (coreResources999 136).q).drop 226 := by
  decide +kernel

theorem coreCheck999_136 :
    ∀ c : Fin 1, (coreChunks999_136 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 136)) = true := by
  decide +kernel
#print axioms coreFlatten999_136
#print axioms coreCheck999_136
end Erdos883Verified
