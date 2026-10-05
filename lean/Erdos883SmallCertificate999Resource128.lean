import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_128 :
    (List.ofFn coreChunks999_128).flatten =
      (coreData999.take (coreResources999 128).q).drop 218 := by
  decide +kernel

theorem coreCheck999_128 :
    ∀ c : Fin 1, (coreChunks999_128 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 128)) = true := by
  decide +kernel
#print axioms coreFlatten999_128
#print axioms coreCheck999_128
end Erdos883Verified
