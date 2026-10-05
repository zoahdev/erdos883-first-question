import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_73 :
    (List.ofFn coreChunks999_73).flatten =
      (coreData999.take (coreResources999 73).q).drop 121 := by
  decide +kernel

theorem coreCheck999_73 :
    ∀ c : Fin 1, (coreChunks999_73 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 73)) = true := by
  decide +kernel
#print axioms coreFlatten999_73
#print axioms coreCheck999_73
end Erdos883Verified
