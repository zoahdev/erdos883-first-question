import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_140 :
    (List.ofFn coreChunks999_140).flatten =
      (coreData999.take (coreResources999 140).q).drop 240 := by
  decide +kernel

theorem coreCheck999_140 :
    ∀ c : Fin 1, (coreChunks999_140 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 140)) = true := by
  decide +kernel
#print axioms coreFlatten999_140
#print axioms coreCheck999_140
end Erdos883Verified
