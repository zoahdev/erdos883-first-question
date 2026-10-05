import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_112 :
    (List.ofFn coreChunks999_112).flatten =
      (coreData999.take (coreResources999 112).q).drop 193 := by
  decide +kernel

theorem coreCheck999_112 :
    ∀ c : Fin 1, (coreChunks999_112 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 112)) = true := by
  decide +kernel
#print axioms coreFlatten999_112
#print axioms coreCheck999_112
end Erdos883Verified
