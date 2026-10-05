import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_172 :
    (List.ofFn coreChunks999_172).flatten =
      (coreData999.take (coreResources999 172).q).drop 394 := by
  decide +kernel

theorem coreCheck999_172 :
    ∀ c : Fin 1, (coreChunks999_172 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 172)) = true := by
  decide +kernel
#print axioms coreFlatten999_172
#print axioms coreCheck999_172
end Erdos883Verified
