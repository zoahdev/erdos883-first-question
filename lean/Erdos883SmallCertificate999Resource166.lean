import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_166 :
    (List.ofFn coreChunks999_166).flatten =
      (coreData999.take (coreResources999 166).q).drop 316 := by
  decide +kernel

theorem coreCheck999_166 :
    ∀ c : Fin 1, (coreChunks999_166 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 166)) = true := by
  decide +kernel
#print axioms coreFlatten999_166
#print axioms coreCheck999_166
end Erdos883Verified
