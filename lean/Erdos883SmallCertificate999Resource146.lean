import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_146 :
    (List.ofFn coreChunks999_146).flatten =
      (coreData999.take (coreResources999 146).q).drop 253 := by
  decide +kernel

theorem coreCheck999_146 :
    ∀ c : Fin 1, (coreChunks999_146 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 146)) = true := by
  decide +kernel
#print axioms coreFlatten999_146
#print axioms coreCheck999_146
end Erdos883Verified
