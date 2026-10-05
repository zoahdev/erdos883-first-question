import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_182 :
    (List.ofFn coreChunks999_182).flatten =
      (coreData999.take (coreResources999 182).q).drop 430 := by
  decide +kernel

theorem coreCheck999_182 :
    ∀ c : Fin 1, (coreChunks999_182 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 182)) = true := by
  decide +kernel
#print axioms coreFlatten999_182
#print axioms coreCheck999_182
end Erdos883Verified
