import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_139 :
    (List.ofFn coreChunks999_139).flatten =
      (coreData999.take (coreResources999 139).q).drop 234 := by
  decide +kernel

theorem coreCheck999_139 :
    ∀ c : Fin 1, (coreChunks999_139 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 139)) = true := by
  decide +kernel
#print axioms coreFlatten999_139
#print axioms coreCheck999_139
end Erdos883Verified
