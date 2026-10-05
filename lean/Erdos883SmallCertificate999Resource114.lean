import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_114 :
    (List.ofFn coreChunks999_114).flatten =
      (coreData999.take (coreResources999 114).q).drop 197 := by
  decide +kernel

theorem coreCheck999_114 :
    ∀ c : Fin 1, (coreChunks999_114 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 114)) = true := by
  decide +kernel
#print axioms coreFlatten999_114
#print axioms coreCheck999_114
end Erdos883Verified
