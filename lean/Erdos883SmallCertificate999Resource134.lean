import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_134 :
    (List.ofFn coreChunks999_134).flatten =
      (coreData999.take (coreResources999 134).q).drop 224 := by
  decide +kernel

theorem coreCheck999_134 :
    ∀ c : Fin 1, (coreChunks999_134 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 134)) = true := by
  decide +kernel
#print axioms coreFlatten999_134
#print axioms coreCheck999_134
end Erdos883Verified
