import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_96 :
    (List.ofFn coreChunks999_96).flatten =
      (coreData999.take (coreResources999 96).q).drop 170 := by
  decide +kernel

theorem coreCheck999_96 :
    ∀ c : Fin 1, (coreChunks999_96 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 96)) = true := by
  decide +kernel
#print axioms coreFlatten999_96
#print axioms coreCheck999_96
end Erdos883Verified
