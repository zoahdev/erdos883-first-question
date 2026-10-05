import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_86 :
    (List.ofFn coreChunks999_86).flatten =
      (coreData999.take (coreResources999 86).q).drop 155 := by
  decide +kernel

theorem coreCheck999_86 :
    ∀ c : Fin 1, (coreChunks999_86 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 86)) = true := by
  decide +kernel
#print axioms coreFlatten999_86
#print axioms coreCheck999_86
end Erdos883Verified
