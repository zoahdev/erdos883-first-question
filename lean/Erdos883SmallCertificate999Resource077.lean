import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_77 :
    (List.ofFn coreChunks999_77).flatten =
      (coreData999.take (coreResources999 77).q).drop 140 := by
  decide +kernel

theorem coreCheck999_77 :
    ∀ c : Fin 1, (coreChunks999_77 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 77)) = true := by
  decide +kernel
#print axioms coreFlatten999_77
#print axioms coreCheck999_77
end Erdos883Verified
