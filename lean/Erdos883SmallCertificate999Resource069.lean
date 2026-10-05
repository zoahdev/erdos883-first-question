import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_69 :
    (List.ofFn coreChunks999_69).flatten =
      (coreData999.take (coreResources999 69).q).drop 250 := by
  decide +kernel

theorem coreCheck999_69 :
    ∀ c : Fin 1, (coreChunks999_69 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 69)) = true := by
  decide +kernel
#print axioms coreFlatten999_69
#print axioms coreCheck999_69
end Erdos883Verified
