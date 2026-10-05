import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_46 :
    (List.ofFn coreChunks999_46).flatten =
      (coreData999.take (coreResources999 46).q).drop 212 := by
  decide +kernel

theorem coreCheck999_46 :
    ∀ c : Fin 1, (coreChunks999_46 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 46)) = true := by
  decide +kernel
#print axioms coreFlatten999_46
#print axioms coreCheck999_46
end Erdos883Verified
