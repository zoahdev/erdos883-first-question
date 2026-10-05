import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_98 :
    (List.ofFn coreChunks999_98).flatten =
      (coreData999.take (coreResources999 98).q).drop 172 := by
  decide +kernel

theorem coreCheck999_98 :
    ∀ c : Fin 1, (coreChunks999_98 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 98)) = true := by
  decide +kernel
#print axioms coreFlatten999_98
#print axioms coreCheck999_98
end Erdos883Verified
