import Erdos883SmallCertificate999Data
set_option maxHeartbeats 0
set_option maxRecDepth 1000000
namespace Erdos883Verified

theorem coreFlatten999_174 :
    (List.ofFn coreChunks999_174).flatten =
      (coreData999.take (coreResources999 174).q).drop 405 := by
  decide +kernel

theorem coreCheck999_174 :
    ∀ c : Fin 1, (coreChunks999_174 c).all
      (coreResourceRowCheck 909 coreData999 (coreResources999 174)) = true := by
  decide +kernel
#print axioms coreFlatten999_174
#print axioms coreCheck999_174
end Erdos883Verified
